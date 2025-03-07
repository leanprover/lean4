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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_setFunIndInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5;
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22;
static lean_object* l_Lean_Meta_getFunCasesName___closed__2;
static lean_object* l_Lean_Meta_getFunInductName___closed__2;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__5;
static lean_object* l_Lean_Meta_instInhabitedFunIndInfo___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind;
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16;
static lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFunIndInfo;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20;
static lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__7;
static lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1;
static lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_funIndInfoExt;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMutualInductName___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__10;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__9;
static lean_object* l_Lean_Meta_getMutualInductName___closed__1;
static lean_object* l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3;
static lean_object* l_Lean_Meta_getFunCasesName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__2;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12;
static lean_object* l_Lean_Meta_instReprFunIndInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7;
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqFunIndParamKind___closed__1;
static lean_object* l_Lean_Meta_getFunInductName___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27;
static lean_object* l_Lean_Meta_instReprFunIndParamKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedFunIndInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setFunIndInfo___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind;
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
static lean_object* _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_1, x_2);
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
x_13 = l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__4(x_2, x_12, x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unbox(x_11);
lean_dec(x_11);
x_15 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_9);
x_11 = l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(x_2, x_10, x_4);
return x_11;
}
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
x_1 = lean_mk_string_unchecked(",", 1, 1);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("levelMask", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
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
x_12 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_eq(x_21, x_4);
lean_dec(x_21);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_eq(x_24, x_4);
lean_dec(x_24);
if (x_22 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_68 = lean_array_to_list(x_20);
x_69 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22;
x_70 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(x_68, x_69);
x_71 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26;
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28;
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25;
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = 1;
x_78 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_26 = x_78;
goto block_67;
}
else
{
lean_object* x_79; 
lean_dec(x_20);
x_79 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30;
x_26 = x_79;
goto block_67;
}
block_67:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_8);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_18);
if (x_25 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_36 = lean_array_to_list(x_23);
x_37 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22;
x_38 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__3(x_36, x_37);
x_39 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25;
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = 1;
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15;
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_8);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19;
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21;
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18;
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_8);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_23);
x_58 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32;
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18;
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_8);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4;
x_3 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getFunInductName___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getFunCasesName___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_getMutualInductName___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Meta_getFunInductName(x_2);
x_12 = l_Lean_realizeGlobalConstNoOverloadCore(x_11, x_3, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_7, 0, x_14);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_7);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = l_Lean_Exception_isInterrupt(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
return x_12;
}
}
else
{
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = l_Lean_Meta_getFunCasesName(x_2);
x_33 = l_Lean_realizeGlobalConstNoOverloadCore(x_32, x_3, x_4, x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_7, 0, x_35);
lean_ctor_set(x_33, 0, x_7);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_7, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_7);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = l_Lean_Exception_isInterrupt(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
x_43 = lean_box(0);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_43);
return x_33;
}
else
{
return x_33;
}
}
else
{
return x_33;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = l_Lean_Exception_isInterrupt(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Exception_isRuntime(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_45);
return x_51;
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_dec(x_6);
x_53 = l_Lean_Meta_getFunInductName(x_2);
x_54 = l_Lean_realizeGlobalConstNoOverloadCore(x_53, x_3, x_4, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = l_Lean_Exception_isInterrupt(x_60);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Exception_isRuntime(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_60);
x_65 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_62;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_62)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_62;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
return x_67;
}
}
else
{
lean_object* x_68; 
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_6, 1);
lean_inc(x_69);
lean_dec(x_6);
x_70 = l_Lean_Meta_getFunCasesName(x_2);
x_71 = l_Lean_realizeGlobalConstNoOverloadCore(x_70, x_3, x_4, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Exception_isInterrupt(x_77);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Exception_isRuntime(x_77);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_77);
x_82 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
else
{
lean_object* x_84; 
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
}
else
{
lean_object* x_85; 
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_6, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_6, 0, x_88);
return x_6;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_6, 1);
lean_inc(x_89);
lean_dec(x_6);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_6);
if (x_92 == 0)
{
return x_6;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_6, 0);
x_94 = lean_ctor_get(x_6, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_6);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
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
x_1 = lean_mk_string_unchecked("!(funIndInfoExt.contains ( __do_lift._@.Lean.Meta.Tactic.FunIndInfo._hyg.455.0 ) funIndInfo.funIndName)\n  ", 106, 106);
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
x_3 = lean_unsigned_to_nat(66u);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_instInhabitedFunIndInfo;
x_10 = l_Lean_Meta_setFunIndInfo___closed__1;
x_11 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_8, x_1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_instInhabitedFunIndInfo;
x_16 = l_Lean_Meta_setFunIndInfo___closed__1;
x_17 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_15, x_16, x_14, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
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
l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1 = _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1();
lean_mark_persistent(l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1);
l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2 = _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2();
lean_mark_persistent(l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2);
l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3 = _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3();
lean_mark_persistent(l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3);
l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4 = _init_l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4();
lean_mark_persistent(l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4);
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
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__20);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__21);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__22);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__23);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__24);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__25);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__26);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__27);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__28);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__29);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__30);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__31);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__32);
l_Lean_Meta_instReprFunIndInfo___closed__1 = _init_l_Lean_Meta_instReprFunIndInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprFunIndInfo___closed__1);
l_Lean_Meta_instReprFunIndInfo = _init_l_Lean_Meta_instReprFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instReprFunIndInfo);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_funIndInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
lean_dec_ref(res);
}l_Lean_Meta_getFunInductName___closed__1 = _init_l_Lean_Meta_getFunInductName___closed__1();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__1);
l_Lean_Meta_getFunInductName___closed__2 = _init_l_Lean_Meta_getFunInductName___closed__2();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__2);
l_Lean_Meta_getFunCasesName___closed__1 = _init_l_Lean_Meta_getFunCasesName___closed__1();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__1);
l_Lean_Meta_getFunCasesName___closed__2 = _init_l_Lean_Meta_getFunCasesName___closed__2();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__2);
l_Lean_Meta_getMutualInductName___closed__1 = _init_l_Lean_Meta_getMutualInductName___closed__1();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__1);
l_Lean_Meta_getMutualInductName___closed__2 = _init_l_Lean_Meta_getMutualInductName___closed__2();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__2);
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
