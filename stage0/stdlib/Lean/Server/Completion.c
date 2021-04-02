// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Init Lean.Environment Lean.Data.Lsp.LanguageFeatures Lean.Server.InfoUtils
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
lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__4;
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Server_Completion_find_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_noConfusionExt;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Elab_Info_occursBefore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_isSmaller(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__2;
lean_object* l_Lean_Server_Completion_find_x3f___closed__1;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt;
lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__1;
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__3(lean_object*);
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5(lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__2(lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__3;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___closed__5;
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__1(lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_match__2(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(lean_object*, lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1(lean_object*);
uint8_t l_Lean_Elab_Info_isDotCompletion(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___boxed(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__4;
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7(lean_object*);
lean_object* l_Lean_Elab_Info_tailPos_x3f(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4(lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1(lean_object*);
lean_object* lean_completion_add_to_black_list(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed(lean_object*);
lean_object* l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2(lean_object*);
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_find_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9(lean_object*);
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8(lean_object*);
lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4_(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("blackListCompletion");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_completionBlackListExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Server_Completion_completionBlackListExt___closed__1;
x_4 = l_Lean_Server_Completion_completionBlackListExt___closed__2;
x_5 = l_Lean_Server_Completion_completionBlackListExt___closed__3;
x_6 = l_Lean_Server_Completion_completionBlackListExt___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Completion_completionBlackListExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Completion_completionBlackListExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Completion_completionBlackListExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Completion_completionBlackListExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_completion_add_to_black_list(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_Completion_completionBlackListExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Completion_completionBlackListExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListed(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_isRecCore(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_isRecCore(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_auxRecExt;
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_10, x_1);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_noConfusionExt;
x_17 = l_Lean_TagDeclarationExtension_isTagged(x_16, x_10, x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_unbox(x_13);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = l_Lean_Server_Completion_completionBlackListExt;
x_20 = l_Lean_TagDeclarationExtension_isTagged(x_19, x_10, x_1);
lean_dec(x_1);
lean_dec(x_10);
x_21 = lean_box(x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_1);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_1);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_1);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = l_Lean_auxRecExt;
x_31 = l_Lean_TagDeclarationExtension_isTagged(x_30, x_10, x_1);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_noConfusionExt;
x_33 = l_Lean_TagDeclarationExtension_isTagged(x_32, x_10, x_1);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_unbox(x_28);
lean_dec(x_28);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_Server_Completion_completionBlackListExt;
x_36 = l_Lean_TagDeclarationExtension_isTagged(x_35, x_10, x_1);
lean_dec(x_1);
lean_dec(x_10);
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_1);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_1);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_1);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_29);
return x_47;
}
}
}
}
lean_object* l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isRec___at___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Elab_Info_isDotCompletion(x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Info_occursBefore_x3f(x_5, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_66; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_66 = l_Lean_Elab_Info_tailPos_x3f(x_5);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = l_instInhabitedNat;
x_68 = l_Option_get_x21___rarg___closed__4;
x_69 = lean_panic_fn(x_67, x_68);
x_70 = l_Lean_FileMap_toPosition(x_2, x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_nat_dec_eq(x_71, x_3);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_11 = x_73;
goto block_65;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Lean_FileMap_toPosition(x_2, x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_nat_dec_eq(x_76, x_3);
lean_dec(x_76);
if (x_77 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
x_11 = x_78;
goto block_65;
}
}
block_65:
{
lean_dec(x_11);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
if (lean_is_scalar(x_10)) {
 x_13 = lean_alloc_ctor(1, 1, 0);
} else {
 x_13 = x_10;
}
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_Info_occursBefore_x3f(x_16, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_instInhabitedNat;
x_20 = l_Option_get_x21___rarg___closed__4;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = lean_nat_dec_lt(x_9, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_9, x_21);
lean_dec(x_21);
lean_dec(x_9);
if (x_23 == 0)
{
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_24; 
x_24 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_24 == 0)
{
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
return x_6;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_14);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_6, 0);
lean_dec(x_29);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
return x_6;
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_nat_dec_lt(x_9, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_9, x_32);
lean_dec(x_32);
lean_dec(x_9);
if (x_34 == 0)
{
lean_free_object(x_18);
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_35 == 0)
{
lean_free_object(x_18);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_nat_dec_lt(x_9, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_nat_dec_eq(x_9, x_36);
lean_dec(x_36);
lean_dec(x_9);
if (x_38 == 0)
{
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_39; 
x_39 = l_Lean_Elab_Info_isSmaller(x_5, x_16);
lean_dec(x_16);
if (x_39 == 0)
{
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_40; 
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_14);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_4);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_14);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec(x_14);
x_43 = l_Lean_Elab_Info_occursBefore_x3f(x_42, x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_instInhabitedNat;
x_45 = l_Option_get_x21___rarg___closed__4;
x_46 = lean_panic_fn(x_44, x_45);
x_47 = lean_nat_dec_lt(x_9, x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = lean_nat_dec_eq(x_9, x_46);
lean_dec(x_46);
lean_dec(x_9);
if (x_48 == 0)
{
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_Elab_Info_isSmaller(x_5, x_42);
lean_dec(x_42);
if (x_49 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_50 = x_6;
} else {
 lean_dec_ref(x_6);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_5);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_53 = x_6;
} else {
 lean_dec_ref(x_6);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_5);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
x_58 = lean_nat_dec_lt(x_9, x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_nat_dec_eq(x_9, x_56);
lean_dec(x_56);
lean_dec(x_9);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_60; 
x_60 = l_Lean_Elab_Info_isSmaller(x_5, x_42);
lean_dec(x_42);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_5);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_6);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_5);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
}
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f_choose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Completion_find_x3f_choose(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = x_3 + x_8;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_3(x_1, x_5, x_10, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg(x_1, x_14, x_5);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_1, x_12, x_13, lean_box(0), x_14, x_3);
return x_15;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = x_3 + x_8;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_3(x_1, x_5, x_10, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg(x_1, x_14, x_5);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_1, x_12, x_13, lean_box(0), x_14, x_3);
return x_15;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Std_AssocList_foldlM___at_Lean_Server_Completion_find_x3f___spec__2___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = x_3 + x_8;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = lean_apply_3(x_1, x_5, x_10, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg(x_1, x_14, x_5);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Lean_mkModuleData___spec__5___rarg(x_1, x_12, x_13, lean_box(0), x_14, x_3);
return x_15;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg(x_1, x_4, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg(x_1, x_4, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg(x_1, x_6, x_13, x_14, x_2);
x_16 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg(x_1, x_4, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_ConstantInfo_name(x_11);
lean_inc(x_12);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_isBlackListedForCompletion(x_12, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_18 = l_Lean_Meta_ppExpr(x_17, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Name_getString_x21(x_12);
lean_dec(x_12);
x_22 = l_Std_Format_defWidth;
x_23 = lean_format_pretty(x_19, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_array_push(x_4, x_26);
x_28 = 1;
x_29 = x_2 + x_28;
x_2 = x_29;
x_4 = x_27;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = 1;
x_37 = x_2 + x_36;
x_2 = x_37;
x_9 = x_35;
goto _start;
}
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
}
lean_object* l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_le(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_usize_of_nat(x_2);
x_17 = lean_usize_of_nat(x_3);
x_18 = l_Array_empty___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14(x_1, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Name_isInternal(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Name_getPrefix(x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_array_push(x_2, x_4);
return x_8;
}
}
else
{
lean_dec(x_4);
return x_2;
}
}
}
lean_object* l_Lean_Server_Completion_find_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_inferType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_instantiateMVars(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_getAppFn(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_12);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_7, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f___lambda__1___boxed), 4, 1);
lean_closure_set(x_22, 0, x_17);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Array_empty___closed__1;
x_25 = l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg(x_22, x_24, x_23);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13(x_25, x_27, x_26, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = l_Lean_Expr_getAppFn(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_46) == 4)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_get(x_7, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f___lambda__1___boxed), 4, 1);
lean_closure_set(x_52, 0, x_47);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Array_empty___closed__1;
x_55 = l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg(x_52, x_54, x_53);
lean_dec(x_53);
x_56 = lean_array_get_size(x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13(x_55, x_57, x_56, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = 1;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_45);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
return x_12;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_12, 0);
x_73 = lean_ctor_get(x_12, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_12);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_9);
if (x_75 == 0)
{
return x_9;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_9, 0);
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_9);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
static lean_object* _init_l_Lean_Server_Completion_find_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> ");
return x_1;
}
}
lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_FileMap_toPosition(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f_choose___boxed), 6, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Elab_InfoTree_foldInfo___rarg(x_7, x_8, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_formatStxAux(x_8, x_17, x_18, x_16);
x_20 = l_Std_Format_defWidth;
x_21 = lean_format_pretty(x_19, x_20);
x_22 = l_Lean_Server_Completion_find_x3f___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_term_x5b___x5d___closed__5;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
x_27 = lean_expr_dbg_to_string(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = l_Lean_instInhabitedParserDescr___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Server_Completion_find_x3f___lambda__2___boxed), 8, 2);
lean_closure_set(x_31, 0, x_26);
lean_closure_set(x_31, 1, x_8);
x_32 = lean_dbg_trace(x_30, x_31);
x_33 = l_Lean_Elab_TermInfo_runMetaM___rarg(x_15, x_13, x_32, x_4);
lean_dec(x_13);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__8___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__7___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__6___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__9___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__12___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_find_x3f___spec__11___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_foldlM___at_Lean_Server_Completion_find_x3f___spec__10___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_fold___at_Lean_Server_Completion_find_x3f___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_find_x3f___spec__14(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at_Lean_Server_Completion_find_x3f___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Server_Completion_find_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Completion_find_x3f___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Completion_find_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_find_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_Completion(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__1);
l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2 = _init_l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4____closed__2);
l_Lean_Server_Completion_completionBlackListExt___closed__1 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__1);
l_Lean_Server_Completion_completionBlackListExt___closed__2 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__2();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__2);
l_Lean_Server_Completion_completionBlackListExt___closed__3 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__3();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__3);
l_Lean_Server_Completion_completionBlackListExt___closed__4 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__4();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__4);
l_Lean_Server_Completion_completionBlackListExt___closed__5 = _init_l_Lean_Server_Completion_completionBlackListExt___closed__5();
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt___closed__5);
res = l_Lean_Server_Completion_initFn____x40_Lean_Server_Completion___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Completion_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Completion_completionBlackListExt);
lean_dec_ref(res);
l_Lean_Server_Completion_find_x3f___closed__1 = _init_l_Lean_Server_Completion_find_x3f___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_find_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
