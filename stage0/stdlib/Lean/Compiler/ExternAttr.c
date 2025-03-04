// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: Init.Data.List.BasicAux Lean.Expr Lean.Environment Lean.Attributes Lean.ProjFns Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instBEqExternAttrData___closed__1;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_getExternAttrData_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__14;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10;
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry;
lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1(uint64_t, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData;
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
static uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____closed__1;
uint64_t lean_string_hash(lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getExternConstArityExport___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__2;
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
static lean_object* l_Lean_getExternConstArityExport___closed__12;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Lean_instHashableExternAttrData___closed__1;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__8;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__10;
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___lambda__1___closed__1;
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__3;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
static lean_object* l_Lean_getExternConstArityExport___closed__5;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__1;
static lean_object* l_Lean_instBEqExternEntry___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
static lean_object* l_Lean_getExternConstArityExport___closed__6;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__7;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed(lean_object*);
lean_object* l_Lean_throwError___at_Lean_initFn____x40_Lean_Class___hyg_789____spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__1;
static uint8_t l_Lean_getExternConstArityExport___closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
lean_object* l_List_intersperseTR___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData;
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternConstArityExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__13;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed(lean_object*);
static lean_object* l_Lean_instInhabitedExternAttrData___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7;
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
static lean_object* l_Lean_getExternConstArityExport___closed__11;
static lean_object* l_Lean_getExternConstArityExport___closed__4;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__2;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
static lean_object* l_Lean_getExternConstArityExport___closed__9;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_expandExternPatternAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry;
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instHashableExternEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_name_eq(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_8, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_name_eq(x_15, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_string_dec_eq(x_16, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_name_eq(x_23, x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_string_dec_eq(x_24, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqExternEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = 1;
x_9 = l_Lean_Name_hash___override(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_string_hash(x_7);
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = 2;
x_16 = l_Lean_Name_hash___override(x_13);
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = lean_string_hash(x_14);
x_19 = lean_uint64_mix_hash(x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = 3;
x_23 = l_Lean_Name_hash___override(x_20);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = lean_string_hash(x_21);
x_26 = lean_uint64_mix_hash(x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableExternEntry___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedExternAttrData___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_66_(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324____spec__1(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternAttrData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_382____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqExternAttrData___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_250_(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
static uint64_t _init_l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 0;
x_2 = 11;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_5 = 7;
x_6 = l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1(x_5, x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_7; uint64_t x_8; 
x_7 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____closed__1;
x_8 = lean_uint64_mix_hash(x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_uint64_of_nat(x_9);
x_11 = 13;
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = lean_uint64_mix_hash(x_4, x_12);
x_14 = lean_uint64_mix_hash(x_13, x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternAttrData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableExternAttrData___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 5);
x_8 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 5, x_8);
x_9 = l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*12);
x_22 = lean_ctor_get(x_3, 11);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*12 + 1);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_24 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_25, 6, x_16);
lean_ctor_set(x_25, 7, x_17);
lean_ctor_set(x_25, 8, x_18);
lean_ctor_set(x_25, 9, x_19);
lean_ctor_set(x_25, 10, x_20);
lean_ctor_set(x_25, 11, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*12, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*12 + 1, x_23);
x_26 = l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(x_2, x_25, x_4, x_5);
lean_dec(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_array_push(x_3, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_array_push(x_3, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("string literal expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_array_uget(x_3, x_5);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_12, x_20);
x_22 = l_Lean_Syntax_isNone(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_12, x_23);
x_25 = l_Lean_Syntax_isStrLit_x3f(x_24);
if (x_22 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Syntax_getArg(x_21, x_20);
lean_dec(x_21);
x_27 = l_Lean_Syntax_getId(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_6);
x_28 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
x_29 = l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(x_24, x_28, x_7, x_8, x_9);
lean_dec(x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_12, x_27, x_6, x_34, x_7, x_8, x_9);
lean_dec(x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_13 = x_36;
x_14 = x_37;
goto block_19;
}
}
else
{
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_6);
x_38 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
x_39 = l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(x_24, x_38, x_7, x_8, x_9);
lean_dec(x_24);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
x_46 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_12, x_45, x_6, x_44, x_7, x_8, x_9);
lean_dec(x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_13 = x_47;
x_14 = x_48;
goto block_19;
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(x_1, x_7, x_1, x_8, x_9, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_to_list(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_array_to_list(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isNone(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_7 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Syntax_getArg(x_6, x_12);
lean_dec(x_6);
x_25 = l_Lean_Syntax_isNatLit_x3f(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4;
x_14 = x_26;
goto block_23;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
x_14 = x_25;
goto block_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_14 = x_29;
goto block_23;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
x_30 = lean_box(0);
x_14 = x_30;
goto block_23;
}
block_23:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_10, x_14, x_15, x_2, x_3, x_4);
lean_dec(x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324____spec__1(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_10, x_14, x_19, x_2, x_3, x_4);
lean_dec(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_2);
x_21 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_extern(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_stringToMessageData(x_5);
x_7 = l_Lean_throwError___at_Lean_initFn____x40_Lean_Class___hyg_789____spec__2(x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_add_extern(x_1, x_2);
x_8 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1(x_7, x_4, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__4(x_9, x_4, x_5, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instInhabitedProjectionFunctionInfo;
x_12 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1;
lean_inc(x_1);
lean_inc(x_10);
x_13 = l_Lean_MapDeclarationExtension_contains___rarg(x_11, x_12, x_10, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_1);
lean_inc(x_10);
x_14 = l_Lean_Environment_isConstructor(x_10, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; 
lean_inc(x_1);
lean_inc(x_10);
x_16 = l_Lean_Environment_find_x3f(x_10, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
x_17 = lean_box(0);
x_18 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_10, x_1, x_17, x_3, x_4, x_9);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_free_object(x_6);
x_21 = lean_box(0);
x_22 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_10, x_1, x_21, x_3, x_4, x_9);
return x_22;
}
}
}
}
else
{
lean_object* x_23; 
lean_inc(x_1);
lean_inc(x_10);
x_23 = l_Lean_Environment_find_x3f(x_10, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
x_24 = lean_box(0);
x_25 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_10, x_1, x_24, x_3, x_4, x_9);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 2)
{
lean_object* x_27; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_free_object(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_10, x_1, x_28, x_3, x_4, x_9);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_instInhabitedProjectionFunctionInfo;
x_34 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1;
lean_inc(x_1);
lean_inc(x_32);
x_35 = l_Lean_MapDeclarationExtension_contains___rarg(x_33, x_34, x_32, x_1);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_1);
lean_inc(x_32);
x_36 = l_Lean_Environment_isConstructor(x_32, x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
else
{
lean_object* x_39; 
lean_inc(x_1);
lean_inc(x_32);
x_39 = l_Lean_Environment_find_x3f(x_32, x_1);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
x_41 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_32, x_1, x_40, x_3, x_4, x_31);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
if (lean_obj_tag(x_42) == 2)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_32, x_1, x_45, x_3, x_4, x_31);
return x_46;
}
}
}
}
else
{
lean_object* x_47; 
lean_inc(x_1);
lean_inc(x_32);
x_47 = l_Lean_Environment_find_x3f(x_32, x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_32, x_1, x_48, x_3, x_4, x_31);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
if (lean_obj_tag(x_50) == 2)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_50);
lean_dec(x_32);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_31);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_32, x_1, x_53, x_3, x_4, x_31);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externAttr", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin and foreign functions", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5;
x_3 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8;
x_3 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9;
x_4 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11;
x_3 = l_Lean_registerParametricAttribute___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_getExternAttrData_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_externAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExternAttrData;
x_4 = l_Lean_getExternAttrData_x3f___closed__1;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_13 = 48;
x_14 = lean_string_utf8_get(x_8, x_9);
x_15 = lean_uint32_dec_le(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(10u);
x_24 = lean_nat_mul(x_3, x_23);
lean_dec(x_3);
x_25 = lean_uint32_to_nat(x_14);
x_26 = lean_unsigned_to_nat(48u);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_25);
x_28 = lean_nat_add(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
x_29 = lean_string_utf8_next(x_8, x_9);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_29);
x_1 = x_7;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(10u);
x_32 = lean_nat_mul(x_3, x_31);
lean_dec(x_3);
x_33 = lean_uint32_to_nat(x_14);
x_34 = lean_unsigned_to_nat(48u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = lean_nat_add(x_32, x_35);
lean_dec(x_35);
lean_dec(x_32);
x_37 = lean_string_utf8_next(x_8, x_9);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_37);
x_1 = x_7;
x_2 = x_38;
x_3 = x_36;
goto _start;
}
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
}
static lean_object* _init_l_Lean_expandExternPatternAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_string_utf8_byte_size(x_9);
lean_dec(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_58; 
x_58 = 0;
x_13 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = 1;
x_13 = x_59;
goto block_57;
}
block_57:
{
uint8_t x_14; 
x_14 = l_instDecidableNot___rarg(x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 35;
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_string_utf8_get(x_17, x_18);
x_20 = lean_uint32_dec_eq(x_19, x_15);
x_21 = l_instDecidableNot___rarg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_string_utf8_next(x_17, x_18);
lean_dec(x_18);
lean_inc(x_22);
lean_inc(x_17);
lean_ctor_set(x_3, 1, x_22);
x_23 = lean_string_utf8_byte_size(x_17);
lean_dec(x_17);
x_24 = lean_nat_sub(x_23, x_22);
lean_dec(x_22);
lean_dec(x_23);
x_25 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_24, x_3, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_sub(x_27, x_7);
lean_dec(x_27);
x_29 = l_Lean_expandExternPatternAux___closed__1;
x_30 = l_List_getD___rarg(x_1, x_28, x_29);
x_31 = lean_string_append(x_4, x_30);
lean_dec(x_30);
x_2 = x_8;
x_3 = x_26;
x_4 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_string_push(x_4, x_19);
x_34 = lean_string_utf8_next(x_17, x_18);
lean_dec(x_18);
lean_ctor_set(x_3, 1, x_34);
x_2 = x_8;
x_4 = x_33;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint32_t x_38; uint8_t x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_38 = lean_string_utf8_get(x_36, x_37);
x_39 = lean_uint32_dec_eq(x_38, x_15);
x_40 = l_instDecidableNot___rarg(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_string_utf8_next(x_36, x_37);
lean_dec(x_37);
lean_inc(x_41);
lean_inc(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_string_utf8_byte_size(x_36);
lean_dec(x_36);
x_44 = lean_nat_sub(x_43, x_41);
lean_dec(x_41);
lean_dec(x_43);
x_45 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_44, x_42, x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_nat_sub(x_47, x_7);
lean_dec(x_47);
x_49 = l_Lean_expandExternPatternAux___closed__1;
x_50 = l_List_getD___rarg(x_1, x_48, x_49);
x_51 = lean_string_append(x_4, x_50);
lean_dec(x_50);
x_2 = x_8;
x_3 = x_46;
x_4 = x_51;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_string_push(x_4, x_38);
x_54 = lean_string_utf8_next(x_36, x_37);
lean_dec(x_37);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_54);
x_2 = x_8;
x_3 = x_55;
x_4 = x_53;
goto _start;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_string_length(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_expandExternPatternAux___closed__1;
x_7 = l_Lean_expandExternPatternAux(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_expandExternPattern(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_mkSimpleFnCall___closed__1;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_Lean_mkSimpleFnCall___closed__2;
x_6 = l_List_intersperseTR___rarg(x_5, x_2);
x_7 = l_Lean_expandExternPatternAux___closed__1;
x_8 = l_List_foldl___at_String_join___spec__1(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = l_Lean_mkSimpleFnCall___closed__3;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_ExternEntry_backend(x_4);
x_7 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_inc(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_getExternEntryForAux(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExternAttrData;
x_4 = l_Lean_getExternAttrData_x3f___closed__1;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_3, x_4, x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExternAttrData;
x_4 = l_Lean_getExternAttrData_x3f___closed__1;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_3, x_4, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_13);
x_17 = 0;
return x_17;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
x_19 = 0;
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_20 = 0;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_8);
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_8);
x_22 = 0;
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_instInhabitedExternAttrData;
x_5 = l_Lean_getExternAttrData_x3f___closed__1;
x_6 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_4, x_5, x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_getExternEntryFor(x_8, x_2);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
switch (lean_obj_tag(x_12)) {
case 2:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
case 3:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
default: 
{
lean_object* x_15; 
lean_free_object(x_9);
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
switch (lean_obj_tag(x_16)) {
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_box(0);
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
x_5 = 0;
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
x_7 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instInhabitedExternAttrData;
x_11 = l_Lean_getExternAttrData_x3f___closed__1;
lean_inc(x_1);
x_12 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_10, x_11, x_9, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_5);
x_13 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_18 = lean_st_mk_ref(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_22 = 0;
x_23 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_19);
x_24 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_16, x_21, x_22, x_23, x_19, x_2, x_3, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_19, x_26);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_free_object(x_5);
x_42 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_ConstantInfo_type(x_43);
lean_dec(x_43);
x_46 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_47 = lean_st_mk_ref(x_46, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_51 = 0;
x_52 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_48);
x_53 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_45, x_50, x_51, x_52, x_48, x_2, x_3, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_get(x_48, x_55);
lean_dec(x_48);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_48);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_42);
if (x_65 == 0)
{
return x_42;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_42, 0);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_42);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_41, 0);
lean_inc(x_69);
lean_dec(x_41);
lean_ctor_set(x_5, 0, x_69);
return x_5;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_5);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_instInhabitedExternAttrData;
x_74 = l_Lean_getExternAttrData_x3f___closed__1;
lean_inc(x_1);
x_75 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_73, x_74, x_72, x_1);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_ConstantInfo_type(x_77);
lean_dec(x_77);
x_80 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_81 = lean_st_mk_ref(x_80, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_85 = 0;
x_86 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_82);
x_87 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_79, x_84, x_85, x_86, x_82, x_2, x_3, x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_82, x_89);
lean_dec(x_82);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_82);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_76, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_76, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_100 = x_76;
} else {
 lean_dec_ref(x_76);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_75, 0);
lean_inc(x_102);
lean_dec(x_75);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_71);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_ConstantInfo_type(x_105);
lean_dec(x_105);
x_108 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_109 = lean_st_mk_ref(x_108, x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_113 = 0;
x_114 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_110);
x_115 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_107, x_112, x_113, x_114, x_110, x_2, x_3, x_111);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_get(x_110, x_117);
lean_dec(x_110);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_110);
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
lean_dec(x_2);
x_126 = lean_ctor_get(x_104, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_128 = x_104;
} else {
 lean_dec_ref(x_104);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_103, 0);
lean_inc(x_130);
lean_dec(x_103);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_71);
return x_131;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getExternConstArityExport___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lean_getExternConstArityExport___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*12, x_2);
x_13 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_25 = l_Lean_getExternConstArityExport___lambda__1___closed__1;
x_26 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_17);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_24);
x_28 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_3, x_27, x_6, x_7);
return x_28;
}
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_expandExternPatternAux___closed__1;
x_2 = l_Lean_getExternConstArityExport___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getExternConstArityExport___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__7;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__9() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__12() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<compiler>", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lean_getExternConstArityExport___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getExternConstArityExport___closed__14;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_21; lean_object* x_22; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; 
x_46 = lean_box(0);
x_47 = lean_box(0);
x_48 = l_Lean_getExternConstArityExport___closed__5;
x_49 = l_Lean_getExternConstArityExport___closed__8;
x_50 = l_Lean_getExternConstArityExport___closed__9;
x_51 = l_Lean_getExternConstArityExport___closed__10;
x_52 = l_Lean_getExternConstArityExport___closed__11;
x_53 = l_Lean_getExternConstArityExport___closed__12;
x_54 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set(x_55, 6, x_53);
lean_ctor_set(x_55, 7, x_54);
x_56 = lean_io_get_num_heartbeats(x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_getExternConstArityExport___closed__13;
x_60 = l_Lean_getExternConstArityExport___closed__3;
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unsigned_to_nat(1000u);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = l_Lean_getExternConstArityExport___closed__4;
x_66 = l_Lean_firstFrontendMacroScope;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_46);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_63);
lean_ctor_set(x_68, 6, x_64);
lean_ctor_set(x_68, 7, x_46);
lean_ctor_set(x_68, 8, x_57);
lean_ctor_set(x_68, 9, x_65);
lean_ctor_set(x_68, 10, x_66);
lean_ctor_set(x_68, 11, x_47);
lean_ctor_set_uint8(x_68, sizeof(void*)*12, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*12 + 1, x_67);
x_69 = lean_st_mk_ref(x_55, x_58);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_70, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Kernel_isDiagnosticsEnabled(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_155; 
x_155 = l_Lean_getExternConstArityExport___closed__15;
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = 1;
x_77 = x_156;
goto block_154;
}
else
{
x_77 = x_67;
goto block_154;
}
}
else
{
uint8_t x_157; 
x_157 = l_Lean_getExternConstArityExport___closed__15;
if (x_157 == 0)
{
x_77 = x_67;
goto block_154;
}
else
{
uint8_t x_158; 
x_158 = 1;
x_77 = x_158;
goto block_154;
}
}
block_20:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
block_45:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MessageData_toString(x_23, x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_27);
x_4 = x_24;
goto block_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_4 = x_31;
goto block_20;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_dec(x_34);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_36 = l_Lean_getExternConstArityExport___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_21, 1, x_22);
lean_ctor_set(x_21, 0, x_38);
x_4 = x_21;
goto block_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_39);
x_41 = l_Lean_getExternConstArityExport___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_22);
x_4 = x_44;
goto block_20;
}
}
}
block_154:
{
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_st_ref_take(x_70, x_74);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 4);
lean_dec(x_83);
x_84 = l_Lean_getExternConstArityExport___closed__15;
x_85 = l_Lean_Kernel_enableDiag(x_82, x_84);
lean_ctor_set(x_79, 4, x_51);
lean_ctor_set(x_79, 0, x_85);
x_86 = lean_st_ref_set(x_70, x_79, x_80);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(0);
lean_inc(x_70);
x_89 = l_Lean_getExternConstArityExport___lambda__1(x_46, x_84, x_2, x_88, x_68, x_70, x_87);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_st_ref_get(x_70, x_91);
lean_dec(x_70);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_ctor_set(x_89, 1, x_94);
lean_ctor_set(x_92, 0, x_89);
x_4 = x_92;
goto block_20;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set(x_89, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_96);
x_4 = x_97;
goto block_20;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_st_ref_get(x_70, x_99);
lean_dec(x_70);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_101);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
x_4 = x_105;
goto block_20;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_70);
x_106 = lean_ctor_get(x_89, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
lean_dec(x_89);
x_21 = x_106;
x_22 = x_107;
goto block_45;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_ctor_get(x_79, 0);
x_109 = lean_ctor_get(x_79, 1);
x_110 = lean_ctor_get(x_79, 2);
x_111 = lean_ctor_get(x_79, 3);
x_112 = lean_ctor_get(x_79, 5);
x_113 = lean_ctor_get(x_79, 6);
x_114 = lean_ctor_get(x_79, 7);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_79);
x_115 = l_Lean_getExternConstArityExport___closed__15;
x_116 = l_Lean_Kernel_enableDiag(x_108, x_115);
x_117 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_110);
lean_ctor_set(x_117, 3, x_111);
lean_ctor_set(x_117, 4, x_51);
lean_ctor_set(x_117, 5, x_112);
lean_ctor_set(x_117, 6, x_113);
lean_ctor_set(x_117, 7, x_114);
x_118 = lean_st_ref_set(x_70, x_117, x_80);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_box(0);
lean_inc(x_70);
x_121 = l_Lean_getExternConstArityExport___lambda__1(x_46, x_115, x_2, x_120, x_68, x_70, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_st_ref_get(x_70, x_123);
lean_dec(x_70);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
x_4 = x_130;
goto block_20;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_70);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_dec(x_121);
x_21 = x_131;
x_22 = x_132;
goto block_45;
}
}
}
else
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_133 = l_Lean_getExternConstArityExport___closed__15;
x_134 = lean_box(0);
lean_inc(x_70);
x_135 = l_Lean_getExternConstArityExport___lambda__1(x_46, x_133, x_2, x_134, x_68, x_70, x_74);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_135, 1);
x_138 = lean_st_ref_get(x_70, x_137);
lean_dec(x_70);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_ctor_set(x_135, 1, x_140);
lean_ctor_set(x_138, 0, x_135);
x_4 = x_138;
goto block_20;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_138, 0);
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_138);
lean_ctor_set(x_135, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_142);
x_4 = x_143;
goto block_20;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_135);
x_146 = lean_st_ref_get(x_70, x_145);
lean_dec(x_70);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_147);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
x_4 = x_151;
goto block_20;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_70);
x_152 = lean_ctor_get(x_135, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_135, 1);
lean_inc(x_153);
lean_dec(x_135);
x_21 = x_152;
x_22 = x_153;
goto block_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExternConstArityExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_getExternConstArityExport___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instBEqExternEntry___closed__1 = _init_l_Lean_instBEqExternEntry___closed__1();
lean_mark_persistent(l_Lean_instBEqExternEntry___closed__1);
l_Lean_instBEqExternEntry = _init_l_Lean_instBEqExternEntry();
lean_mark_persistent(l_Lean_instBEqExternEntry);
l_Lean_instHashableExternEntry___closed__1 = _init_l_Lean_instHashableExternEntry___closed__1();
lean_mark_persistent(l_Lean_instHashableExternEntry___closed__1);
l_Lean_instHashableExternEntry = _init_l_Lean_instHashableExternEntry();
lean_mark_persistent(l_Lean_instHashableExternEntry);
l_Lean_instInhabitedExternAttrData___closed__1 = _init_l_Lean_instInhabitedExternAttrData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData___closed__1);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
l_Lean_instBEqExternAttrData___closed__1 = _init_l_Lean_instBEqExternAttrData___closed__1();
lean_mark_persistent(l_Lean_instBEqExternAttrData___closed__1);
l_Lean_instBEqExternAttrData = _init_l_Lean_instBEqExternAttrData();
lean_mark_persistent(l_Lean_instBEqExternAttrData);
l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_456____closed__1();
l_Lean_instHashableExternAttrData___closed__1 = _init_l_Lean_instHashableExternAttrData___closed__1();
lean_mark_persistent(l_Lean_instHashableExternAttrData___closed__1);
l_Lean_instHashableExternAttrData = _init_l_Lean_instHashableExternAttrData();
lean_mark_persistent(l_Lean_instHashableExternAttrData);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____lambda__3___closed__1);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__1);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__2);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__3);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__4);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__5);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__6);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__7);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__8);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__9);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__10);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192____closed__11);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
}l_Lean_getExternAttrData_x3f___closed__1 = _init_l_Lean_getExternAttrData_x3f___closed__1();
lean_mark_persistent(l_Lean_getExternAttrData_x3f___closed__1);
l_Lean_expandExternPatternAux___closed__1 = _init_l_Lean_expandExternPatternAux___closed__1();
lean_mark_persistent(l_Lean_expandExternPatternAux___closed__1);
l_Lean_mkSimpleFnCall___closed__1 = _init_l_Lean_mkSimpleFnCall___closed__1();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__1);
l_Lean_mkSimpleFnCall___closed__2 = _init_l_Lean_mkSimpleFnCall___closed__2();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__2);
l_Lean_mkSimpleFnCall___closed__3 = _init_l_Lean_mkSimpleFnCall___closed__3();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__3);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2();
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14);
l_Lean_getExternConstArityExport___lambda__1___closed__1 = _init_l_Lean_getExternConstArityExport___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getExternConstArityExport___lambda__1___closed__1);
l_Lean_getExternConstArityExport___closed__1 = _init_l_Lean_getExternConstArityExport___closed__1();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__1);
l_Lean_getExternConstArityExport___closed__2 = _init_l_Lean_getExternConstArityExport___closed__2();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__2);
l_Lean_getExternConstArityExport___closed__3 = _init_l_Lean_getExternConstArityExport___closed__3();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__3);
l_Lean_getExternConstArityExport___closed__4 = _init_l_Lean_getExternConstArityExport___closed__4();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__4);
l_Lean_getExternConstArityExport___closed__5 = _init_l_Lean_getExternConstArityExport___closed__5();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__5);
l_Lean_getExternConstArityExport___closed__6 = _init_l_Lean_getExternConstArityExport___closed__6();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__6);
l_Lean_getExternConstArityExport___closed__7 = _init_l_Lean_getExternConstArityExport___closed__7();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__7);
l_Lean_getExternConstArityExport___closed__8 = _init_l_Lean_getExternConstArityExport___closed__8();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__8);
l_Lean_getExternConstArityExport___closed__9 = _init_l_Lean_getExternConstArityExport___closed__9();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__9);
l_Lean_getExternConstArityExport___closed__10 = _init_l_Lean_getExternConstArityExport___closed__10();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__10);
l_Lean_getExternConstArityExport___closed__11 = _init_l_Lean_getExternConstArityExport___closed__11();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__11);
l_Lean_getExternConstArityExport___closed__12 = _init_l_Lean_getExternConstArityExport___closed__12();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__12);
l_Lean_getExternConstArityExport___closed__13 = _init_l_Lean_getExternConstArityExport___closed__13();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__13);
l_Lean_getExternConstArityExport___closed__14 = _init_l_Lean_getExternConstArityExport___closed__14();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__14);
l_Lean_getExternConstArityExport___closed__15 = _init_l_Lean_getExternConstArityExport___closed__15();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
