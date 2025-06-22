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
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedExternAttrData___closed__0;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_;
static lean_object* l_Lean_getExternConstArityExport___closed__25;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_expandExternPatternAux___closed__0;
static lean_object* l_Lean_getExternConstArityExport___closed__17;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22;
LEAN_EXPORT lean_object* l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82____boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_getExternConstArityExport___closed__16;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_getExternAttrData_x3f___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__14;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3;
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
static lean_object* l_Lean_instBEqExternEntry___closed__0;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqExternEntry;
static lean_object* l_Lean_instBEqExternAttrData___closed__0;
lean_object* l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_instHashableExternAttrData;
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_;
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT uint64_t l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477_(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_mkSimpleFnCall___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_getExternConstArityExport___closed__20;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82_(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__2;
static lean_object* l_Lean_getExternConstArityExport___closed__22;
static lean_object* l_Lean_getExternConstArityExport___closed__12;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Array_empty(lean_object*);
static uint8_t l_Lean_getExternConstArityExport___closed__26;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17;
static lean_object* l_Lean_getExternConstArityExport___closed__8;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_instHashableExternEntry___closed__0;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24;
static lean_object* l_Lean_getExternConstArityExport___closed__10;
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_;
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403____boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__3;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instHashableExternAttrData___closed__0;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
static lean_object* l_Lean_getExternConstArityExport___closed__21;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lean_getExternConstArityExport___closed__5;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__1;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25;
static lean_object* l_Lean_getExternConstArityExport___closed__24;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
static lean_object* l_Lean_getExternConstArityExport___closed__6;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__7;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static uint64_t l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20;
LEAN_EXPORT lean_object* l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6;
static lean_object* l_Lean_getExternConstArityExport___closed__27;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26;
lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__1;
static lean_object* l_Lean_getExternConstArityExport___closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
static lean_object* l_Lean_getExternConstArityExport___closed__0;
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__23;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExternAttrData;
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_;
LEAN_EXPORT uint64_t l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403_(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__18;
static lean_object* l_Lean_getExternConstArityExport___closed__13;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0(uint64_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_;
static lean_object* l_Lean_getExternConstArityExport___closed__19;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18;
static lean_object* l_Lean_getExternConstArityExport___closed__11;
static lean_object* l_Lean_getExternConstArityExport___closed__4;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__2;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
static lean_object* l_Lean_getExternConstArityExport___closed__9;
static lean_object* l_Lean_getExternConstArityExport___closed__28;
LEAN_EXPORT lean_object* l_Lean_instHashableExternEntry;
LEAN_EXPORT uint8_t l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_name_eq(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_3 = x_15;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
goto block_9;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_3 = x_21;
x_4 = x_22;
x_5 = x_23;
x_6 = x_24;
goto block_9;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
x_6 = x_30;
goto block_9;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
block_9:
{
uint8_t x_7; 
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqExternEntry___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableExternEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableExternEntry___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedExternAttrData___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_beqExternEntry____x40_Lean_Compiler_ExternAttr___hyg_82_(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371__spec__0(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403__spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqExternAttrData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_403____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqExternAttrData___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0(uint64_t x_1, lean_object* x_2) {
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
x_5 = l_Lean_hashExternEntry____x40_Lean_Compiler_ExternAttr___hyg_266_(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint64_t l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_11; 
x_11 = 11;
x_5 = x_11;
goto block_10;
}
else
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_uint64_of_nat(x_12);
x_14 = 13;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_5 = x_15;
goto block_10;
}
block_10:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = 7;
x_8 = l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0(x_7, x_3);
x_9 = lean_uint64_mix_hash(x_6, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477__spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableExternAttrData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashExternAttrData____x40_Lean_Compiler_ExternAttr___hyg_477____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableExternAttrData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableExternAttrData___closed__0;
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("string literal expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_18 = lean_array_uget(x_3, x_5);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_18, x_41);
x_43 = l_Lean_Syntax_isNone(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_Syntax_getArg(x_42, x_41);
lean_dec(x_42);
x_45 = l_Lean_Syntax_getId(x_44);
lean_dec(x_44);
x_30 = x_45;
goto block_40;
}
else
{
lean_object* x_46; 
lean_dec(x_42);
x_46 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3;
x_30 = x_46;
goto block_40;
}
block_29:
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Syntax_getArg(x_18, x_1);
lean_dec(x_18);
x_24 = l_Lean_Syntax_isNone(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_array_push(x_20, x_25);
x_10 = x_26;
x_11 = x_22;
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_21);
x_28 = lean_array_push(x_20, x_27);
x_10 = x_28;
x_11 = x_22;
goto block_15;
}
}
block_40:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Syntax_getArg(x_18, x_2);
x_32 = l_Lean_Syntax_isStrLit_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_6);
x_33 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1;
x_34 = l_Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(x_31, x_33, x_7, x_8, x_9);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_19 = x_30;
x_20 = x_6;
x_21 = x_39;
x_22 = x_9;
goto block_29;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_10;
x_9 = x_11;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3;
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
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_30; lean_object* x_40; lean_object* x_43; uint8_t x_44; 
x_5 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_1, x_5);
x_44 = l_Lean_Syntax_isNone(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getArg(x_43, x_45);
lean_dec(x_43);
x_47 = l_Lean_Syntax_isNatLit_x3f(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
x_40 = x_45;
goto block_42;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_40 = x_48;
goto block_42;
}
}
else
{
lean_object* x_49; 
lean_dec(x_43);
x_49 = lean_box(0);
x_30 = x_49;
goto block_39;
}
block_29:
{
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0;
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(x_5, x_6, x_8, x_11, x_12, x_10, x_2, x_3, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_array_to_list(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_array_to_list(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_27 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
block_39:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = l_Lean_Syntax_getArgs(x_32);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
x_6 = x_31;
x_7 = x_30;
x_8 = x_33;
x_9 = x_36;
goto block_29;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371__spec__0(x_30, x_37);
x_6 = x_31;
x_7 = x_30;
x_8 = x_33;
x_9 = x_38;
goto block_29;
}
}
block_42:
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_30 = x_41;
goto block_39;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_24; uint8_t x_34; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_10);
x_34 = l_Lean_Environment_isProjectionFn(x_10, x_1);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc(x_1);
lean_inc(x_10);
x_35 = l_Lean_Environment_isConstructor(x_10, x_1);
x_24 = x_35;
goto block_33;
}
else
{
x_24 = x_34;
goto block_33;
}
block_23:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_add_extern(x_10, x_1);
x_15 = l_Lean_ofExcept___at___Lean_Attribute_add_spec__0___redArg(x_14, x_11, x_12, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__7___redArg(x_16, x_12, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
block_33:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_1);
x_25 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_9;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_1);
lean_inc(x_10);
x_29 = l_Lean_Environment_find_x3f(x_10, x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_9);
x_11 = x_3;
x_12 = x_4;
x_13 = x_8;
goto block_23;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 2)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_1);
x_31 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_9;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
else
{
lean_dec(x_30);
lean_dec(x_9);
x_11 = x_3;
x_12 = x_4;
x_13 = x_8;
goto block_23;
}
}
}
}
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externAttr", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin and foreign functions", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed), 5, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed), 5, 0);
x_5 = l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
x_7 = l_Lean_registerParametricAttribute___redArg(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__0____x40_Lean_Compiler_ExternAttr___hyg_1213_(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__1____x40_Lean_Compiler_ExternAttr___hyg_1213_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn___lam__2____x40_Lean_Compiler_ExternAttr___hyg_1213_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_getExternAttrData_x3f___closed__0() {
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
x_4 = l_Lean_getExternAttrData_x3f___closed__0;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; uint32_t x_38; uint8_t x_39; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
lean_dec(x_1);
x_14 = lean_string_utf8_get(x_7, x_8);
x_38 = 48;
x_39 = lean_uint32_dec_le(x_38, x_14);
if (x_39 == 0)
{
x_15 = x_39;
goto block_37;
}
else
{
uint32_t x_40; uint8_t x_41; 
x_40 = 57;
x_41 = lean_uint32_dec_le(x_14, x_40);
x_15 = x_41;
goto block_37;
}
block_37:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_20);
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_nat_mul(x_3, x_21);
lean_dec(x_3);
x_23 = lean_uint32_to_nat(x_14);
x_24 = lean_unsigned_to_nat(48u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_nat_add(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_1 = x_13;
x_3 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_28 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(10u);
x_31 = lean_nat_mul(x_3, x_30);
lean_dec(x_3);
x_32 = lean_uint32_to_nat(x_14);
x_33 = lean_unsigned_to_nat(48u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = lean_nat_add(x_31, x_34);
lean_dec(x_34);
lean_dec(x_31);
x_1 = x_13;
x_2 = x_29;
x_3 = x_35;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_expandExternPatternAux___closed__0() {
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
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_35; uint8_t x_36; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_35 = lean_string_utf8_byte_size(x_7);
x_36 = lean_nat_dec_lt(x_8, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
x_12 = x_6;
goto block_34;
}
else
{
x_12 = x_36;
goto block_34;
}
block_34:
{
uint8_t x_13; 
x_13 = l_instDecidableNot___redArg(x_12);
if (x_13 == 0)
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get(x_7, x_8);
x_15 = 35;
x_16 = lean_uint32_dec_eq(x_14, x_15);
x_17 = l_instDecidableNot___redArg(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_inc(x_18);
lean_inc(x_7);
if (lean_is_scalar(x_9)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_9;
}
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
x_22 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_21, x_19, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_sub(x_24, x_10);
lean_dec(x_24);
x_26 = l_Lean_expandExternPatternAux___closed__0;
x_27 = l_List_getD___redArg(x_1, x_25, x_26);
x_28 = lean_string_append(x_4, x_27);
lean_dec(x_27);
x_2 = x_11;
x_3 = x_23;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
if (lean_is_scalar(x_9)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_9;
}
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_string_push(x_4, x_14);
x_2 = x_11;
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_4;
}
}
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
x_6 = l_Lean_expandExternPatternAux___closed__0;
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
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__2() {
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
x_3 = l_Lean_mkSimpleFnCall___closed__0;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_Lean_expandExternPatternAux___closed__0;
x_6 = l_Lean_mkSimpleFnCall___closed__1;
x_7 = l_List_intersperseTR___redArg(x_6, x_2);
x_8 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_5, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = l_Lean_mkSimpleFnCall___closed__2;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_4, 0);
x_6 = x_14;
goto block_13;
block_13:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_name_eq(x_6, x_1);
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
lean_inc(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
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
lean_object* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
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
lean_object* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
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
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2;
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_13);
return x_16;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
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
lean_object* x_4; 
x_4 = lean_get_extern_attr_data(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_getExternEntryFor(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
switch (lean_obj_tag(x_10)) {
case 2:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
case 3:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
default: 
{
lean_object* x_13; 
lean_free_object(x_7);
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
switch (lean_obj_tag(x_14)) {
case 2:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_box(0);
return x_19;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15;
x_3 = lean_box(0);
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 18);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
return x_6;
}
}
static uint64_t _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25;
x_5 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20;
x_9 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19;
x_10 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_2);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*7, x_8);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 8, x_11);
x_12 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 9, x_12);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 10, x_13);
return x_10;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_39; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed), 7, 0);
lean_inc(x_1);
x_39 = lean_get_extern_attr_data(x_9, x_1);
if (lean_obj_tag(x_39) == 0)
{
lean_free_object(x_5);
x_11 = x_2;
x_12 = x_3;
x_13 = x_8;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_free_object(x_5);
x_11 = x_2;
x_12 = x_3;
x_13 = x_8;
goto block_38;
}
else
{
lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
}
block_38:
{
lean_object* x_14; 
x_14 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18;
x_18 = lean_st_mk_ref(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_ConstantInfo_type(x_15);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26;
x_24 = lean_unbox(x_22);
x_25 = lean_unbox(x_22);
lean_inc(x_19);
x_26 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_21, x_10, x_24, x_25, x_23, x_19, x_11, x_12, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_19, x_28);
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_dec(x_19);
return x_26;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_74; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed), 7, 0);
lean_inc(x_1);
x_74 = lean_get_extern_attr_data(x_45, x_1);
if (lean_obj_tag(x_74) == 0)
{
x_47 = x_2;
x_48 = x_3;
x_49 = x_44;
goto block_73;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
x_47 = x_2;
x_48 = x_3;
x_49 = x_44;
goto block_73;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_44);
return x_78;
}
}
block_73:
{
lean_object* x_50; 
x_50 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_47, x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18;
x_54 = lean_st_mk_ref(x_53, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_ConstantInfo_type(x_51);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26;
x_60 = lean_unbox(x_58);
x_61 = lean_unbox(x_58);
lean_inc(x_55);
x_62 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_57, x_46, x_60, x_61, x_59, x_55, x_47, x_48, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_get(x_55, x_64);
lean_dec(x_55);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_dec(x_55);
return x_62;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_71 = x_50;
} else {
 lean_dec_ref(x_50);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_getExternConstArityExport___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_getExternConstArityExport___closed__4;
x_4 = l_Lean_getExternConstArityExport___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__7() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__9;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_getExternConstArityExport___closed__4;
x_4 = l_Lean_getExternConstArityExport___closed__11;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getExternConstArityExport___closed__12;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getExternConstArityExport___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__17() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_getExternConstArityExport___closed__4;
x_4 = l_Lean_getExternConstArityExport___closed__16;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Lean_getExternConstArityExport___closed__17;
x_2 = l_Lean_getExternConstArityExport___closed__15;
x_3 = l_Lean_getExternConstArityExport___closed__14;
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<compiler>", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__22;
x_2 = l_Lean_expandExternPatternAux___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lean_getExternConstArityExport___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__25;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__27;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_87; 
x_8 = lean_io_get_num_heartbeats(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_getExternConstArityExport___closed__2;
x_16 = l_Lean_getExternConstArityExport___closed__3;
x_17 = l_Lean_getExternConstArityExport___closed__7;
x_18 = l_Lean_getExternConstArityExport___closed__10;
x_19 = l_Lean_getExternConstArityExport___closed__13;
x_20 = l_Lean_getExternConstArityExport___closed__18;
x_21 = l_Lean_getExternConstArityExport___closed__19;
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
x_23 = lean_st_mk_ref(x_22, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_getExternConstArityExport___closed__20;
x_27 = lean_st_ref_get(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_24, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_getExternConstArityExport___closed__21;
x_35 = l_Lean_getExternConstArityExport___closed__23;
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_getExternConstArityExport___closed__24;
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = l_Lean_getExternConstArityExport___closed__26;
x_87 = l_Lean_Kernel_isDiagnosticsEnabled(x_33);
lean_dec(x_33);
if (x_87 == 0)
{
if (x_42 == 0)
{
lean_inc(x_24);
x_43 = x_24;
x_44 = x_32;
goto block_64;
}
else
{
goto block_86;
}
}
else
{
if (x_42 == 0)
{
goto block_86;
}
else
{
lean_inc(x_24);
x_43 = x_24;
x_44 = x_32;
goto block_64;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_64:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_45 = l_Lean_getExternConstArityExport___closed__28;
x_46 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_11);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_37);
lean_ctor_set(x_46, 6, x_12);
lean_ctor_set(x_46, 7, x_38);
lean_ctor_set(x_46, 8, x_9);
lean_ctor_set(x_46, 9, x_39);
lean_ctor_set(x_46, 10, x_13);
lean_ctor_set(x_46, 11, x_41);
lean_ctor_set(x_46, 12, x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*13, x_42);
x_47 = lean_unbox(x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 1, x_47);
x_48 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_2, x_46, x_43, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_24, x_50);
lean_dec(x_24);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_24);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_MessageData_toString(x_60, x_59);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_4 = x_62;
goto block_7;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_dec(x_48);
x_4 = x_63;
goto block_7;
}
}
}
block_86:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_st_ref_take(x_24, x_32);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 5);
lean_dec(x_70);
x_71 = l_Lean_Kernel_enableDiag(x_69, x_42);
lean_ctor_set(x_66, 5, x_18);
lean_ctor_set(x_66, 0, x_71);
x_72 = lean_st_ref_set(x_24, x_66, x_67);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_inc(x_24);
x_43 = x_24;
x_44 = x_73;
goto block_64;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
x_76 = lean_ctor_get(x_66, 2);
x_77 = lean_ctor_get(x_66, 3);
x_78 = lean_ctor_get(x_66, 4);
x_79 = lean_ctor_get(x_66, 6);
x_80 = lean_ctor_get(x_66, 7);
x_81 = lean_ctor_get(x_66, 8);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_82 = l_Lean_Kernel_enableDiag(x_74, x_42);
x_83 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_76);
lean_ctor_set(x_83, 3, x_77);
lean_ctor_set(x_83, 4, x_78);
lean_ctor_set(x_83, 5, x_18);
lean_ctor_set(x_83, 6, x_79);
lean_ctor_set(x_83, 7, x_80);
lean_ctor_set(x_83, 8, x_81);
x_84 = lean_st_ref_set(x_24, x_83, x_67);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_24);
x_43 = x_24;
x_44 = x_85;
goto block_64;
}
}
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
l_Lean_instBEqExternEntry___closed__0 = _init_l_Lean_instBEqExternEntry___closed__0();
lean_mark_persistent(l_Lean_instBEqExternEntry___closed__0);
l_Lean_instBEqExternEntry = _init_l_Lean_instBEqExternEntry();
lean_mark_persistent(l_Lean_instBEqExternEntry);
l_Lean_instHashableExternEntry___closed__0 = _init_l_Lean_instHashableExternEntry___closed__0();
lean_mark_persistent(l_Lean_instHashableExternEntry___closed__0);
l_Lean_instHashableExternEntry = _init_l_Lean_instHashableExternEntry();
lean_mark_persistent(l_Lean_instHashableExternEntry);
l_Lean_instInhabitedExternAttrData___closed__0 = _init_l_Lean_instInhabitedExternAttrData___closed__0();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData___closed__0);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
l_Lean_instBEqExternAttrData___closed__0 = _init_l_Lean_instBEqExternAttrData___closed__0();
lean_mark_persistent(l_Lean_instBEqExternAttrData___closed__0);
l_Lean_instBEqExternAttrData = _init_l_Lean_instBEqExternAttrData();
lean_mark_persistent(l_Lean_instBEqExternAttrData);
l_Lean_instHashableExternAttrData___closed__0 = _init_l_Lean_instHashableExternAttrData___closed__0();
lean_mark_persistent(l_Lean_instHashableExternAttrData___closed__0);
l_Lean_instHashableExternAttrData = _init_l_Lean_instHashableExternAttrData();
lean_mark_persistent(l_Lean_instHashableExternAttrData);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___closed__3);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2);
l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3);
l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Compiler_ExternAttr___hyg_1213_);
l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_ = _init_l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Compiler_ExternAttr___hyg_1213_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_1213_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
}l_Lean_getExternAttrData_x3f___closed__0 = _init_l_Lean_getExternAttrData_x3f___closed__0();
lean_mark_persistent(l_Lean_getExternAttrData_x3f___closed__0);
l_Lean_expandExternPatternAux___closed__0 = _init_l_Lean_expandExternPatternAux___closed__0();
lean_mark_persistent(l_Lean_expandExternPatternAux___closed__0);
l_Lean_mkSimpleFnCall___closed__0 = _init_l_Lean_mkSimpleFnCall___closed__0();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__0);
l_Lean_mkSimpleFnCall___closed__1 = _init_l_Lean_mkSimpleFnCall___closed__1();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__1);
l_Lean_mkSimpleFnCall___closed__2 = _init_l_Lean_mkSimpleFnCall___closed__2();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__2);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__0);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2);
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
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20();
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26);
l_Lean_getExternConstArityExport___closed__0 = _init_l_Lean_getExternConstArityExport___closed__0();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__0);
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
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__15);
l_Lean_getExternConstArityExport___closed__16 = _init_l_Lean_getExternConstArityExport___closed__16();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__16);
l_Lean_getExternConstArityExport___closed__17 = _init_l_Lean_getExternConstArityExport___closed__17();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__17);
l_Lean_getExternConstArityExport___closed__18 = _init_l_Lean_getExternConstArityExport___closed__18();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__18);
l_Lean_getExternConstArityExport___closed__19 = _init_l_Lean_getExternConstArityExport___closed__19();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__19);
l_Lean_getExternConstArityExport___closed__20 = _init_l_Lean_getExternConstArityExport___closed__20();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__20);
l_Lean_getExternConstArityExport___closed__21 = _init_l_Lean_getExternConstArityExport___closed__21();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__21);
l_Lean_getExternConstArityExport___closed__22 = _init_l_Lean_getExternConstArityExport___closed__22();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__22);
l_Lean_getExternConstArityExport___closed__23 = _init_l_Lean_getExternConstArityExport___closed__23();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__23);
l_Lean_getExternConstArityExport___closed__24 = _init_l_Lean_getExternConstArityExport___closed__24();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__24);
l_Lean_getExternConstArityExport___closed__25 = _init_l_Lean_getExternConstArityExport___closed__25();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__25);
l_Lean_getExternConstArityExport___closed__26 = _init_l_Lean_getExternConstArityExport___closed__26();
l_Lean_getExternConstArityExport___closed__27 = _init_l_Lean_getExternConstArityExport___closed__27();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__27);
l_Lean_getExternConstArityExport___closed__28 = _init_l_Lean_getExternConstArityExport___closed__28();
lean_mark_persistent(l_Lean_getExternConstArityExport___closed__28);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
