// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: Init Lean.Expr Lean.Environment Lean.Attributes Lean.ProjFns Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6;
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_getExternAttrData_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExternAttrData;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9;
lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7;
static lean_object* l_Lean_getExternConstArityExport___closed__2;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Class___hyg_769____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11;
LEAN_EXPORT lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__3;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17;
uint8_t l_String_Iterator_hasNext(lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__8;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10;
LEAN_EXPORT uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1036____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_341____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4;
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24;
LEAN_EXPORT lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__3;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__5;
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
static lean_object* l_Lean_getExternConstArityExport___closed__5;
LEAN_EXPORT lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__1;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
static lean_object* l_Lean_getExternConstArityExport___closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1;
lean_object* l_String_Iterator_remainingBytes(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__7;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__6;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
lean_object* l_List_intersperse___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExternEntry_backend(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__4;
extern lean_object* l_Lean_firstFrontendMacroScope;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_expandExternPatternAux___closed__2;
static lean_object* l_Lean_instInhabitedExternAttrData___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3;
LEAN_EXPORT lean_object* l_Lean_ExternAttrData_arity_x3f___default;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
LEAN_EXPORT lean_object* l_Lean_externAttr;
LEAN_EXPORT lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18;
static lean_object* l_Lean_getExternConstArityExport___closed__4;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleFnCall___closed__2;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23;
static lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650_(lean_object*);
static lean_object* l_Lean_getExternConstArityExport___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
static uint8_t l_Lean_expandExternPatternAux___closed__1;
static uint8_t l_Lean_expandExternPatternAux___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_ExternAttrData_arity_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
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
lean_dec(x_1);
lean_ctor_set(x_3, 5, x_8);
x_9 = l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
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
x_22 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set(x_23, 3, x_13);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_23, 6, x_16);
lean_ctor_set(x_23, 7, x_17);
lean_ctor_set(x_23, 8, x_18);
lean_ctor_set(x_23, 9, x_19);
lean_ctor_set(x_23, 10, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*11, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__2(x_2, x_23, x_4, x_5);
lean_dec(x_4);
lean_dec(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("string literal expected", 23);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("all", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_array_uget(x_1, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_10, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_10, x_21);
x_23 = l_Lean_Syntax_isStrLit_x3f(x_22);
if (x_20 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Syntax_getArg(x_19, x_18);
lean_dec(x_19);
x_25 = l_Lean_Syntax_getId(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_4);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
x_27 = l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(x_22, x_26, x_5, x_6, x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_10, x_25, x_4, x_32, x_5, x_6, x_7);
lean_dec(x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_11 = x_34;
x_12 = x_35;
goto block_17;
}
}
else
{
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_4);
x_36 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2;
x_37 = l_Lean_throwErrorAt___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__1(x_22, x_36, x_5, x_6, x_7);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_22);
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_10, x_43, x_4, x_42, x_5, x_6, x_7);
lean_dec(x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_11 = x_45;
x_12 = x_46;
goto block_17;
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
x_7 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_usize_of_nat(x_1);
x_9 = 0;
x_10 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(x_2, x_8, x_9, x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_to_list(lean_box(0), x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
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
x_18 = lean_array_to_list(lean_box(0), x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
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
lean_dec(x_3);
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
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
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
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
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
x_16 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_11, x_10, x_14, x_15, x_2, x_3, x_4);
lean_dec(x_10);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1036____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_341____spec__1(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_11, x_10, x_14, x_19, x_2, x_3, x_4);
lean_dec(x_10);
lean_dec(x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1;
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
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_6);
x_16 = lean_add_extern(x_10, x_1);
x_17 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Class___hyg_769____spec__1(x_16, x_3, x_4, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__3(x_18, x_3, x_4, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_6);
x_25 = lean_add_extern(x_10, x_1);
x_26 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Class___hyg_769____spec__1(x_25, x_3, x_4, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__3(x_27, x_3, x_4, x_28);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_instInhabitedProjectionFunctionInfo;
x_38 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1;
lean_inc(x_1);
lean_inc(x_36);
x_39 = l_Lean_MapDeclarationExtension_contains___rarg(x_37, x_38, x_36, x_1);
if (x_39 == 0)
{
uint8_t x_40; 
lean_inc(x_1);
lean_inc(x_36);
x_40 = l_Lean_Environment_isConstructor(x_36, x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_add_extern(x_36, x_1);
x_44 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Class___hyg_769____spec__1(x_43, x_3, x_4, x_35);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__3(x_45, x_3, x_4, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_add_extern(x_36, x_1);
x_53 = l_Lean_ofExcept___at_Lean_initFn____x40_Lean_Class___hyg_769____spec__1(x_52, x_3, x_4, x_35);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_setEnv___at_Lean_registerParametricAttribute___spec__3(x_54, x_3, x_4, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("externAttr", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extern", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("builtin and foreign functions", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5;
x_3 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7;
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8;
x_3 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9;
x_4 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11;
x_3 = l_Lean_registerParametricAttribute___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__3(x_1, x_2, x_3);
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = l_String_Iterator_hasNext(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = l_String_Iterator_curr(x_2);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 57;
x_15 = lean_uint32_dec_le(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = l_String_Iterator_next(x_2);
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_nat_mul(x_3, x_18);
lean_dec(x_3);
x_20 = lean_uint32_to_nat(x_10);
x_21 = lean_unsigned_to_nat(48u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_add(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_1 = x_7;
x_2 = x_17;
x_3 = x_23;
goto _start;
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
static uint8_t _init_l_Lean_expandExternPatternAux___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_expandExternPatternAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static uint8_t _init_l_Lean_expandExternPatternAux___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = l_String_Iterator_hasNext(x_3);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_expandExternPatternAux___closed__1;
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; uint8_t x_14; 
x_11 = l_String_Iterator_curr(x_3);
x_12 = 35;
x_13 = lean_uint32_dec_eq(x_11, x_12);
x_14 = l_instDecidableNot___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = l_String_Iterator_next(x_3);
x_16 = l_String_Iterator_remainingBytes(x_15);
x_17 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_16, x_15, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_nat_sub(x_19, x_7);
lean_dec(x_19);
x_21 = l_Lean_expandExternPatternAux___closed__2;
x_22 = l_List_getD___rarg(x_1, x_20, x_21);
x_23 = lean_string_append(x_4, x_22);
lean_dec(x_22);
x_2 = x_8;
x_3 = x_18;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_String_Iterator_next(x_3);
x_26 = lean_string_push(x_4, x_11);
x_2 = x_8;
x_3 = x_25;
x_4 = x_26;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_expandExternPatternAux___closed__3;
if (x_28 == 0)
{
uint32_t x_29; uint32_t x_30; uint8_t x_31; uint8_t x_32; 
x_29 = l_String_Iterator_curr(x_3);
x_30 = 35;
x_31 = lean_uint32_dec_eq(x_29, x_30);
x_32 = l_instDecidableNot___rarg(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = l_String_Iterator_next(x_3);
x_34 = l_String_Iterator_remainingBytes(x_33);
x_35 = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(x_34, x_33, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_nat_sub(x_37, x_7);
lean_dec(x_37);
x_39 = l_Lean_expandExternPatternAux___closed__2;
x_40 = l_List_getD___rarg(x_1, x_38, x_39);
x_41 = lean_string_append(x_4, x_40);
lean_dec(x_40);
x_2 = x_8;
x_3 = x_36;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_String_Iterator_next(x_3);
x_44 = lean_string_push(x_4, x_29);
x_2 = x_8;
x_3 = x_43;
x_4 = x_44;
goto _start;
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
x_6 = l_Lean_expandExternPatternAux___closed__2;
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
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleFnCall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
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
x_6 = l_List_intersperse___rarg(x_5, x_2);
x_7 = l_Lean_expandExternPatternAux___closed__2;
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
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4;
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
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3;
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
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__4;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__1;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__8;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__10;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__17;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__18;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__21;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__26;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__14;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__16;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__23;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__13;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28;
x_4 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30() {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29;
x_18 = lean_st_mk_ref(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30;
x_22 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_19);
x_23 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_16, x_21, x_22, x_19, x_2, x_3, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_19, x_25);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_free_object(x_5);
x_41 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_ConstantInfo_type(x_42);
lean_dec(x_42);
x_45 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29;
x_46 = lean_st_mk_ref(x_45, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30;
x_50 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_47);
x_51 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_44, x_49, x_50, x_47, x_2, x_3, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_get(x_47, x_53);
lean_dec(x_47);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_47);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_40, 0);
lean_inc(x_67);
lean_dec(x_40);
lean_ctor_set(x_5, 0, x_67);
return x_5;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_5);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_instInhabitedExternAttrData;
x_72 = l_Lean_getExternAttrData_x3f___closed__1;
lean_inc(x_1);
x_73 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_71, x_72, x_70, x_1);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_ConstantInfo_type(x_75);
lean_dec(x_75);
x_78 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29;
x_79 = lean_st_mk_ref(x_78, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30;
x_83 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_80);
x_84 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_77, x_82, x_83, x_80, x_2, x_3, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_get(x_80, x_86);
lean_dec(x_80);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_93 = x_84;
} else {
 lean_dec_ref(x_84);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_ctor_get(x_74, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_97 = x_74;
} else {
 lean_dec_ref(x_74);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_73, 0);
lean_inc(x_99);
lean_dec(x_73);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_1, x_2, x_3, x_69);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_ConstantInfo_type(x_102);
lean_dec(x_102);
x_105 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29;
x_106 = lean_st_mk_ref(x_105, x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30;
x_110 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__9;
lean_inc(x_107);
x_111 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_104, x_109, x_110, x_107, x_2, x_3, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_get(x_107, x_113);
lean_dec(x_107);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_107);
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_120 = x_111;
} else {
 lean_dec_ref(x_111);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_101, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_101, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_124 = x_101;
} else {
 lean_dec_ref(x_101);
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
lean_object* x_126; lean_object* x_127; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_100, 0);
lean_inc(x_126);
lean_dec(x_100);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_69);
return x_127;
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
static lean_object* _init_l_Lean_getExternConstArityExport___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_expandExternPatternAux___closed__2;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getExternConstArityExport___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getExternConstArityExport___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__12;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__11;
x_3 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_getExternConstArityExport___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<compiler>", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_get_extern_const_arity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_box(0);
x_5 = l_Lean_getExternConstArityExport___closed__3;
x_6 = l_Lean_getExternConstArityExport___closed__6;
x_7 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__7;
x_8 = l_Lean_getExternConstArityExport___closed__7;
x_9 = l_Lean_getExternConstArityExport___closed__8;
x_10 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_7);
lean_ctor_set(x_10, 6, x_9);
x_11 = lean_io_get_num_heartbeats(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_getExternConstArityExport___closed__9;
x_15 = l_Lean_getExternConstArityExport___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1000u);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_getExternConstArityExport___closed__2;
x_21 = l_Lean_firstFrontendMacroScope;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 3, x_16);
lean_ctor_set(x_23, 4, x_17);
lean_ctor_set(x_23, 5, x_18);
lean_ctor_set(x_23, 6, x_19);
lean_ctor_set(x_23, 7, x_4);
lean_ctor_set(x_23, 8, x_12);
lean_ctor_set(x_23, 9, x_20);
lean_ctor_set(x_23, 10, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*11, x_22);
x_24 = lean_st_mk_ref(x_10, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity(x_2, x_23, x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_25, x_29);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_toString(x_39, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_37);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_27, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_55);
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_dec(x_27);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
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
res = initialize_Init(builtin, lean_io_mk_world());
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
l_Lean_ExternAttrData_arity_x3f___default = _init_l_Lean_ExternAttrData_arity_x3f___default();
lean_mark_persistent(l_Lean_ExternAttrData_arity_x3f___default);
l_Lean_instInhabitedExternAttrData___closed__1 = _init_l_Lean_instInhabitedExternAttrData___closed__1();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData___closed__1);
l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___spec__3___closed__4);
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
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____lambda__2___closed__1);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__1);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__2);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__3);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__4);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__5);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__6);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__7);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__8);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__9);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__10);
l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11 = _init_l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650____closed__11);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ExternAttr___hyg_650_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
}l_Lean_getExternAttrData_x3f___closed__1 = _init_l_Lean_getExternAttrData_x3f___closed__1();
lean_mark_persistent(l_Lean_getExternAttrData_x3f___closed__1);
l_Lean_expandExternPatternAux___closed__1 = _init_l_Lean_expandExternPatternAux___closed__1();
l_Lean_expandExternPatternAux___closed__2 = _init_l_Lean_expandExternPatternAux___closed__2();
lean_mark_persistent(l_Lean_expandExternPatternAux___closed__2);
l_Lean_expandExternPatternAux___closed__3 = _init_l_Lean_expandExternPatternAux___closed__3();
l_Lean_mkSimpleFnCall___closed__1 = _init_l_Lean_mkSimpleFnCall___closed__1();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__1);
l_Lean_mkSimpleFnCall___closed__2 = _init_l_Lean_mkSimpleFnCall___closed__2();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__2);
l_Lean_mkSimpleFnCall___closed__3 = _init_l_Lean_mkSimpleFnCall___closed__3();
lean_mark_persistent(l_Lean_mkSimpleFnCall___closed__3);
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
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__20);
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
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__27);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__28);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__29);
l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30 = _init_l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30();
lean_mark_persistent(l___private_Lean_Compiler_ExternAttr_0__Lean_getExternConstArity___closed__30);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
