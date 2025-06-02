// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: Lean.Meta.InferType Lean.Compiler.LCNF.Util Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.CompilerM
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_toMonoType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_builtinRuntimeTypes;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1;
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20;
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10;
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255_(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5;
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static uint64_t l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__1;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1665_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
uint8_t l_Lean_Expr_isErased(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4(lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12;
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19;
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_24 = l_Lean_Meta_isProp(x_22, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Meta_isTypeFormerType(x_22, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_array_push(x_4, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_14 = x_35;
x_15 = x_31;
goto block_20;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_array_push(x_4, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_14 = x_40;
x_15 = x_36;
goto block_20;
}
}
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_array_push(x_4, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_14 = x_49;
x_15 = x_45;
goto block_20;
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_21);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_16;
x_9 = x_15;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_get_size(x_2);
x_11 = l_Array_toSubarray___rarg(x_2, x_9, x_10);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
x_17 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2(x_11, x_13, x_15, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.MonoTypes", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.getRelevantCtorFields", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
x_3 = lean_unsigned_to_nat(19u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5() {
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
static uint64_t _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
x_5 = 0;
x_6 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
x_7 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___boxed), 8, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
x_13 = lean_st_mk_ref(x_12, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
lean_inc(x_14);
x_18 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_16, x_17, x_14, x_2, x_3, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_31 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
x_32 = l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1(x_31, x_2, x_3, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ctorName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3;
x_2 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numParams", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l___private_Init_Data_Repr_0__Nat_reprFast(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_8);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
x_29 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_8);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_8);
return x_44;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_array_fget(x_3, x_8);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_5);
lean_ctor_set(x_7, 0, x_5);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_8 = x_23;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_7);
x_25 = lean_box(0);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_2);
x_26 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_5, x_18, x_25, x_11, x_12, x_13);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_6, 2);
x_31 = lean_nat_add(x_8, x_30);
lean_dec(x_8);
x_7 = x_29;
x_8 = x_31;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_13 = x_28;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_7, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_array_fget(x_3, x_8);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_ctor_get(x_6, 2);
x_40 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_7 = x_38;
x_8 = x_40;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_box(0);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_2);
x_43 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_5, x_35, x_42, x_11, x_12, x_13);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_6, 2);
x_48 = lean_nat_add(x_8, x_47);
lean_dec(x_8);
x_7 = x_46;
x_8 = x_48;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_13 = x_45;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_35);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_13);
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_getRelevantCtorFields(x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1;
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(x_1, x_10, x_12, x_14, x_14, x_18, x_19, x_16, lean_box(0), lean_box(0), x_3, x_4, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_5);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*6 + 1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2(x_8, x_12, x_3, x_4, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
return x_6;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Compiler_LCNF_builtinRuntimeTypes;
x_6 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(x_1, x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
x_3 = l_Lean_Compiler_LCNF_getParamTypes_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_expr_instantiate1(x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.toMonoType.visitApp", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(104u);
x_4 = lean_unsigned_to_nat(50u);
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_array_uget(x_3, x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
lean_inc(x_32);
x_33 = l_Lean_Expr_headBeta(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_headBeta(x_12);
switch (lean_obj_tag(x_34)) {
case 3:
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = lean_box(0);
x_37 = x_49;
goto block_48;
}
case 4:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_Compiler_LCNF_anyExpr;
x_56 = l_Lean_Expr_app___override(x_31, x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_56, x_32, x_57, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_58;
goto block_30;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_50);
x_60 = l_Lean_Compiler_LCNF_anyExpr;
x_61 = l_Lean_Expr_app___override(x_31, x_60);
x_62 = lean_box(0);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_61, x_32, x_62, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
x_64 = l_Lean_Compiler_LCNF_anyExpr;
x_65 = l_Lean_Expr_app___override(x_31, x_64);
x_66 = lean_box(0);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_65, x_32, x_66, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_67;
goto block_30;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_68 = l_Lean_Compiler_LCNF_anyExpr;
x_69 = l_Lean_Expr_app___override(x_31, x_68);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_69, x_32, x_70, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_71;
goto block_30;
}
}
block_48:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_toMonoType(x_36, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_31, x_39);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_41, x_32, x_42, x_7, x_8, x_40);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_43;
goto block_30;
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
x_13 = x_38;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_13 = x_47;
goto block_30;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_12);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_72, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_73, 0, x_77);
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_13 = x_81;
goto block_30;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_13 = x_85;
goto block_30;
}
}
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_array_uget(x_3, x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
lean_inc(x_32);
x_33 = l_Lean_Expr_headBeta(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_headBeta(x_12);
switch (lean_obj_tag(x_34)) {
case 3:
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = lean_box(0);
x_37 = x_49;
goto block_48;
}
case 4:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_Compiler_LCNF_anyExpr;
x_56 = l_Lean_Expr_app___override(x_31, x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_56, x_32, x_57, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_58;
goto block_30;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_50);
x_60 = l_Lean_Compiler_LCNF_anyExpr;
x_61 = l_Lean_Expr_app___override(x_31, x_60);
x_62 = lean_box(0);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_61, x_32, x_62, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
x_64 = l_Lean_Compiler_LCNF_anyExpr;
x_65 = l_Lean_Expr_app___override(x_31, x_64);
x_66 = lean_box(0);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_65, x_32, x_66, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_67;
goto block_30;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_68 = l_Lean_Compiler_LCNF_anyExpr;
x_69 = l_Lean_Expr_app___override(x_31, x_68);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_69, x_32, x_70, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_71;
goto block_30;
}
}
block_48:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_toMonoType(x_36, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_31, x_39);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_41, x_32, x_42, x_7, x_8, x_40);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_43;
goto block_30;
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
x_13 = x_38;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_13 = x_47;
goto block_30;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_12);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_72, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_73, 0, x_77);
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_13 = x_81;
goto block_30;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_13 = x_85;
goto block_30;
}
}
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isErased(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_array_uget(x_3, x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
lean_inc(x_32);
x_33 = l_Lean_Expr_headBeta(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_headBeta(x_12);
switch (lean_obj_tag(x_34)) {
case 3:
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = lean_box(0);
x_37 = x_49;
goto block_48;
}
case 4:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_Compiler_LCNF_anyExpr;
x_56 = l_Lean_Expr_app___override(x_31, x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_56, x_32, x_57, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_58;
goto block_30;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_50);
x_60 = l_Lean_Compiler_LCNF_anyExpr;
x_61 = l_Lean_Expr_app___override(x_31, x_60);
x_62 = lean_box(0);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_61, x_32, x_62, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
x_64 = l_Lean_Compiler_LCNF_anyExpr;
x_65 = l_Lean_Expr_app___override(x_31, x_64);
x_66 = lean_box(0);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_65, x_32, x_66, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_67;
goto block_30;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_68 = l_Lean_Compiler_LCNF_anyExpr;
x_69 = l_Lean_Expr_app___override(x_31, x_68);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_69, x_32, x_70, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_71;
goto block_30;
}
}
block_48:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_toMonoType(x_36, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_31, x_39);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_41, x_32, x_42, x_7, x_8, x_40);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_43;
goto block_30;
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
x_13 = x_38;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_13 = x_47;
goto block_30;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_12);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_72, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_73, 0, x_77);
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_13 = x_81;
goto block_30;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_13 = x_85;
goto block_30;
}
}
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_array_uget(x_3, x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
lean_inc(x_32);
x_33 = l_Lean_Expr_headBeta(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_headBeta(x_12);
switch (lean_obj_tag(x_34)) {
case 3:
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = lean_box(0);
x_37 = x_49;
goto block_48;
}
case 4:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_Compiler_LCNF_anyExpr;
x_56 = l_Lean_Expr_app___override(x_31, x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_56, x_32, x_57, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_58;
goto block_30;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_50);
x_60 = l_Lean_Compiler_LCNF_anyExpr;
x_61 = l_Lean_Expr_app___override(x_31, x_60);
x_62 = lean_box(0);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_61, x_32, x_62, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
x_64 = l_Lean_Compiler_LCNF_anyExpr;
x_65 = l_Lean_Expr_app___override(x_31, x_64);
x_66 = lean_box(0);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_65, x_32, x_66, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_67;
goto block_30;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_68 = l_Lean_Compiler_LCNF_anyExpr;
x_69 = l_Lean_Expr_app___override(x_31, x_68);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_69, x_32, x_70, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_71;
goto block_30;
}
}
block_48:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_toMonoType(x_36, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_31, x_39);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_41, x_32, x_42, x_7, x_8, x_40);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_43;
goto block_30;
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
x_13 = x_38;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_13 = x_47;
goto block_30;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_12);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_72, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_73, 0, x_77);
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_13 = x_81;
goto block_30;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_13 = x_85;
goto block_30;
}
}
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_12 = lean_array_uget(x_3, x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
lean_inc(x_32);
x_33 = l_Lean_Expr_headBeta(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_headBeta(x_12);
switch (lean_obj_tag(x_34)) {
case 3:
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = lean_box(0);
x_37 = x_49;
goto block_48;
}
case 4:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_Compiler_LCNF_anyExpr;
x_56 = l_Lean_Expr_app___override(x_31, x_55);
x_57 = lean_box(0);
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_56, x_32, x_57, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_58;
goto block_30;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_37 = x_59;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_50);
x_60 = l_Lean_Compiler_LCNF_anyExpr;
x_61 = l_Lean_Expr_app___override(x_31, x_60);
x_62 = lean_box(0);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_61, x_32, x_62, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_63;
goto block_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_50);
x_64 = l_Lean_Compiler_LCNF_anyExpr;
x_65 = l_Lean_Expr_app___override(x_31, x_64);
x_66 = lean_box(0);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_65, x_32, x_66, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_67;
goto block_30;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_34);
x_68 = l_Lean_Compiler_LCNF_anyExpr;
x_69 = l_Lean_Expr_app___override(x_31, x_68);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_69, x_32, x_70, x_7, x_8, x_9);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_71;
goto block_30;
}
}
block_48:
{
lean_object* x_38; 
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_toMonoType(x_36, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_app___override(x_31, x_39);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_35, x_36, x_41, x_32, x_42, x_7, x_8, x_40);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_35);
x_13 = x_43;
goto block_30;
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
x_13 = x_38;
goto block_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_13 = x_47;
goto block_30;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_12);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_72, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_73, 0, x_77);
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_32);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_13 = x_81;
goto block_30;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
x_13 = x_73;
goto block_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_13 = x_85;
goto block_30;
}
}
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcAny", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Expr_const___override(x_6, x_11);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_7, x_3, x_4, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_array_size(x_2);
x_19 = 0;
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(x_2, x_16, x_2, x_18, x_19, x_17, x_3, x_4, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_38, x_39, x_3, x_4, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_toSubarray___rarg(x_2, x_44, x_43);
x_46 = l_Array_ofSubarray___rarg(x_45);
lean_dec(x_45);
x_47 = l_Lean_Compiler_LCNF_instantiateForall_go(x_46, x_44, x_41, x_3, x_4, x_42);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Compiler_LCNF_getParamTypes(x_48);
x_51 = lean_ctor_get(x_37, 2);
lean_inc(x_51);
lean_dec(x_37);
x_52 = l_Lean_instInhabitedExpr;
x_53 = lean_array_get(x_52, x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_54 = l_Lean_Compiler_LCNF_toMonoType(x_53, x_3, x_4, x_49);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_8);
if (x_63 == 0)
{
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_8, 0);
x_65 = lean_ctor_get(x_8, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_8);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 1:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_6, 0);
lean_inc(x_67);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_ctor_get(x_6, 1);
lean_inc(x_69);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_71 = lean_string_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
x_73 = lean_string_dec_eq(x_69, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
x_75 = lean_string_dec_eq(x_69, x_74);
lean_dec(x_69);
if (x_75 == 0)
{
lean_object* x_76; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_76 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
lean_inc(x_6);
x_80 = l_Lean_Expr_const___override(x_6, x_79);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_68, x_3, x_4, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_82);
x_86 = lean_array_size(x_2);
x_87 = 0;
x_88 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3(x_2, x_84, x_2, x_86, x_87, x_85, x_3, x_4, x_83);
lean_dec(x_2);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_80);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_81);
if (x_100 == 0)
{
return x_81;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_81, 0);
x_102 = lean_ctor_get(x_81, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_81);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_68);
lean_dec(x_6);
x_104 = lean_ctor_get(x_76, 1);
lean_inc(x_104);
lean_dec(x_76);
x_105 = lean_ctor_get(x_77, 0);
lean_inc(x_105);
lean_dec(x_77);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_106, x_107, x_3, x_4, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_toSubarray___rarg(x_2, x_112, x_111);
x_114 = l_Array_ofSubarray___rarg(x_113);
lean_dec(x_113);
x_115 = l_Lean_Compiler_LCNF_instantiateForall_go(x_114, x_112, x_109, x_3, x_4, x_110);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Compiler_LCNF_getParamTypes(x_116);
x_119 = lean_ctor_get(x_105, 2);
lean_inc(x_119);
lean_dec(x_105);
x_120 = l_Lean_instInhabitedExpr;
x_121 = lean_array_get(x_120, x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
x_122 = l_Lean_Compiler_LCNF_toMonoType(x_121, x_3, x_4, x_117);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_105);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
return x_115;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_115, 0);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_115);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_108);
if (x_127 == 0)
{
return x_108;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_108, 0);
x_129 = lean_ctor_get(x_108, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_108);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_76);
if (x_131 == 0)
{
return x_76;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_76, 0);
x_133 = lean_ctor_get(x_76, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_76);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_5);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = l_Lean_Compiler_LCNF_anyExpr;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_5);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_array_get_size(x_2);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_lt(x_140, x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_139);
lean_dec(x_2);
x_142 = l_Lean_Compiler_LCNF_erasedExpr;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_5);
return x_143;
}
else
{
size_t x_144; size_t x_145; uint8_t x_146; 
x_144 = 0;
x_145 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_146 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4(x_2, x_144, x_145);
lean_dec(x_2);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = l_Lean_Compiler_LCNF_erasedExpr;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_5);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = l_Lean_Compiler_LCNF_anyExpr;
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
return x_150;
}
}
}
}
case 1:
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_67);
x_151 = lean_ctor_get(x_1, 1);
lean_inc(x_151);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_152 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_box(0);
lean_inc(x_6);
x_156 = l_Lean_Expr_const___override(x_6, x_155);
lean_inc(x_4);
lean_inc(x_3);
x_157 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_151, x_3, x_4, x_154);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_158);
x_162 = lean_array_size(x_2);
x_163 = 0;
x_164 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5(x_2, x_160, x_2, x_162, x_163, x_161, x_3, x_4, x_159);
lean_dec(x_2);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec(x_166);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_164);
if (x_172 == 0)
{
return x_164;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_164, 0);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_164);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_156);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_157);
if (x_176 == 0)
{
return x_157;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_157, 0);
x_178 = lean_ctor_get(x_157, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_157);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_151);
lean_dec(x_6);
x_180 = lean_ctor_get(x_152, 1);
lean_inc(x_180);
lean_dec(x_152);
x_181 = lean_ctor_get(x_153, 0);
lean_inc(x_181);
lean_dec(x_153);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_184 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_182, x_183, x_3, x_4, x_180);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
x_188 = lean_unsigned_to_nat(0u);
x_189 = l_Array_toSubarray___rarg(x_2, x_188, x_187);
x_190 = l_Array_ofSubarray___rarg(x_189);
lean_dec(x_189);
x_191 = l_Lean_Compiler_LCNF_instantiateForall_go(x_190, x_188, x_185, x_3, x_4, x_186);
lean_dec(x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Compiler_LCNF_getParamTypes(x_192);
x_195 = lean_ctor_get(x_181, 2);
lean_inc(x_195);
lean_dec(x_181);
x_196 = l_Lean_instInhabitedExpr;
x_197 = lean_array_get(x_196, x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
x_198 = l_Lean_Compiler_LCNF_toMonoType(x_197, x_3, x_4, x_193);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_191);
if (x_199 == 0)
{
return x_191;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_191, 0);
x_201 = lean_ctor_get(x_191, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_191);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_181);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_184);
if (x_203 == 0)
{
return x_184;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_184, 0);
x_205 = lean_ctor_get(x_184, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_184);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_151);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_152);
if (x_207 == 0)
{
return x_152;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_152, 0);
x_209 = lean_ctor_get(x_152, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_152);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
default: 
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_67);
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_212 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_box(0);
lean_inc(x_6);
x_216 = l_Lean_Expr_const___override(x_6, x_215);
lean_inc(x_4);
lean_inc(x_3);
x_217 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_211, x_3, x_4, x_214);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; size_t x_222; size_t x_223; lean_object* x_224; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_216);
lean_ctor_set(x_221, 1, x_218);
x_222 = lean_array_size(x_2);
x_223 = 0;
x_224 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6(x_2, x_220, x_2, x_222, x_223, x_221, x_3, x_4, x_219);
lean_dec(x_2);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
lean_ctor_set(x_224, 0, x_227);
return x_224;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_224, 0);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_224);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_224);
if (x_232 == 0)
{
return x_224;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_224, 0);
x_234 = lean_ctor_get(x_224, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_224);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_216);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_236 = !lean_is_exclusive(x_217);
if (x_236 == 0)
{
return x_217;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_217, 0);
x_238 = lean_ctor_get(x_217, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_217);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_211);
lean_dec(x_6);
x_240 = lean_ctor_get(x_212, 1);
lean_inc(x_240);
lean_dec(x_212);
x_241 = lean_ctor_get(x_213, 0);
lean_inc(x_241);
lean_dec(x_213);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_244 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_242, x_243, x_3, x_4, x_240);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_241, 1);
lean_inc(x_247);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Array_toSubarray___rarg(x_2, x_248, x_247);
x_250 = l_Array_ofSubarray___rarg(x_249);
lean_dec(x_249);
x_251 = l_Lean_Compiler_LCNF_instantiateForall_go(x_250, x_248, x_245, x_3, x_4, x_246);
lean_dec(x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_Compiler_LCNF_getParamTypes(x_252);
x_255 = lean_ctor_get(x_241, 2);
lean_inc(x_255);
lean_dec(x_241);
x_256 = l_Lean_instInhabitedExpr;
x_257 = lean_array_get(x_256, x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
x_258 = l_Lean_Compiler_LCNF_toMonoType(x_257, x_3, x_4, x_253);
return x_258;
}
else
{
uint8_t x_259; 
lean_dec(x_241);
lean_dec(x_4);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_251);
if (x_259 == 0)
{
return x_251;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_251, 0);
x_261 = lean_ctor_get(x_251, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_251);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_241);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_244);
if (x_263 == 0)
{
return x_244;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_244, 0);
x_265 = lean_ctor_get(x_244, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_244);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_267 = !lean_is_exclusive(x_212);
if (x_267 == 0)
{
return x_212;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_212, 0);
x_269 = lean_ctor_get(x_212, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_212);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
}
default: 
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_272 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_box(0);
lean_inc(x_6);
x_276 = l_Lean_Expr_const___override(x_6, x_275);
lean_inc(x_4);
lean_inc(x_3);
x_277 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_271, x_3, x_4, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; size_t x_282; size_t x_283; lean_object* x_284; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_278);
x_282 = lean_array_size(x_2);
x_283 = 0;
x_284 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7(x_2, x_280, x_2, x_282, x_283, x_281, x_3, x_4, x_279);
lean_dec(x_2);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec(x_286);
lean_ctor_set(x_284, 0, x_287);
return x_284;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_284, 0);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_284);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
else
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_284);
if (x_292 == 0)
{
return x_284;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_284, 0);
x_294 = lean_ctor_get(x_284, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_284);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_276);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_296 = !lean_is_exclusive(x_277);
if (x_296 == 0)
{
return x_277;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_277, 0);
x_298 = lean_ctor_get(x_277, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_277);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_271);
lean_dec(x_6);
x_300 = lean_ctor_get(x_272, 1);
lean_inc(x_300);
lean_dec(x_272);
x_301 = lean_ctor_get(x_273, 0);
lean_inc(x_301);
lean_dec(x_273);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_304 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_302, x_303, x_3, x_4, x_300);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_301, 1);
lean_inc(x_307);
x_308 = lean_unsigned_to_nat(0u);
x_309 = l_Array_toSubarray___rarg(x_2, x_308, x_307);
x_310 = l_Array_ofSubarray___rarg(x_309);
lean_dec(x_309);
x_311 = l_Lean_Compiler_LCNF_instantiateForall_go(x_310, x_308, x_305, x_3, x_4, x_306);
lean_dec(x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l_Lean_Compiler_LCNF_getParamTypes(x_312);
x_315 = lean_ctor_get(x_301, 2);
lean_inc(x_315);
lean_dec(x_301);
x_316 = l_Lean_instInhabitedExpr;
x_317 = lean_array_get(x_316, x_314, x_315);
lean_dec(x_315);
lean_dec(x_314);
x_318 = l_Lean_Compiler_LCNF_toMonoType(x_317, x_3, x_4, x_313);
return x_318;
}
else
{
uint8_t x_319; 
lean_dec(x_301);
lean_dec(x_4);
lean_dec(x_3);
x_319 = !lean_is_exclusive(x_311);
if (x_319 == 0)
{
return x_311;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_311, 0);
x_321 = lean_ctor_get(x_311, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_311);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_301);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_323 = !lean_is_exclusive(x_304);
if (x_323 == 0)
{
return x_304;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_304, 0);
x_325 = lean_ctor_get(x_304, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_304);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_271);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_327 = !lean_is_exclusive(x_272);
if (x_327 == 0)
{
return x_272;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_272, 0);
x_329 = lean_ctor_get(x_272, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_272);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = l_Lean_Compiler_LCNF_anyExpr;
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_5);
return x_332;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_toMonoType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_set(x_2, x_3, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_1 = x_7;
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_toMonoType_visitApp(x_1, x_2, x_4, x_5, x_6);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_5)) {
case 3:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_erasedExpr;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
x_9 = l_Lean_Compiler_LCNF_toMonoType_visitApp(x_5, x_8, x_2, x_3, x_4);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_10);
x_12 = l_Lean_Compiler_LCNF_toMonoType___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_toMonoType___spec__1(x_5, x_13, x_15, x_2, x_3, x_4);
return x_16;
}
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Lean_Compiler_LCNF_anyExpr;
x_20 = lean_expr_instantiate1(x_18, x_19);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Compiler_LCNF_toMonoType(x_20, x_2, x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_mkArrow(x_32, x_22, x_2, x_3, x_33);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_39 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3;
x_43 = lean_string_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_mkArrow(x_45, x_22, x_2, x_3, x_46);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_52 = l_Lean_Compiler_LCNF_erasedExpr;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_24);
lean_dec(x_23);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_mkArrow(x_56, x_22, x_2, x_3, x_57);
lean_dec(x_3);
lean_dec(x_2);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_23);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_64 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_mkArrow(x_65, x_22, x_2, x_3, x_66);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_mkArrow(x_74, x_22, x_2, x_3, x_75);
lean_dec(x_3);
lean_dec(x_2);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_73);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_21);
if (x_81 == 0)
{
return x_21;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_21, 0);
x_83 = lean_ctor_get(x_21, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_21);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_5, 1);
lean_inc(x_85);
lean_dec(x_5);
x_1 = x_85;
goto _start;
}
default: 
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_87 = l_Lean_Compiler_LCNF_anyExpr;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_4);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__3(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__6(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__7(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1665_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3____spec__1(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_monoTypeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__1___rarg(x_5, x_1, x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_9, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_toMonoType(x_11, x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Compiler_LCNF_CacheExtension_insert___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__2___rarg(x_5, x_1, x_14, x_2, x_3, x_15);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_6, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6();
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__1);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__2);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__3);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__4);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__5);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__6);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__7);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__8);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__9);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__10);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__11);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__12);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__13);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__14);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__15);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__16);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__17);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__18);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__19);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_255____closed__20);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1 = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo);
l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__3);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5);
l_Lean_Compiler_LCNF_toMonoType___closed__1 = _init_l_Lean_Compiler_LCNF_toMonoType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType___closed__1);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1665_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1 = _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
