// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: Init Lean.Meta.InferType Lean.Compiler.LCNF.Util Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.CompilerM
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
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_toMonoType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
extern lean_object* l_Lean_Compiler_LCNF_builtinRuntimeTypes;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8;
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_MonoTypeExtState_mono___default;
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10;
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1;
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22;
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__4(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31;
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974_(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472_(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29;
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13;
static lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28;
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.MonoTypes", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.getRelevantCtorFields", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
x_3 = lean_unsigned_to_nat(18u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lambda__1___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_12 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33;
x_13 = lean_st_mk_ref(x_12, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
lean_inc(x_14);
x_17 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_16, x_14, x_2, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_14, x_19);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
x_31 = l_panic___at_Lean_Compiler_LCNF_getRelevantCtorFields___spec__1(x_30, x_2, x_3, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
return x_5;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ctorName", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3;
x_2 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("numParams", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fieldIdx", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" }", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12;
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
x_29 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Nat_repr(x_32);
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
x_38 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_8);
return x_44;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____boxed), 2, 0);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_9, x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_nat_dec_lt(x_8, x_5);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_instInhabitedBool;
x_25 = lean_box(x_24);
x_26 = l___private_Init_Util_0__outOfBounds___rarg(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_6);
lean_ctor_set(x_11, 0, x_6);
x_28 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_28;
goto _start;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_11);
x_30 = lean_box(0);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
x_31 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_6, x_21, x_30, x_12, x_13, x_14);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_35;
x_11 = x_34;
x_14 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_11, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_14);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_fget(x_3, x_8);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_6);
lean_ctor_set(x_11, 0, x_6);
x_41 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_41;
goto _start;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_11);
x_43 = lean_box(0);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
x_44 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_6, x_21, x_43, x_12, x_13, x_14);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_48;
x_11 = x_47;
x_14 = x_46;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_11, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_14);
return x_51;
}
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_nat_dec_lt(x_8, x_5);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_instInhabitedBool;
x_55 = lean_box(x_54);
x_56 = l___private_Init_Util_0__outOfBounds___rarg(x_55);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_inc(x_6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_6);
lean_ctor_set(x_58, 1, x_52);
x_59 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_59;
x_11 = x_58;
goto _start;
}
else
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_box(0);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
x_62 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_6, x_52, x_61, x_12, x_13, x_14);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_66;
x_11 = x_65;
x_14 = x_64;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_4);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_14);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_array_fget(x_3, x_8);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_inc(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_52);
x_74 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_74;
x_11 = x_73;
goto _start;
}
else
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_box(0);
lean_inc(x_6);
lean_inc(x_8);
lean_inc(x_2);
x_77 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_8, x_6, x_52, x_76, x_12, x_13, x_14);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_81;
x_11 = x_80;
x_14 = x_79;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_4);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_52);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_14);
return x_85;
}
}
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_11);
lean_ctor_set(x_86, 1, x_14);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_11);
lean_ctor_set(x_87, 1, x_14);
return x_87;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1;
lean_inc(x_15);
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(x_1, x_10, x_12, x_14, x_15, x_14, x_15, x_16, x_15, x_17, x_18, x_3, x_4, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_dec(x_2);
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
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*5 + 1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
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
x_6 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_1, x_5);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_hasTrivialStructure_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.toMonoType.visitApp", 38);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(98u);
x_4 = lean_unsigned_to_nat(50u);
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_array_uget(x_1, x_3);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_dec(x_4);
lean_inc(x_30);
x_31 = l_Lean_Expr_headBeta(x_30);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_47; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_headBeta(x_10);
x_47 = l_Lean_Expr_isErased(x_34);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isErased(x_32);
if (x_48 == 0)
{
if (lean_obj_tag(x_32) == 3)
{
lean_object* x_49; 
lean_dec(x_32);
x_49 = lean_box(0);
x_35 = x_49;
goto block_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_32);
x_50 = l_Lean_Compiler_LCNF_erasedExpr;
x_51 = l_Lean_Expr_app___override(x_29, x_50);
x_52 = lean_box(0);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_33, x_34, x_51, x_30, x_52, x_5, x_6, x_7);
lean_dec(x_30);
lean_dec(x_34);
lean_dec(x_33);
x_11 = x_53;
goto block_28;
}
}
else
{
lean_object* x_54; 
lean_dec(x_32);
x_54 = lean_box(0);
x_35 = x_54;
goto block_46;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_32);
lean_inc(x_34);
x_55 = l_Lean_Expr_app___override(x_29, x_34);
x_56 = lean_box(0);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_33, x_34, x_55, x_30, x_56, x_5, x_6, x_7);
lean_dec(x_30);
lean_dec(x_34);
lean_dec(x_33);
x_11 = x_57;
goto block_28;
}
block_46:
{
lean_object* x_36; 
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
x_36 = l_Lean_Compiler_LCNF_toMonoType(x_34, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_app___override(x_29, x_37);
x_40 = lean_box(0);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_33, x_34, x_39, x_30, x_40, x_5, x_6, x_38);
lean_dec(x_30);
lean_dec(x_34);
lean_dec(x_33);
x_11 = x_41;
goto block_28;
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
x_11 = x_36;
goto block_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_11 = x_45;
goto block_28;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_31);
lean_dec(x_10);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2;
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_panic___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__1(x_58, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_29);
lean_ctor_set(x_62, 1, x_30);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_59, 0, x_63);
x_11 = x_59;
goto block_28;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_29);
lean_ctor_set(x_65, 1, x_30);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_11 = x_67;
goto block_28;
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_29);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
x_11 = x_59;
goto block_28;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_59, 0);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_59);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_11 = x_71;
goto block_28;
}
}
}
block_28:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_20;
x_7 = x_19;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_1, x_5, x_6, x_7);
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
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_1, x_11);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_2, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_get_size(x_3);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(x_3, x_18, x_19, x_16, x_5, x_6, x_15);
lean_dec(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_38, x_39, x_5, x_6, x_36);
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
x_45 = l_Array_toSubarray___rarg(x_3, x_44, x_43);
x_46 = l_Array_ofSubarray___rarg(x_45);
lean_inc(x_5);
x_47 = l_Lean_Compiler_LCNF_instantiateForall_go(x_46, x_44, x_41, x_5, x_6, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Compiler_LCNF_getParamTypes(x_48);
x_51 = lean_ctor_get(x_37, 2);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_array_get_size(x_50);
x_53 = lean_nat_dec_lt(x_51, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_50);
x_54 = l_Lean_instInhabitedExpr;
x_55 = l___private_Init_Util_0__outOfBounds___rarg(x_54);
x_56 = l_Lean_Compiler_LCNF_toMonoType(x_55, x_5, x_6, x_49);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fget(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
x_58 = l_Lean_Compiler_LCNF_toMonoType(x_57, x_5, x_6, x_49);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
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
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_40);
if (x_63 == 0)
{
return x_40;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_40, 0);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_40);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
return x_8;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Decidable", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
x_9 = lean_name_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lambda__1(x_6, x_7, x_2, x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_erasedExpr;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
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
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_headBeta(x_1);
x_6 = l_Lean_Expr_isErased(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
x_7 = l_Lean_Compiler_LCNF_isTypeFormerType(x_5);
if (x_7 == 0)
{
switch (lean_obj_tag(x_5)) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Compiler_LCNF_toMonoType(x_17, x_2, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_erasedExpr;
x_23 = lean_expr_instantiate1(x_18, x_22);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Compiler_LCNF_toMonoType(x_23, x_2, x_3, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_mkArrow(x_20, x_25, x_2, x_3, x_26);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = l_Lean_Compiler_LCNF_erasedExpr;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = l_Lean_Compiler_LCNF_erasedExpr;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_40 = l_Lean_Compiler_LCNF_erasedExpr;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_MonoTypeExtState_mono___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__4(x_3, x_1, x_2);
return x_4;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState;
x_11 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
x_12 = l_Lean_EnvExtension_getState___rarg(x_10, x_11, x_9);
lean_dec(x_9);
lean_inc(x_1);
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__1(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
x_14 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_14, x_2, x_3, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Compiler_LCNF_toMonoType(x_16, x_2, x_3, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_3, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 4);
lean_dec(x_26);
lean_inc(x_19);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lambda__1), 3, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_19);
x_28 = l_Lean_EnvExtension_modifyState___rarg(x_11, x_25, x_27);
x_29 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2;
lean_ctor_set(x_22, 4, x_29);
lean_ctor_set(x_22, 0, x_28);
x_30 = lean_st_ref_set(x_3, x_22, x_23);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
x_37 = lean_ctor_get(x_22, 2);
x_38 = lean_ctor_get(x_22, 3);
x_39 = lean_ctor_get(x_22, 5);
x_40 = lean_ctor_get(x_22, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
lean_inc(x_19);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lambda__1), 3, 2);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_19);
x_42 = l_Lean_EnvExtension_modifyState___rarg(x_11, x_35, x_41);
x_43 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2;
x_44 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_39);
lean_ctor_set(x_44, 6, x_40);
x_45 = lean_st_ref_set(x_3, x_44, x_23);
lean_dec(x_3);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_5);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState;
x_62 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1;
x_63 = l_Lean_EnvExtension_getState___rarg(x_61, x_62, x_60);
lean_dec(x_60);
lean_inc(x_1);
x_64 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_getOtherDeclBaseType___spec__1(x_63, x_1);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_66 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_65, x_2, x_3, x_59);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_3);
x_69 = l_Lean_Compiler_LCNF_toMonoType(x_67, x_2, x_3, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_take(x_3, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 lean_ctor_release(x_73, 6);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
lean_inc(x_70);
x_82 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getOtherDeclMonoType___lambda__1), 3, 2);
lean_closure_set(x_82, 0, x_1);
lean_closure_set(x_82, 1, x_70);
x_83 = l_Lean_EnvExtension_modifyState___rarg(x_62, x_75, x_82);
x_84 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2;
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 7, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_77);
lean_ctor_set(x_85, 3, x_78);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_79);
lean_ctor_set(x_85, 6, x_80);
x_86 = lean_st_ref_set(x_3, x_85, x_74);
lean_dec(x_3);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_92 = x_69;
} else {
 lean_dec_ref(x_69);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_66, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_66, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_96 = x_66;
} else {
 lean_dec_ref(x_66);
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
lean_object* x_98; lean_object* x_99; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_64, 0);
lean_inc(x_98);
lean_dec(x_64);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_59);
return x_99;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6);
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
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__31);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__32);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__33);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__1);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__1);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__2);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__3);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__4);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__5);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__6);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__7);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__8);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__9);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__10);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__11);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__12);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__13);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__14);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__15);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__16);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__17);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__18);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__19);
l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20 = _init_l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_472____closed__20);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1 = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__1);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo);
l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_toMonoType_visitApp___spec__2___closed__2);
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
l_Lean_Compiler_LCNF_MonoTypeExtState_mono___default = _init_l_Lean_Compiler_LCNF_MonoTypeExtState_mono___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_MonoTypeExtState_mono___default);
l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState = _init_l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedMonoTypeExtState);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974____closed__1);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1974_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1 = _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__1);
l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2 = _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
