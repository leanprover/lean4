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
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_336_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
static lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo;
uint8_t l_Lean_Compiler_LCNF_isRuntimeBuiltinType(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0;
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructureInfoExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19;
static lean_object* l_Lean_Compiler_LCNF_getParamTypes___closed__0;
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
uint8_t l_Lean_Expr_isErased(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14;
static lean_object* l_Lean_Compiler_LCNF_toMonoType___closed__0;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13;
static lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12;
static uint64_t l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27;
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258____boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1912_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
static lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_30; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_30 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_31);
x_33 = l_Lean_Meta_isProp(x_31, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_37 = l_Lean_Meta_isTypeFormerType(x_31, x_4, x_5, x_6, x_7, x_36);
x_18 = x_37;
goto block_29;
}
else
{
lean_dec(x_31);
x_18 = x_33;
goto block_29;
}
}
else
{
lean_dec(x_31);
x_18 = x_33;
goto block_29;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(x_13);
x_15 = lean_array_push(x_3, x_14);
x_2 = x_10;
x_3 = x_15;
x_8 = x_12;
goto _start;
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = 1;
x_12 = x_21;
x_13 = x_22;
goto block_17;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec_ref(x_18);
x_24 = 0;
x_12 = x_23;
x_13 = x_24;
goto block_17;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
case 1:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
lean_dec(x_9);
x_2 = x_42;
goto _start;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___redArg(x_1, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; uint8_t x_28; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0;
x_27 = lean_array_get_size(x_4);
x_28 = lean_nat_dec_le(x_3, x_11);
if (x_28 == 0)
{
x_13 = x_3;
x_14 = x_27;
goto block_26;
}
else
{
lean_dec(x_3);
x_13 = x_11;
x_14 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = l_Array_toSubarray___redArg(x_4, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2___boxed), 2, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13;
x_22 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14;
x_23 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_22, x_21);
x_24 = l_Std_Iterators_instIteratorMap___redArg(x_21, x_23, x_2, x_18);
x_25 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___redArg(x_24, x_20, x_12, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__6;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__5;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__4;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__3;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__2;
x_6 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__11;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__10;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__9;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__8;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__16;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__17;
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__15;
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__12;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 2;
x_2 = 0;
x_3 = 1;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_6, 0, x_5);
lean_ctor_set_uint8(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, 5, x_4);
lean_ctor_set_uint8(x_6, 6, x_4);
lean_ctor_set_uint8(x_6, 7, x_5);
lean_ctor_set_uint8(x_6, 8, x_4);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_2);
lean_ctor_set_uint8(x_6, 11, x_4);
lean_ctor_set_uint8(x_6, 12, x_4);
lean_ctor_set_uint8(x_6, 13, x_4);
lean_ctor_set_uint8(x_6, 14, x_1);
lean_ctor_set_uint8(x_6, 15, x_4);
lean_ctor_set_uint8(x_6, 16, x_4);
lean_ctor_set_uint8(x_6, 17, x_4);
lean_ctor_set_uint8(x_6, 18, x_4);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__13;
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__22;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__23;
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__25;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__24;
x_6 = lean_box(0);
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__20;
x_9 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__19;
x_10 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_2);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 8, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 9, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 10, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.MonoTypes", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.getRelevantCtorFields", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(19u);
x_4 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__28;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__18;
x_10 = lean_st_mk_ref(x_9, x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
lean_dec_ref(x_8);
x_15 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed), 2, 0);
lean_inc_ref(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___boxed), 10, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_14);
x_18 = 0;
x_19 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__26;
lean_inc(x_12);
x_20 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_15, x_17, x_18, x_18, x_19, x_12, x_2, x_3, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_st_ref_get(x_12, x_22);
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_dec(x_12);
return x_20;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec_ref(x_5);
x_29 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__30;
x_30 = l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(x_29, x_2, x_3, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ctorName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numParams", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_6 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_7 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Name_reprPrec(x_2, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_22 = l_Nat_reprFast(x_3);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_11);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = l_Nat_reprFast(x_4);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_11);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_38 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_11);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_336_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_30; uint8_t x_31; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_20 = x_8;
} else {
 lean_dec_ref(x_8);
 x_20 = lean_box(0);
}
x_30 = lean_array_fget(x_5, x_9);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_20);
lean_inc(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_19);
x_11 = x_32;
x_12 = x_10;
goto block_18;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
x_21 = x_6;
goto block_29;
}
else
{
x_21 = x_31;
goto block_29;
}
}
block_18:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_9);
x_15 = lean_nat_dec_lt(x_14, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
x_8 = x_11;
x_9 = x_14;
x_10 = x_12;
goto _start;
}
}
block_29:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_22);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_9);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_3);
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_11 = x_25;
x_12 = x_10;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_13, x_14, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0() {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; 
x_9 = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*6 + 1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 4);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = x_12;
goto block_8;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_22);
x_24 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_22, x_23, x_2, x_3, x_12);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Expr_isErased(x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_24);
lean_inc(x_22);
x_29 = l_Lean_Compiler_LCNF_getRelevantCtorFields(x_22, x_2, x_3, x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_array_get_size(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_34, x_33);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_22);
lean_dec_ref(x_17);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_29);
x_37 = lean_box(0);
x_38 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0;
x_39 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(x_17, x_22, x_37, x_35, x_31, x_9, x_33, x_38, x_34, x_32);
lean_dec(x_33);
lean_dec(x_31);
lean_dec_ref(x_17);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_40);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_50);
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_29);
x_56 = lean_array_get_size(x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_box(0);
x_59 = lean_nat_dec_lt(x_57, x_56);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_22);
lean_dec_ref(x_17);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_box(0);
x_62 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0;
x_63 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(x_17, x_22, x_61, x_58, x_54, x_9, x_56, x_62, x_57, x_55);
lean_dec(x_56);
lean_dec(x_54);
lean_dec_ref(x_17);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_64);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
lean_dec(x_65);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec_ref(x_17);
x_74 = !lean_is_exclusive(x_29);
if (x_74 == 0)
{
return x_29;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_29, 0);
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_29);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_box(0);
lean_ctor_set(x_24, 0, x_78);
return x_24;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_24, 0);
x_80 = lean_ctor_get(x_24, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_24);
x_81 = l_Lean_Expr_isErased(x_79);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_inc(x_22);
x_82 = l_Lean_Compiler_LCNF_getRelevantCtorFields(x_22, x_2, x_3, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_array_get_size(x_83);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_box(0);
x_89 = lean_nat_dec_lt(x_87, x_86);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_22);
lean_dec_ref(x_17);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_85);
x_91 = lean_box(0);
x_92 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0;
x_93 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(x_17, x_22, x_91, x_88, x_83, x_9, x_86, x_92, x_87, x_84);
lean_dec(x_86);
lean_dec(x_83);
lean_dec_ref(x_17);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_102);
lean_dec(x_95);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_22);
lean_dec_ref(x_17);
x_104 = lean_ctor_get(x_82, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_106 = x_82;
} else {
 lean_dec_ref(x_82);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_80);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_24);
if (x_110 == 0)
{
return x_24;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_24, 0);
x_112 = lean_ctor_get(x_24, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_24);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = x_12;
goto block_8;
}
}
}
else
{
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_16;
}
}
else
{
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_16;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_12);
return x_115;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_13;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_116; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_116 = !lean_is_exclusive(x_10);
if (x_116 == 0)
{
return x_10;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_10, 0);
x_118 = lean_ctor_get(x_10, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_10);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
return x_121;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
x_12 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_6);
x_21 = lean_unbox(x_7);
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache_spec__0(x_1, x_2, x_3, x_4, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_22;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_trivialStructureInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0;
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(x_5, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(x_5, x_1, x_10, x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_array_push(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getParamTypes___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_getParamTypes___closed__0;
x_3 = l_Lean_Compiler_LCNF_getParamTypes_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.toMonoType.visitApp", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__29;
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_unsigned_to_nat(113u);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1;
x_5 = l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__27;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_19 = x_5;
} else {
 lean_dec_ref(x_5);
 x_19 = lean_box(0);
}
lean_inc(x_18);
x_20 = l_Lean_Expr_headBeta(x_18);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_20);
x_23 = lean_array_uget(x_2, x_4);
x_24 = l_Lean_Expr_headBeta(x_23);
switch (lean_obj_tag(x_21)) {
case 3:
{
lean_dec_ref(x_21);
goto block_38;
}
case 4:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec_ref(x_21);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_45);
lean_dec(x_43);
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec_ref(x_45);
if (x_47 == 0)
{
x_39 = x_1;
goto block_42;
}
else
{
goto block_38;
}
}
else
{
lean_dec(x_44);
lean_dec(x_43);
x_39 = x_1;
goto block_42;
}
}
else
{
lean_dec(x_43);
x_39 = x_1;
goto block_42;
}
}
default: 
{
lean_dec_ref(x_21);
x_39 = x_1;
goto block_42;
}
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_expr_instantiate1(x_22, x_24);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
if (lean_is_scalar(x_19)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_19;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_9 = x_28;
x_10 = x_26;
goto block_14;
}
block_38:
{
lean_object* x_30; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
x_30 = l_Lean_Compiler_LCNF_toMonoType(x_24, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Expr_app___override(x_17, x_31);
x_25 = x_33;
x_26 = x_32;
goto block_29;
}
else
{
uint8_t x_34; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
block_42:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Compiler_LCNF_anyExpr;
x_41 = l_Lean_Expr_app___override(x_17, x_40);
x_25 = x_41;
x_26 = x_8;
goto block_29;
}
else
{
goto block_38;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_20);
x_48 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2;
lean_inc(x_7);
lean_inc_ref(x_6);
x_49 = l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(x_48, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_18);
x_9 = x_51;
x_10 = x_50;
goto block_14;
}
else
{
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_9;
x_8 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcAny", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_6, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_92);
x_93 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
x_94 = lean_string_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0;
x_96 = lean_string_dec_eq(x_92, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1;
x_98 = lean_string_dec_eq(x_92, x_97);
lean_dec_ref(x_92);
if (x_98 == 0)
{
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_90;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_99 = l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_5);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_92);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_101 = l_Lean_Compiler_LCNF_anyExpr;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_5);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_92);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_103 = l_Lean_Compiler_LCNF_erasedExpr;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_5);
return x_104;
}
}
else
{
lean_dec(x_91);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_90;
}
}
else
{
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
goto block_90;
}
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Array_toSubarray___redArg(x_2, x_14, x_15);
x_17 = l_Array_ofSubarray___redArg(x_16);
x_18 = l_Lean_Compiler_LCNF_instantiateForall(x_11, x_17, x_9, x_10, x_13);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_Compiler_LCNF_getParamTypes(x_19);
x_22 = lean_array_get(x_8, x_21, x_12);
lean_dec(x_12);
lean_dec_ref(x_21);
x_23 = l_Lean_Compiler_LCNF_toMonoType(x_22, x_9, x_10, x_20);
return x_23;
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_18;
}
}
block_90:
{
lean_object* x_28; 
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_6);
x_28 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_6, x_25, x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_6);
x_31 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_6, x_7, x_25, x_26, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Expr_isErased(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
lean_free_object(x_31);
x_36 = lean_box(0);
x_37 = l_Lean_Expr_const___override(x_6, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_array_size(x_2);
x_40 = 0;
x_41 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(x_35, x_2, x_39, x_40, x_38, x_25, x_26, x_34);
lean_dec_ref(x_2);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_6);
lean_dec_ref(x_2);
x_53 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_31, 0, x_53);
return x_31;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = l_Lean_Expr_isErased(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_57 = lean_box(0);
x_58 = l_Lean_Expr_const___override(x_6, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
x_60 = lean_array_size(x_2);
x_61 = 0;
x_62 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(x_56, x_2, x_60, x_61, x_59, x_25, x_26, x_55);
lean_dec_ref(x_2);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_54);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_6);
lean_dec_ref(x_2);
x_72 = l_Lean_Compiler_LCNF_erasedExpr;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_55);
return x_73;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_31;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_7);
lean_dec(x_6);
x_74 = lean_ctor_get(x_29, 0);
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_ctor_get(x_28, 1);
lean_inc(x_75);
lean_dec_ref(x_28);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
lean_inc(x_26);
lean_inc_ref(x_25);
x_80 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_76, x_79, x_25, x_26, x_75);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get_size(x_2);
x_85 = lean_nat_dec_le(x_77, x_84);
if (x_85 == 0)
{
lean_dec(x_77);
x_9 = x_25;
x_10 = x_26;
x_11 = x_81;
x_12 = x_78;
x_13 = x_82;
x_14 = x_83;
x_15 = x_84;
goto block_24;
}
else
{
lean_dec(x_84);
x_9 = x_25;
x_10 = x_26;
x_11 = x_81;
x_12 = x_78;
x_13 = x_82;
x_14 = x_83;
x_15 = x_77;
goto block_24;
}
}
else
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
return x_80;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_86 = !lean_is_exclusive(x_28);
if (x_86 == 0)
{
return x_28;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_28, 0);
x_88 = lean_ctor_get(x_28, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_28);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = l_Lean_Compiler_LCNF_anyExpr;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_5);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
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
static lean_object* _init_l_Lean_Compiler_LCNF_toMonoType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
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
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = l_Lean_Compiler_LCNF_erasedExpr;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_getParamTypes___closed__0;
x_9 = l_Lean_Compiler_LCNF_toMonoType_visitApp(x_5, x_8, x_2, x_3, x_4);
return x_9;
}
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Compiler_LCNF_toMonoType___closed__0;
x_11 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(x_5, x_12, x_14, x_2, x_3, x_4);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_5);
x_18 = l_Lean_Compiler_LCNF_anyExpr;
x_19 = lean_expr_instantiate1(x_17, x_18);
lean_dec_ref(x_17);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Lean_Compiler_LCNF_toMonoType(x_19, x_2, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
lean_dec(x_31);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
x_35 = lean_string_dec_eq(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_free_object(x_20);
x_24 = x_2;
x_25 = x_3;
goto block_30;
}
else
{
lean_object* x_36; 
lean_dec(x_22);
lean_dec_ref(x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
x_36 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_20, 0, x_36);
return x_20;
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_free_object(x_20);
x_24 = x_2;
x_25 = x_3;
goto block_30;
}
}
else
{
lean_dec(x_31);
lean_free_object(x_20);
x_24 = x_2;
x_25 = x_3;
goto block_30;
}
}
else
{
lean_free_object(x_20);
x_24 = x_2;
x_25 = x_3;
goto block_30;
}
block_30:
{
lean_object* x_26; 
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_toMonoType(x_16, x_24, x_25, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_mkArrow___redArg(x_27, x_22, x_25, x_28);
lean_dec(x_25);
return x_29;
}
else
{
lean_dec(x_25);
lean_dec(x_22);
return x_26;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
if (lean_obj_tag(x_37) == 4)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
lean_dec(x_46);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0;
x_50 = lean_string_dec_eq(x_48, x_49);
lean_dec_ref(x_48);
if (x_50 == 0)
{
x_39 = x_2;
x_40 = x_3;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_dec_ref(x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = l_Lean_Compiler_LCNF_erasedExpr;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
}
else
{
lean_dec(x_47);
lean_dec(x_46);
x_39 = x_2;
x_40 = x_3;
goto block_45;
}
}
else
{
lean_dec(x_46);
x_39 = x_2;
x_40 = x_3;
goto block_45;
}
}
else
{
x_39 = x_2;
x_40 = x_3;
goto block_45;
}
block_45:
{
lean_object* x_41; 
lean_inc(x_40);
x_41 = l_Lean_Compiler_LCNF_toMonoType(x_16, x_39, x_40, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_mkArrow___redArg(x_42, x_37, x_40, x_43);
lean_dec(x_40);
return x_44;
}
else
{
lean_dec(x_40);
lean_dec(x_37);
return x_41;
}
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
case 10:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_5, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_54);
lean_dec_ref(x_5);
x_55 = l_Lean_Compiler_LCNF_toMonoType(x_54, x_2, x_3, x_4);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_mdata___override(x_53, x_57);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = l_Lean_Expr_mdata___override(x_53, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_dec(x_53);
return x_55;
}
}
default: 
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = l_Lean_Compiler_LCNF_anyExpr;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1912_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0() {
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
x_5 = l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0;
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(x_5, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_9, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_3);
x_13 = l_Lean_Compiler_LCNF_toMonoType(x_11, x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_14);
x_16 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___redArg(x_5, x_1, x_14, x_3, x_15);
lean_dec(x_3);
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
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
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
l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1___closed__0);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__0);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__1);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__2);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__3);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__4);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__5);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__6);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__7);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__8);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__9);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__10);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__11);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__12);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__13);
l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__1___closed__14);
l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0 = _init_l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getRelevantCtorFields___closed__0);
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
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0 = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo___closed__0);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__0____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__1____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__2____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__3____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__4____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__5____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__6____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__7____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__8____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__9____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__10____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__11____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__12____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__13____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__14____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__15____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__16____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__17____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_ = _init_l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_();
lean_mark_persistent(l_Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg___closed__18____x40_Lean_Compiler_LCNF_MonoTypes___hyg_258_);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0 = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo___closed__0);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_336_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_trivialStructureInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_trivialStructureInfoExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0 = _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_hasTrivialStructure_x3f_fillCache___closed__0);
l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_hasTrivialStructure_x3f___closed__0);
l_Lean_Compiler_LCNF_getParamTypes___closed__0 = _init_l_Lean_Compiler_LCNF_getParamTypes___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getParamTypes___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1___closed__2);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__0);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__1);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__2);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__3);
l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4 = _init_l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType_visitApp___closed__4);
l_Lean_Compiler_LCNF_toMonoType___closed__0 = _init_l_Lean_Compiler_LCNF_toMonoType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_toMonoType___closed__0);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1912_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0 = _init_l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclMonoType___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
