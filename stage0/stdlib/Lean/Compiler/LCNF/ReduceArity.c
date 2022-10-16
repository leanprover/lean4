// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Internalize
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2744_(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1;
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2;
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__3;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_State_used___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_FindUsed_State_used___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_16, x_1, x_18);
x_20 = lean_st_ref_set(x_3, x_19, x_17);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_15, x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_16, x_25);
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_26);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_Expr_isFVarOf(x_24, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_11 = x_30;
goto _start;
}
else
{
size_t x_34; size_t x_35; 
lean_dec(x_24);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_4);
x_37 = lean_array_fget(x_15, x_16);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_16, x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_17);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = l_Lean_Expr_isFVarOf(x_37, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_43 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
x_4 = x_40;
x_11 = x_44;
goto _start;
}
else
{
size_t x_48; size_t x_49; 
lean_dec(x_37);
x_48 = 1;
x_49 = lean_usize_add(x_3, x_48);
x_3 = x_49;
x_4 = x_40;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_14, x_3);
x_16 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_box(0);
x_3 = x_19;
x_4 = x_20;
x_11 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_11 = x_18;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = l_Lean_Expr_getAppFn(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = l_Lean_Expr_isConstOf(x_11, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_array_get_size(x_18);
x_27 = lean_nat_dec_lt(x_12, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_22);
x_31 = 0;
x_32 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(x_18, x_31, x_32, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_array_get_size(x_18);
x_37 = lean_nat_dec_lt(x_12, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_36, x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_45 = lean_box(0);
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(x_18, x_43, x_44, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; lean_object* x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; lean_object* x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_11);
x_47 = lean_array_get_size(x_18);
lean_inc(x_47);
lean_inc(x_18);
x_48 = l_Array_toSubarray___rarg(x_18, x_12, x_47);
x_49 = lean_ctor_get(x_19, 3);
lean_inc(x_49);
lean_dec(x_19);
x_50 = lean_array_get_size(x_49);
x_51 = lean_usize_of_nat(x_50);
x_52 = 0;
x_53 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2(x_49, x_51, x_52, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_array_get_size(x_18);
x_57 = l_Array_toSubarray___rarg(x_18, x_55, x_56);
x_58 = lean_ctor_get(x_57, 2);
lean_inc(x_58);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3(x_57, x_59, x_61, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
lean_dec(x_57);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Array_toSubarray___rarg(x_49, x_47, x_50);
x_66 = lean_ctor_get(x_65, 2);
lean_inc(x_66);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4(x_65, x_67, x_69, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_62);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 10:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_dec(x_1);
x_1 = x_75;
goto _start;
}
case 11:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_77);
lean_dec(x_1);
x_1 = x_77;
goto _start;
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_8);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = l_Lean_Compiler_LCNF_AltCore_getCode(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_FindUsed_visit(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_FindUsed_visitExpr(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_10;
x_8 = x_13;
goto _start;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_16, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitExpr___spec__1(x_15, x_24, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
return x_27;
}
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
x_30 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_array_get_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_30, 0, x_38);
return x_30;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_35);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
lean_ctor_set(x_30, 0, x_40);
return x_30;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_30);
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(x_34, x_41, x_42, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_34);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_ctor_get(x_28, 3);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_array_get_size(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_47, x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = lean_box(0);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(x_46, x_55, x_56, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_46);
return x_58;
}
}
}
}
case 5:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_60;
}
case 6:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_8);
return x_62;
}
default: 
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_ctor_get(x_63, 4);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Compiler_LCNF_FindUsed_visit(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_1 = x_64;
x_8 = x_67;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_st_ref_get(x_5, x_6);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
x_14 = x_7;
goto block_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_9, x_9);
if (x_30 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
x_14 = x_7;
goto block_29;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(x_8, x_31, x_32, x_7);
lean_dec(x_8);
x_14 = x_33;
goto block_29;
}
}
block_29:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_st_mk_ref(x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_18);
x_20 = l_Lean_Compiler_LCNF_FindUsed_visit(x_12, x_16, x_18, x_2, x_3, x_4, x_5, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_5, x_21);
lean_dec(x_5);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_18, x_23);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_16, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_array_fget(x_18, x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_19, x_28);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_29);
if (x_14 == 0)
{
size_t x_30; size_t x_31; 
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; 
x_33 = lean_array_push(x_17, x_27);
lean_ctor_set(x_4, 1, x_33);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
x_37 = lean_array_fget(x_18, x_19);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_19, x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_20);
if (x_14 == 0)
{
size_t x_41; size_t x_42; 
lean_dec(x_37);
lean_ctor_set(x_4, 0, x_40);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; 
x_44 = lean_array_push(x_17, x_37);
lean_ctor_set(x_4, 1, x_44);
lean_ctor_set(x_4, 0, x_40);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
goto _start;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 2);
lean_inc(x_52);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
x_57 = lean_array_fget(x_50, x_51);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_51, x_58);
lean_dec(x_51);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_52);
if (x_14 == 0)
{
lean_object* x_61; size_t x_62; size_t x_63; 
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
x_62 = 1;
x_63 = lean_usize_add(x_3, x_62);
x_3 = x_63;
x_4 = x_61;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_65 = lean_array_push(x_49, x_57);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
x_67 = 1;
x_68 = lean_usize_add(x_3, x_67);
x_3 = x_68;
x_4 = x_66;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__3(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_9 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l_Lean_Expr_isAppOf(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_inc(x_9);
x_13 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_17 = lean_ptr_addr(x_15);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
size_t x_23; uint8_t x_24; 
x_23 = lean_ptr_addr(x_8);
x_24 = lean_usize_dec_eq(x_23, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_dec(x_15);
lean_dec(x_8);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_32 = lean_ptr_addr(x_29);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_34 = x_1;
} else {
 lean_dec_ref(x_1);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; uint8_t x_38; 
x_37 = lean_ptr_addr(x_8);
x_38 = lean_usize_dec_eq(x_37, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_8);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_47);
x_49 = l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1;
lean_inc(x_48);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_53 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_50, x_52);
x_54 = lean_array_get_size(x_53);
x_55 = l_Array_toSubarray___rarg(x_53, x_47, x_54);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_get_size(x_56);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
x_62 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(x_56, x_60, x_61, x_58, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_56);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_box(0);
x_68 = l_Lean_Expr_const___override(x_66, x_67);
x_69 = l_Lean_mkAppN(x_68, x_65);
lean_inc(x_8);
x_70 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_8, x_69, x_3, x_4, x_5, x_6, x_64);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_9);
x_73 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_9, x_2, x_3, x_4, x_5, x_6, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; size_t x_76; size_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_77 = lean_ptr_addr(x_75);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_1, 0);
lean_dec(x_81);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_71);
lean_ctor_set(x_73, 0, x_1);
return x_73;
}
else
{
lean_object* x_82; 
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_73, 0, x_82);
return x_73;
}
}
else
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_84 = lean_ptr_addr(x_71);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_1, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_1, 0);
lean_dec(x_88);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_71);
lean_ctor_set(x_73, 0, x_1);
return x_73;
}
else
{
lean_object* x_89; 
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_71);
lean_ctor_set(x_89, 1, x_75);
lean_ctor_set(x_73, 0, x_89);
return x_73;
}
}
else
{
lean_dec(x_75);
lean_dec(x_71);
lean_ctor_set(x_73, 0, x_1);
return x_73;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; size_t x_92; size_t x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_73, 0);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_73);
x_92 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_93 = lean_ptr_addr(x_90);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_95 = x_1;
} else {
 lean_dec_ref(x_1);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_71);
lean_ctor_set(x_96, 1, x_90);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
return x_97;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_99 = lean_ptr_addr(x_71);
x_100 = lean_usize_dec_eq(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_101 = x_1;
} else {
 lean_dec_ref(x_1);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_71);
lean_ctor_set(x_102, 1, x_90);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_91);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_90);
lean_dec(x_71);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_91);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_71);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_73);
if (x_105 == 0)
{
return x_73;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_73, 0);
x_107 = lean_ctor_get(x_73, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_73);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
case 1:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 4);
lean_inc(x_111);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_112 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_111, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_109, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 2);
lean_inc(x_116);
lean_inc(x_109);
x_117 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_109, x_115, x_116, x_113, x_3, x_4, x_5, x_6, x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_110);
x_120 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_110, x_2, x_3, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; size_t x_123; size_t x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ptr_addr(x_110);
lean_dec(x_110);
x_124 = lean_ptr_addr(x_122);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
uint8_t x_126; 
lean_dec(x_109);
x_126 = !lean_is_exclusive(x_1);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_1, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_1, 0);
lean_dec(x_128);
lean_ctor_set(x_1, 1, x_122);
lean_ctor_set(x_1, 0, x_118);
lean_ctor_set(x_120, 0, x_1);
return x_120;
}
else
{
lean_object* x_129; 
lean_dec(x_1);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_122);
lean_ctor_set(x_120, 0, x_129);
return x_120;
}
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_109);
lean_dec(x_109);
x_131 = lean_ptr_addr(x_118);
x_132 = lean_usize_dec_eq(x_130, x_131);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_1);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_1, 1);
lean_dec(x_134);
x_135 = lean_ctor_get(x_1, 0);
lean_dec(x_135);
lean_ctor_set(x_1, 1, x_122);
lean_ctor_set(x_1, 0, x_118);
lean_ctor_set(x_120, 0, x_1);
return x_120;
}
else
{
lean_object* x_136; 
lean_dec(x_1);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_122);
lean_ctor_set(x_120, 0, x_136);
return x_120;
}
}
else
{
lean_dec(x_122);
lean_dec(x_118);
lean_ctor_set(x_120, 0, x_1);
return x_120;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; size_t x_139; size_t x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_120, 0);
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_120);
x_139 = lean_ptr_addr(x_110);
lean_dec(x_110);
x_140 = lean_ptr_addr(x_137);
x_141 = lean_usize_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_109);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_142 = x_1;
} else {
 lean_dec_ref(x_1);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_118);
lean_ctor_set(x_143, 1, x_137);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
else
{
size_t x_145; size_t x_146; uint8_t x_147; 
x_145 = lean_ptr_addr(x_109);
lean_dec(x_109);
x_146 = lean_ptr_addr(x_118);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_148 = x_1;
} else {
 lean_dec_ref(x_1);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_118);
lean_ctor_set(x_149, 1, x_137);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_138);
return x_150;
}
else
{
lean_object* x_151; 
lean_dec(x_137);
lean_dec(x_118);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_138);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_118);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_120);
if (x_152 == 0)
{
return x_120;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_120, 0);
x_154 = lean_ctor_get(x_120, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_120);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_112);
if (x_156 == 0)
{
return x_112;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_112, 0);
x_158 = lean_ctor_get(x_112, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_112);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
case 2:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 4);
lean_inc(x_162);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_163 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_162, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_160, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 2);
lean_inc(x_167);
lean_inc(x_160);
x_168 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_160, x_166, x_167, x_164, x_3, x_4, x_5, x_6, x_165);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_161);
x_171 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_161, x_2, x_3, x_4, x_5, x_6, x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; size_t x_174; size_t x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_175 = lean_ptr_addr(x_173);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
uint8_t x_177; 
lean_dec(x_160);
x_177 = !lean_is_exclusive(x_1);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_1, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_1, 0);
lean_dec(x_179);
lean_ctor_set(x_1, 1, x_173);
lean_ctor_set(x_1, 0, x_169);
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
else
{
lean_object* x_180; 
lean_dec(x_1);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_169);
lean_ctor_set(x_180, 1, x_173);
lean_ctor_set(x_171, 0, x_180);
return x_171;
}
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_182 = lean_ptr_addr(x_169);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_1);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_1, 1);
lean_dec(x_185);
x_186 = lean_ctor_get(x_1, 0);
lean_dec(x_186);
lean_ctor_set(x_1, 1, x_173);
lean_ctor_set(x_1, 0, x_169);
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
else
{
lean_object* x_187; 
lean_dec(x_1);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_169);
lean_ctor_set(x_187, 1, x_173);
lean_ctor_set(x_171, 0, x_187);
return x_171;
}
}
else
{
lean_dec(x_173);
lean_dec(x_169);
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; size_t x_190; size_t x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_171, 0);
x_189 = lean_ctor_get(x_171, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_171);
x_190 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_191 = lean_ptr_addr(x_188);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_160);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_193 = x_1;
} else {
 lean_dec_ref(x_1);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(2, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_169);
lean_ctor_set(x_194, 1, x_188);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_189);
return x_195;
}
else
{
size_t x_196; size_t x_197; uint8_t x_198; 
x_196 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_197 = lean_ptr_addr(x_169);
x_198 = lean_usize_dec_eq(x_196, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_199 = x_1;
} else {
 lean_dec_ref(x_1);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(2, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_169);
lean_ctor_set(x_200, 1, x_188);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_189);
return x_201;
}
else
{
lean_object* x_202; 
lean_dec(x_188);
lean_dec(x_169);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_1);
lean_ctor_set(x_202, 1, x_189);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_169);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_171);
if (x_203 == 0)
{
return x_171;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_171, 0);
x_205 = lean_ctor_get(x_171, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_171);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_163);
if (x_207 == 0)
{
return x_163;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_163, 0);
x_209 = lean_ctor_get(x_163, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_163);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 4:
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_1, 0);
lean_inc(x_211);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = lean_ctor_get(x_211, 2);
x_216 = lean_ctor_get(x_211, 3);
x_217 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
lean_inc(x_216);
x_218 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(x_216, x_217, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; size_t x_221; size_t x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_222 = lean_ptr_addr(x_220);
x_223 = lean_usize_dec_eq(x_221, x_222);
if (x_223 == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_1);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_1, 0);
lean_dec(x_225);
lean_ctor_set(x_211, 3, x_220);
lean_ctor_set(x_218, 0, x_1);
return x_218;
}
else
{
lean_object* x_226; 
lean_dec(x_1);
lean_ctor_set(x_211, 3, x_220);
x_226 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_226, 0, x_211);
lean_ctor_set(x_218, 0, x_226);
return x_218;
}
}
else
{
lean_dec(x_220);
lean_free_object(x_211);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_ctor_set(x_218, 0, x_1);
return x_218;
}
}
else
{
lean_object* x_227; lean_object* x_228; size_t x_229; size_t x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_218, 0);
x_228 = lean_ctor_get(x_218, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_218);
x_229 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_230 = lean_ptr_addr(x_227);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_232 = x_1;
} else {
 lean_dec_ref(x_1);
 x_232 = lean_box(0);
}
lean_ctor_set(x_211, 3, x_227);
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(4, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_211);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_228);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_227);
lean_free_object(x_211);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_228);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_free_object(x_211);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_218);
if (x_236 == 0)
{
return x_218;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_218, 0);
x_238 = lean_ctor_get(x_218, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_218);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_211, 0);
x_241 = lean_ctor_get(x_211, 1);
x_242 = lean_ctor_get(x_211, 2);
x_243 = lean_ctor_get(x_211, 3);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_211);
x_244 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
lean_inc(x_243);
x_245 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(x_243, x_244, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; size_t x_249; size_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
x_249 = lean_ptr_addr(x_243);
lean_dec(x_243);
x_250 = lean_ptr_addr(x_246);
x_251 = lean_usize_dec_eq(x_249, x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_252 = x_1;
} else {
 lean_dec_ref(x_1);
 x_252 = lean_box(0);
}
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_240);
lean_ctor_set(x_253, 1, x_241);
lean_ctor_set(x_253, 2, x_242);
lean_ctor_set(x_253, 3, x_246);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(4, 1, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_248)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_248;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_247);
return x_255;
}
else
{
lean_object* x_256; 
lean_dec(x_246);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
if (lean_is_scalar(x_248)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_248;
}
lean_ctor_set(x_256, 0, x_1);
lean_ctor_set(x_256, 1, x_247);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_1);
x_257 = lean_ctor_get(x_245, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_245, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_259 = x_245;
} else {
 lean_dec_ref(x_245);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
default: 
{
lean_object* x_261; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_1);
lean_ctor_set(x_261, 1, x_7);
return x_261;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_4, 2);
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_16, x_18, x_1);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_array_uset(x_9, x_4, x_15);
x_4 = x_12;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_array_uset(x_9, x_4, x_19);
x_4 = x_12;
x_5 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_array_uset(x_8, x_3, x_14);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_array_uset(x_8, x_3, x_18);
x_3 = x_11;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_16, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_array_fget(x_18, x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_19, x_28);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_29);
if (x_14 == 0)
{
size_t x_30; size_t x_31; 
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_33 = l_Lean_Compiler_LCNF_Param_toExpr(x_27);
x_34 = lean_array_push(x_17, x_33);
lean_ctor_set(x_4, 1, x_34);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
x_38 = lean_array_fget(x_18, x_19);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_19, x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_20);
if (x_14 == 0)
{
size_t x_42; size_t x_43; 
lean_dec(x_38);
lean_ctor_set(x_4, 0, x_41);
x_42 = 1;
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_45 = l_Lean_Compiler_LCNF_Param_toExpr(x_38);
x_46 = lean_array_push(x_17, x_45);
lean_ctor_set(x_4, 1, x_46);
lean_ctor_set(x_4, 0, x_41);
x_47 = 1;
x_48 = lean_usize_add(x_3, x_47);
x_3 = x_48;
goto _start;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_4);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 2);
lean_inc(x_54);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
 x_58 = lean_box(0);
}
x_59 = lean_array_fget(x_52, x_53);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_53, x_60);
lean_dec(x_53);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_54);
if (x_14 == 0)
{
lean_object* x_63; size_t x_64; size_t x_65; 
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_51);
x_64 = 1;
x_65 = lean_usize_add(x_3, x_64);
x_3 = x_65;
x_4 = x_63;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; 
x_67 = l_Lean_Compiler_LCNF_Param_toExpr(x_59);
x_68 = lean_array_push(x_51, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
x_70 = 1;
x_71 = lean_usize_add(x_3, x_70);
x_3 = x_71;
x_4 = x_69;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_6, x_8);
x_4 = x_11;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_array_push(x_6, x_8);
x_4 = x_11;
x_6 = x_14;
goto _start;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_13;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_fvar___override(x_5);
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
x_11 = l_Lean_Expr_fvar___override(x_9);
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
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3;
x_3 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4;
x_4 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_18);
x_20 = lean_ctor_get(x_5, 2);
x_21 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_st_ref_take(x_6, x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_30 = 0;
x_31 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_PersistentArray_push___rarg(x_28, x_32);
lean_ctor_set(x_25, 3, x_33);
x_34 = lean_st_ref_set(x_6, x_25, x_26);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_49 = 0;
x_50 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc(x_8);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_PersistentArray_push___rarg(x_44, x_51);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
x_54 = lean_st_ref_set(x_6, x_53, x_26);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_redArg", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_usize_of_nat(x_1);
x_18 = 0;
lean_inc(x_3);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3(x_2, x_17, x_18, x_3);
x_20 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2;
x_21 = l_Lean_Name_append(x_4, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_1);
lean_inc(x_19);
lean_inc(x_21);
lean_inc(x_4);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_25 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_5, x_24, x_12, x_13, x_14, x_15, x_16);
if (x_23 == 0)
{
lean_object* x_111; 
x_111 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_26 = x_111;
goto block_110;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_1, x_1);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_26 = x_113;
goto block_110;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_115 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(x_2, x_3, x_18, x_17, x_114);
x_26 = x_115;
goto block_110;
}
}
block_110:
{
lean_object* x_27; 
if (x_23 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_27 = x_105;
goto block_104;
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_1, x_1);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_27 = x_107;
goto block_104;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_109 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(x_2, x_3, x_18, x_17, x_108);
x_27 = x_109;
goto block_104;
}
}
block_104:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_28);
x_30 = l_Lean_Compiler_LCNF_Code_inferType(x_28, x_12, x_13, x_14, x_15, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_26);
x_33 = l_Lean_Compiler_LCNF_mkForallParams(x_26, x_31, x_12, x_13, x_14, x_15, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
lean_inc(x_21);
x_37 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_26);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_8);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 1, x_7);
lean_inc(x_37);
x_38 = l_Lean_Compiler_LCNF_Decl_saveMono(x_37, x_14, x_15, x_35);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_get(x_15, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3;
x_43 = lean_st_mk_ref(x_42, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_17, x_18, x_3, x_44, x_12, x_13, x_14, x_15, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_get_size(x_47);
lean_inc(x_47);
x_50 = l_Array_toSubarray___rarg(x_47, x_22, x_49);
x_51 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_get_size(x_19);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(x_19, x_54, x_18, x_52, x_44, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_19);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_const___override(x_21, x_36);
x_60 = l_Lean_mkAppN(x_59, x_58);
x_61 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_62 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_60, x_61, x_12, x_13, x_14, x_15, x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = 0;
x_69 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6;
x_70 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_9);
lean_ctor_set(x_70, 2, x_10);
lean_ctor_set(x_70, 3, x_47);
lean_ctor_set(x_70, 4, x_67);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*6 + 1, x_7);
lean_inc(x_70);
x_71 = l_Lean_Compiler_LCNF_Decl_saveMono(x_70, x_14, x_15, x_64);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_get(x_15, x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_get(x_44, x_74);
lean_dec(x_44);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Compiler_LCNF_eraseParams(x_27, x_12, x_13, x_14, x_15, x_76);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_27);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
x_81 = lean_array_push(x_80, x_37);
x_82 = lean_array_push(x_81, x_70);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
x_85 = lean_array_push(x_84, x_37);
x_86 = lean_array_push(x_85, x_70);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_62, 0);
x_90 = lean_ctor_get(x_62, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_62);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_33);
if (x_92 == 0)
{
return x_33;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_33, 0);
x_94 = lean_ctor_get(x_33, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_33);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_30);
if (x_96 == 0)
{
return x_30;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_30, 0);
x_98 = lean_ctor_get(x_30, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_30);
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
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_25);
if (x_100 == 0)
{
return x_25;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_25, 0);
x_102 = lean_ctor_get(x_25, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_25);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceArity", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", used params: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(x_11, x_9);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_20 = lean_ctor_get(x_1, 5);
lean_inc(x_20);
x_21 = lean_array_get_size(x_16);
x_22 = lean_nat_dec_eq(x_12, x_21);
lean_dec(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_7);
lean_dec(x_1);
x_23 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(x_23, x_2, x_3, x_4, x_5, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(x_21, x_9, x_16, x_13, x_17, x_18, x_19, x_20, x_14, x_15, x_28, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_9);
lean_dec(x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
lean_inc(x_13);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_13);
x_32 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_9);
x_36 = l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(x_9);
x_37 = lean_box(0);
x_38 = l_List_mapTRAux___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(x_36, x_37);
x_39 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_38, x_37);
x_40 = l_Lean_MessageData_ofList(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
x_43 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(x_23, x_42, x_2, x_3, x_4, x_5, x_30);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(x_21, x_9, x_16, x_13, x_17, x_18, x_19, x_20, x_14, x_15, x_44, x_2, x_3, x_4, x_5, x_45);
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_21);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
x_48 = lean_array_push(x_47, x_1);
lean_ctor_set(x_7, 0, x_48);
return x_7;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(x_51, x_49);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 4);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_60 = lean_ctor_get(x_1, 5);
lean_inc(x_60);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_eq(x_52, x_61);
lean_dec(x_52);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_1);
x_63 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_64 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(x_63, x_2, x_3, x_4, x_5, x_50);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(x_61, x_49, x_56, x_53, x_57, x_58, x_59, x_60, x_54, x_55, x_68, x_2, x_3, x_4, x_5, x_67);
lean_dec(x_49);
lean_dec(x_61);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
lean_inc(x_53);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_53);
x_72 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_49);
x_76 = l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(x_49);
x_77 = lean_box(0);
x_78 = l_List_mapTRAux___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(x_76, x_77);
x_79 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_78, x_77);
x_80 = l_Lean_MessageData_ofList(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
x_83 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(x_63, x_82, x_2, x_3, x_4, x_5, x_70);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(x_61, x_49, x_56, x_53, x_57, x_58, x_59, x_60, x_54, x_55, x_84, x_2, x_3, x_4, x_5, x_85);
lean_dec(x_84);
lean_dec(x_49);
lean_dec(x_61);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
x_88 = lean_array_push(x_87, x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_50);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_Decl_reduceArity(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_append___rarg(x_4, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1(x_1, x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceArity___elambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 1;
x_3 = l_Lean_Compiler_LCNF_reduceArity___closed__1;
x_4 = l_Lean_Compiler_LCNF_reduceArity___closed__2;
x_5 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_reduceArity___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_reduceArity___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2744_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_FindUsed_State_used___default = _init_l_Lean_Compiler_LCNF_FindUsed_State_used___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_FindUsed_State_used___default);
l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1 = _init_l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_FindUsed_visitExpr___closed__1);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6);
l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8);
l_Lean_Compiler_LCNF_reduceArity___closed__1 = _init_l_Lean_Compiler_LCNF_reduceArity___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity___closed__1);
l_Lean_Compiler_LCNF_reduceArity___closed__2 = _init_l_Lean_Compiler_LCNF_reduceArity___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity___closed__2);
l_Lean_Compiler_LCNF_reduceArity___closed__3 = _init_l_Lean_Compiler_LCNF_reduceArity___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity___closed__3);
l_Lean_Compiler_LCNF_reduceArity = _init_l_Lean_Compiler_LCNF_reduceArity();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity);
res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2744_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
