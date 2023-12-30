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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__4;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toArg(lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__2___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__10(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_reduceArity___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_State_used___default;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visit___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_10);
x_13 = lean_st_ref_take(x_3, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_14, x_1, x_16);
x_18 = lean_st_ref_set(x_3, x_17, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_14 = lean_array_uget(x_1, x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_15 = x_28;
x_16 = x_11;
goto block_23;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_4, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = lean_array_fget(x_24, x_25);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_25, x_34);
lean_dec(x_25);
lean_ctor_set(x_4, 1, x_35);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_name_eq(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_4);
x_15 = x_41;
x_16 = x_40;
goto block_23;
}
else
{
lean_object* x_42; 
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_15 = x_42;
x_16 = x_11;
goto block_23;
}
}
else
{
lean_object* x_43; 
lean_dec(x_33);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
x_15 = x_43;
x_16 = x_11;
goto block_23;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
x_44 = lean_array_fget(x_24, x_25);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_25, x_45);
lean_dec(x_25);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_24);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_26);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_name_eq(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_47);
x_15 = x_53;
x_16 = x_52;
goto block_23;
}
else
{
lean_object* x_54; 
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_15 = x_54;
x_16 = x_11;
goto block_23;
}
}
else
{
lean_object* x_55; 
lean_dec(x_44);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_47);
x_15 = x_55;
x_16 = x_11;
goto block_23;
}
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 2);
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
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_16 = lean_array_get_size(x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_12);
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
lean_dec(x_12);
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
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(x_12, x_24, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_12);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_array_get_size(x_12);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_28);
lean_inc(x_12);
x_30 = l_Array_toSubarray___rarg(x_12, x_29, x_28);
x_31 = lean_ctor_get(x_13, 3);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_array_get_size(x_31);
x_33 = lean_usize_of_nat(x_32);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2(x_31, x_33, x_34, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_array_get_size(x_31);
x_38 = lean_array_get_size(x_12);
x_39 = l_Array_toSubarray___rarg(x_12, x_37, x_38);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3(x_39, x_41, x_43, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Array_toSubarray___rarg(x_31, x_28, x_32);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4(x_47, x_49, x_51, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_47);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_44);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 4:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_dec(x_1);
x_59 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
x_63 = lean_array_get_size(x_58);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_lt(x_64, x_63);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_box(0);
lean_ctor_set(x_59, 0, x_66);
return x_59;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_63, x_63);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
lean_ctor_set(x_59, 0, x_68);
return x_59;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_59);
x_69 = 0;
x_70 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(x_58, x_69, x_70, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_58);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_dec(x_59);
x_74 = lean_array_get_size(x_58);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_74, x_74);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_84 = lean_box(0);
x_85 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(x_58, x_82, x_83, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_58);
return x_85;
}
}
}
}
default: 
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_8);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_12 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_visitLetValue___spec__1(x_15, x_24, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_13 = lean_st_mk_ref(x_7, x_6);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
x_14 = x_7;
goto block_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_9, x_9);
if (x_26 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
x_14 = x_7;
goto block_25;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_FindUsed_collectUsedParams___spec__1(x_8, x_27, x_28, x_7);
lean_dec(x_8);
x_14 = x_29;
goto block_25;
}
}
block_25:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
lean_inc(x_15);
x_18 = l_Lean_Compiler_LCNF_FindUsed_visit(x_12, x_17, x_15, x_2, x_3, x_4, x_5, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_1, x_13, x_12);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_get_size(x_15);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__1(x_15, x_19, x_20, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_inc(x_2);
x_28 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_2, x_27, x_7, x_8, x_9, x_10, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
x_31 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_3, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_35 = lean_ptr_addr(x_33);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
x_38 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_39 = lean_ptr_addr(x_29);
x_40 = lean_usize_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_31, 0, x_41);
return x_31;
}
else
{
lean_dec(x_33);
lean_dec(x_29);
lean_ctor_set(x_31, 0, x_4);
return x_31;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_45 = lean_ptr_addr(x_42);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_29);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_50 = lean_ptr_addr(x_29);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_29);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_43);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__2), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_name_eq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
size_t x_25; uint8_t x_26; 
x_25 = lean_ptr_addr(x_8);
x_26 = lean_usize_dec_eq(x_25, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 0);
lean_dec(x_29);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_15, 0, x_30);
return x_15;
}
}
else
{
lean_dec(x_17);
lean_dec(x_8);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_34 = lean_ptr_addr(x_31);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
else
{
size_t x_39; uint8_t x_40; 
x_39 = lean_ptr_addr(x_8);
x_40 = lean_usize_dec_eq(x_39, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_41 = x_1;
} else {
 lean_dec_ref(x_1);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_31);
lean_dec(x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_32);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(x_12, x_8, x_10, x_1, x_49, x_2, x_3, x_4, x_5, x_6, x_7);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; size_t x_55; size_t x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_56 = lean_ptr_addr(x_54);
x_57 = lean_usize_dec_eq(x_55, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_1, 0);
lean_dec(x_60);
lean_ctor_set(x_1, 1, x_54);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_61; 
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_52, 0, x_61);
return x_52;
}
}
else
{
size_t x_62; uint8_t x_63; 
x_62 = lean_ptr_addr(x_8);
x_63 = lean_usize_dec_eq(x_62, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_1, 0);
lean_dec(x_66);
lean_ctor_set(x_1, 1, x_54);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_67; 
lean_dec(x_1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_54);
lean_ctor_set(x_52, 0, x_67);
return x_52;
}
}
else
{
lean_dec(x_54);
lean_dec(x_8);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_52, 0);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_52);
x_70 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_71 = lean_ptr_addr(x_68);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_73 = x_1;
} else {
 lean_dec_ref(x_1);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_68);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
else
{
size_t x_76; uint8_t x_77; 
x_76 = lean_ptr_addr(x_8);
x_77 = lean_usize_dec_eq(x_76, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_78 = x_1;
} else {
 lean_dec_ref(x_1);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_68);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_69);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_68);
lean_dec(x_8);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_69);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_52);
if (x_82 == 0)
{
return x_52;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_52, 0);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_52);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 4);
lean_inc(x_88);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_89 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_88, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_86, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 2);
lean_inc(x_93);
lean_inc(x_86);
x_94 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_86, x_92, x_93, x_90, x_3, x_4, x_5, x_6, x_91);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_87);
x_97 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_87, x_2, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; size_t x_100; size_t x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ptr_addr(x_87);
lean_dec(x_87);
x_101 = lean_ptr_addr(x_99);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_86);
x_103 = !lean_is_exclusive(x_1);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_1, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_1, 0);
lean_dec(x_105);
lean_ctor_set(x_1, 1, x_99);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set(x_97, 0, x_1);
return x_97;
}
else
{
lean_object* x_106; 
lean_dec(x_1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_99);
lean_ctor_set(x_97, 0, x_106);
return x_97;
}
}
else
{
size_t x_107; size_t x_108; uint8_t x_109; 
x_107 = lean_ptr_addr(x_86);
lean_dec(x_86);
x_108 = lean_ptr_addr(x_95);
x_109 = lean_usize_dec_eq(x_107, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_1);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_1, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_1, 0);
lean_dec(x_112);
lean_ctor_set(x_1, 1, x_99);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set(x_97, 0, x_1);
return x_97;
}
else
{
lean_object* x_113; 
lean_dec(x_1);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_99);
lean_ctor_set(x_97, 0, x_113);
return x_97;
}
}
else
{
lean_dec(x_99);
lean_dec(x_95);
lean_ctor_set(x_97, 0, x_1);
return x_97;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_97, 0);
x_115 = lean_ctor_get(x_97, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_97);
x_116 = lean_ptr_addr(x_87);
lean_dec(x_87);
x_117 = lean_ptr_addr(x_114);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_86);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_119 = x_1;
} else {
 lean_dec_ref(x_1);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_95);
lean_ctor_set(x_120, 1, x_114);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
return x_121;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_86);
lean_dec(x_86);
x_123 = lean_ptr_addr(x_95);
x_124 = lean_usize_dec_eq(x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_125 = x_1;
} else {
 lean_dec_ref(x_1);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_95);
lean_ctor_set(x_126, 1, x_114);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_115);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_114);
lean_dec(x_95);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_115);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_95);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_97);
if (x_129 == 0)
{
return x_97;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_97, 0);
x_131 = lean_ctor_get(x_97, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_97);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_89);
if (x_133 == 0)
{
return x_89;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_89, 0);
x_135 = lean_ctor_get(x_89, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_89);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
case 2:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 4);
lean_inc(x_139);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_140 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_139, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_137, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 2);
lean_inc(x_144);
lean_inc(x_137);
x_145 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_137, x_143, x_144, x_141, x_3, x_4, x_5, x_6, x_142);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_138);
x_148 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_138, x_2, x_3, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; size_t x_151; size_t x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_152 = lean_ptr_addr(x_150);
x_153 = lean_usize_dec_eq(x_151, x_152);
if (x_153 == 0)
{
uint8_t x_154; 
lean_dec(x_137);
x_154 = !lean_is_exclusive(x_1);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_1, 1);
lean_dec(x_155);
x_156 = lean_ctor_get(x_1, 0);
lean_dec(x_156);
lean_ctor_set(x_1, 1, x_150);
lean_ctor_set(x_1, 0, x_146);
lean_ctor_set(x_148, 0, x_1);
return x_148;
}
else
{
lean_object* x_157; 
lean_dec(x_1);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_150);
lean_ctor_set(x_148, 0, x_157);
return x_148;
}
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_159 = lean_ptr_addr(x_146);
x_160 = lean_usize_dec_eq(x_158, x_159);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_1);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_1, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_1, 0);
lean_dec(x_163);
lean_ctor_set(x_1, 1, x_150);
lean_ctor_set(x_1, 0, x_146);
lean_ctor_set(x_148, 0, x_1);
return x_148;
}
else
{
lean_object* x_164; 
lean_dec(x_1);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_146);
lean_ctor_set(x_164, 1, x_150);
lean_ctor_set(x_148, 0, x_164);
return x_148;
}
}
else
{
lean_dec(x_150);
lean_dec(x_146);
lean_ctor_set(x_148, 0, x_1);
return x_148;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_148, 0);
x_166 = lean_ctor_get(x_148, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_148);
x_167 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_168 = lean_ptr_addr(x_165);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_137);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_170 = x_1;
} else {
 lean_dec_ref(x_1);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(2, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_146);
lean_ctor_set(x_171, 1, x_165);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
else
{
size_t x_173; size_t x_174; uint8_t x_175; 
x_173 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_174 = lean_ptr_addr(x_146);
x_175 = lean_usize_dec_eq(x_173, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_176 = x_1;
} else {
 lean_dec_ref(x_1);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(2, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_146);
lean_ctor_set(x_177, 1, x_165);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_166);
return x_178;
}
else
{
lean_object* x_179; 
lean_dec(x_165);
lean_dec(x_146);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_166);
return x_179;
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_146);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_148);
if (x_180 == 0)
{
return x_148;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_148, 0);
x_182 = lean_ctor_get(x_148, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_148);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_140);
if (x_184 == 0)
{
return x_140;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_140, 0);
x_186 = lean_ctor_get(x_140, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_140);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
case 4:
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_1, 0);
lean_inc(x_188);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
x_192 = lean_ctor_get(x_188, 2);
x_193 = lean_ctor_get(x_188, 3);
x_194 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
lean_inc(x_193);
x_195 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(x_193, x_194, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; size_t x_198; size_t x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = lean_ptr_addr(x_193);
lean_dec(x_193);
x_199 = lean_ptr_addr(x_197);
x_200 = lean_usize_dec_eq(x_198, x_199);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_1);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_1, 0);
lean_dec(x_202);
lean_ctor_set(x_188, 3, x_197);
lean_ctor_set(x_195, 0, x_1);
return x_195;
}
else
{
lean_object* x_203; 
lean_dec(x_1);
lean_ctor_set(x_188, 3, x_197);
x_203 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_203, 0, x_188);
lean_ctor_set(x_195, 0, x_203);
return x_195;
}
}
else
{
lean_dec(x_197);
lean_free_object(x_188);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_ctor_set(x_195, 0, x_1);
return x_195;
}
}
else
{
lean_object* x_204; lean_object* x_205; size_t x_206; size_t x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_195, 0);
x_205 = lean_ctor_get(x_195, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_195);
x_206 = lean_ptr_addr(x_193);
lean_dec(x_193);
x_207 = lean_ptr_addr(x_204);
x_208 = lean_usize_dec_eq(x_206, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_209 = x_1;
} else {
 lean_dec_ref(x_1);
 x_209 = lean_box(0);
}
lean_ctor_set(x_188, 3, x_204);
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(4, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_188);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
else
{
lean_object* x_212; 
lean_dec(x_204);
lean_free_object(x_188);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_205);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_free_object(x_188);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_195);
if (x_213 == 0)
{
return x_195;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_195, 0);
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_195);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_188, 0);
x_218 = lean_ctor_get(x_188, 1);
x_219 = lean_ctor_get(x_188, 2);
x_220 = lean_ctor_get(x_188, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_188);
x_221 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
lean_inc(x_220);
x_222 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_ReduceArity_reduce___spec__2(x_220, x_221, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; uint8_t x_228; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_ptr_addr(x_220);
lean_dec(x_220);
x_227 = lean_ptr_addr(x_223);
x_228 = lean_usize_dec_eq(x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_229 = x_1;
} else {
 lean_dec_ref(x_1);
 x_229 = lean_box(0);
}
x_230 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_230, 0, x_217);
lean_ctor_set(x_230, 1, x_218);
lean_ctor_set(x_230, 2, x_219);
lean_ctor_set(x_230, 3, x_223);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(4, 1, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
if (lean_is_scalar(x_225)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_225;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_224);
return x_232;
}
else
{
lean_object* x_233; 
lean_dec(x_223);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
if (lean_is_scalar(x_225)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_225;
}
lean_ctor_set(x_233, 0, x_1);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_1);
x_234 = lean_ctor_get(x_222, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_236 = x_222;
} else {
 lean_dec_ref(x_222);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
default: 
{
lean_object* x_238; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_1);
lean_ctor_set(x_238, 1, x_7);
return x_238;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_4, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
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
x_33 = l_Lean_Compiler_LCNF_Param_toArg(x_27);
lean_dec(x_27);
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
x_45 = l_Lean_Compiler_LCNF_Param_toArg(x_38);
lean_dec(x_38);
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
x_67 = l_Lean_Compiler_LCNF_Param_toArg(x_59);
lean_dec(x_59);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__12___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_st_ref_take(x_6, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_23, 3);
x_27 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_28 = 0;
x_29 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PersistentArray_push___rarg(x_26, x_30);
lean_ctor_set(x_23, 3, x_31);
x_32 = lean_st_ref_set(x_6, x_23, x_24);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
x_41 = lean_ctor_get(x_23, 2);
x_42 = lean_ctor_get(x_23, 3);
x_43 = lean_ctor_get(x_23, 4);
x_44 = lean_ctor_get(x_23, 5);
x_45 = lean_ctor_get(x_23, 6);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_46 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_47 = 0;
x_48 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
lean_inc(x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_PersistentArray_push___rarg(x_42, x_49);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_51, 6, x_45);
x_52 = lean_st_ref_set(x_6, x_51, x_24);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
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
x_1 = lean_unsigned_to_nat(8u);
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
lean_inc(x_4);
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
lean_object* x_106; 
x_106 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_26 = x_106;
goto block_105;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_1, x_1);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_26 = x_108;
goto block_105;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_110 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__7___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__8(x_2, x_3, x_18, x_17, x_109);
x_26 = x_110;
goto block_105;
}
}
block_105:
{
lean_object* x_27; 
if (x_23 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_27 = x_100;
goto block_99;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_1, x_1);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_27 = x_102;
goto block_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_104 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__5___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__6(x_2, x_3, x_18, x_17, x_103);
x_27 = x_104;
goto block_99;
}
}
block_99:
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
x_40 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__3;
x_41 = lean_st_mk_ref(x_40, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_17, x_18, x_3, x_42, x_12, x_13, x_14, x_15, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_45);
lean_inc(x_45);
x_48 = l_Array_toSubarray___rarg(x_45, x_22, x_47);
x_49 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_get_size(x_19);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__4(x_19, x_52, x_18, x_50, x_42, x_12, x_13, x_14, x_15, x_46);
lean_dec(x_19);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_36);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__5;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_59 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_57, x_58, x_12, x_13, x_14, x_15, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
x_65 = 0;
x_66 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__6;
x_67 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_9);
lean_ctor_set(x_67, 2, x_10);
lean_ctor_set(x_67, 3, x_45);
lean_ctor_set(x_67, 4, x_64);
lean_ctor_set(x_67, 5, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 1, x_7);
lean_inc(x_67);
x_68 = l_Lean_Compiler_LCNF_Decl_saveMono(x_67, x_14, x_15, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_get(x_42, x_69);
lean_dec(x_42);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_eraseParams(x_27, x_12, x_13, x_14, x_15, x_71);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_27);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
x_76 = lean_array_push(x_75, x_37);
x_77 = lean_array_push(x_76, x_67);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = l_Lean_Compiler_LCNF_Decl_reduceArity___lambda__1___closed__7;
x_80 = lean_array_push(x_79, x_37);
x_81 = lean_array_push(x_80, x_67);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_59);
if (x_83 == 0)
{
return x_59;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_59, 0);
x_85 = lean_ctor_get(x_59, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_59);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
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
x_87 = !lean_is_exclusive(x_33);
if (x_87 == 0)
{
return x_33;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_33, 0);
x_89 = lean_ctor_get(x_33, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_33);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
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
x_91 = !lean_is_exclusive(x_30);
if (x_91 == 0)
{
return x_30;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_30, 0);
x_93 = lean_ctor_get(x_30, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_30);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
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
x_95 = !lean_is_exclusive(x_25);
if (x_95 == 0)
{
return x_25;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_25, 0);
x_97 = lean_ctor_get(x_25, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_25);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
x_31 = l_Lean_MessageData_ofName(x_13);
x_32 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_9);
x_36 = l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(x_9);
x_37 = lean_box(0);
x_38 = l_List_mapTR_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(x_36, x_37);
x_39 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_38, x_37);
x_40 = l_Lean_MessageData_ofList(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
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
x_71 = l_Lean_MessageData_ofName(x_53);
x_72 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_49);
x_76 = l_Lean_RBTree_toList___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__9(x_49);
x_77 = lean_box(0);
x_78 = l_List_mapTR_loop___at_Lean_Compiler_LCNF_Decl_reduceArity___spec__11(x_76, x_77);
x_79 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_78, x_77);
x_80 = l_Lean_MessageData_ofList(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
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
x_10 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
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
x_13 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
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
x_17 = l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2;
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10;
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ReduceArity", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16;
x_2 = lean_unsigned_to_nat(2387u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1);
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
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387____closed__17);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2387_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
