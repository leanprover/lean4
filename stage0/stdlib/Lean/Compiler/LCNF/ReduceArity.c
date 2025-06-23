// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Internalize
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
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
static lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity;
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4;
lean_object* l_Lean_Compiler_LCNF_Param_toArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_RBMap_size___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_box(0);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_free_object(x_2);
x_10 = lean_st_ref_take(x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_FVarIdSet_insert(x_11, x_1);
x_14 = lean_st_ref_set(x_3, x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_21, x_1);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
x_25 = lean_st_ref_take(x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_FVarIdSet_insert(x_26, x_1);
x_29 = lean_st_ref_set(x_3, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_9, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_16, x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_27);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_array_uget(x_1, x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_name_eq(x_28, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_5);
x_32 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_28, x_5, x_6, x_7);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_8 = x_4;
x_9 = x_33;
goto block_13;
}
else
{
lean_dec(x_28);
x_8 = x_4;
x_9 = x_7;
goto block_13;
}
}
else
{
lean_dec(x_25);
x_8 = x_4;
x_9 = x_7;
goto block_13;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_34 = lean_array_fget(x_16, x_17);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_17, x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_18);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_array_uget(x_1, x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_name_eq(x_38, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_inc(x_5);
x_42 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_38, x_5, x_6, x_7);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_8 = x_37;
x_9 = x_43;
goto block_13;
}
else
{
lean_dec(x_38);
x_8 = x_37;
x_9 = x_7;
goto block_13;
}
}
else
{
lean_dec(x_34);
x_8 = x_37;
x_9 = x_7;
goto block_13;
}
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_uget(x_11, x_4);
lean_inc(x_6);
x_13 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_12, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
lean_inc(x_1);
{
size_t _tmp_3 = x_16;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_7 = x_14;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_uget(x_11, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_6);
x_14 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_13, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
lean_inc(x_1);
{
size_t _tmp_3 = x_17;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_7 = x_15;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_13;
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
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_9, x_2, x_3, x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 3);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_13);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_18, x_18);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_32 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_13, x_30, x_31, x_19, x_2, x_3, x_8);
lean_dec(x_13);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; uint8_t x_55; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_13);
lean_inc(x_34);
lean_inc(x_13);
x_35 = l_Array_toSubarray___redArg(x_13, x_33, x_34);
x_36 = lean_array_size(x_15);
x_37 = 0;
lean_inc(x_2);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_15, x_36, x_37, x_35, x_2, x_3, x_8);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_array_get_size(x_15);
lean_inc(x_34);
lean_inc(x_40);
x_41 = l_Array_toSubarray___redArg(x_13, x_40, x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
x_44 = lean_box(0);
x_45 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_46 = lean_usize_of_nat(x_42);
lean_dec(x_42);
lean_inc(x_2);
x_47 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_44, x_41, x_45, x_46, x_44, x_2, x_3, x_39);
lean_dec(x_41);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Array_toSubarray___redArg(x_15, x_34, x_40);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 2);
lean_inc(x_51);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_54 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_44, x_49, x_52, x_53, x_44, x_2, x_3, x_48);
lean_dec(x_49);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_44);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 4:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
lean_inc(x_2);
x_61 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_59, x_2, x_3, x_8);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get_size(x_60);
x_67 = lean_box(0);
x_68 = lean_nat_dec_lt(x_65, x_66);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_2);
lean_ctor_set(x_61, 0, x_67);
return x_61;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_66, x_66);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_2);
lean_ctor_set(x_61, 0, x_67);
return x_61;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; 
lean_free_object(x_61);
x_70 = 0;
x_71 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_72 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_60, x_70, x_71, x_67, x_2, x_3, x_63);
lean_dec(x_60);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_dec(x_61);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_60);
x_76 = lean_box(0);
x_77 = lean_nat_dec_lt(x_74, x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_75);
lean_dec(x_60);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_75, x_75);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_75);
lean_dec(x_60);
lean_dec(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_83 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_60, x_81, x_82, x_76, x_2, x_3, x_73);
lean_dec(x_60);
return x_83;
}
}
}
}
default: 
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_8);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
x_20 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_5);
x_22 = l_Lean_Compiler_LCNF_FindUsed_visit(x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_12 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_5);
x_24 = l_Lean_Compiler_LCNF_FindUsed_visit(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_12 = x_24;
goto block_18;
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
block_18:
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 3);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_2);
x_26 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_1 = x_24;
x_8 = x_27;
goto _start;
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_30);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_free_object(x_1);
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_30, x_37, x_38, x_34, x_2, x_3, x_8);
lean_dec(x_30);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_40);
x_43 = lean_box(0);
x_44 = lean_nat_dec_lt(x_41, x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_42, x_42);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_50 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_40, x_48, x_49, x_43, x_2, x_3, x_8);
lean_dec(x_40);
return x_50;
}
}
}
}
case 4:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 3);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
x_54 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_52, x_2, x_3, x_8);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_53);
x_60 = lean_box(0);
x_61 = lean_nat_dec_lt(x_58, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_2);
lean_ctor_set(x_54, 0, x_60);
return x_54;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_2);
lean_ctor_set(x_54, 0, x_60);
return x_54;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
lean_free_object(x_54);
x_63 = 0;
x_64 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_65 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_53, x_63, x_64, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_53);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_array_get_size(x_53);
x_69 = lean_box(0);
x_70 = lean_nat_dec_lt(x_67, x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_53);
lean_dec(x_2);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_68, x_68);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_53);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_76 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_53, x_74, x_75, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_53);
return x_76;
}
}
}
}
case 5:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_77, x_2, x_3, x_8);
return x_78;
}
case 6:
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_8);
return x_80;
}
default: 
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
lean_dec(x_1);
x_9 = x_81;
x_10 = x_82;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_22;
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 4);
lean_inc(x_18);
lean_dec(x_9);
lean_inc(x_11);
x_19 = l_Lean_Compiler_LCNF_FindUsed_visit(x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_10;
x_2 = x_11;
x_3 = x_12;
x_4 = x_13;
x_5 = x_14;
x_6 = x_15;
x_7 = x_16;
x_8 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FVarIdSet_insert(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FindUsed_visit___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_7);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_7);
x_10 = x_9;
goto block_42;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_7);
x_10 = x_9;
goto block_42;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_7, x_47, x_48, x_9);
lean_dec(x_7);
x_10 = x_49;
goto block_42;
}
}
block_42:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_mk_ref(x_9, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0;
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 0, x_1);
lean_inc(x_13);
x_16 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(x_15, x_8, x_11, x_13, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_10);
lean_inc(x_27);
x_31 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(x_29, x_8, x_30, x_27, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_27, x_32);
lean_dec(x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_18, x_28);
lean_inc(x_17);
lean_ctor_set(x_15, 1, x_29);
if (x_27 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_31 = lean_array_push(x_16, x_30);
lean_ctor_set(x_4, 1, x_31);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
x_32 = lean_array_uget(x_1, x_3);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_18, x_34);
lean_inc(x_17);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_19);
if (x_33 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_36);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_38 = lean_array_push(x_16, x_37);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_36);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = lean_array_uget(x_1, x_3);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_inc(x_41);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_43);
if (x_49 == 0)
{
lean_object* x_53; 
lean_dec(x_42);
lean_dec(x_41);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
x_6 = x_53;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_array_fget(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_55 = lean_array_push(x_40, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_6 = x_56;
x_7 = x_5;
goto block_11;
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 2);
lean_inc(x_29);
x_13 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
x_13 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_14 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_15);
x_18 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = lean_array_fset(x_2, x_1, x_17);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_23;
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_1 = x_26;
x_8 = x_16;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(316u);
x_4 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
x_5 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 3)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 2);
x_77 = lean_ctor_get(x_72, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
x_80 = lean_ctor_get(x_2, 2);
x_81 = lean_name_eq(x_75, x_78);
lean_dec(x_75);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; size_t x_95; size_t x_96; uint8_t x_97; 
lean_free_object(x_72);
lean_dec(x_76);
lean_inc(x_73);
x_82 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_95 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_96 = lean_ptr_addr(x_83);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
x_86 = x_97;
goto block_94;
}
else
{
size_t x_98; uint8_t x_99; 
x_98 = lean_ptr_addr(x_71);
x_99 = lean_usize_dec_eq(x_98, x_98);
x_86 = x_99;
goto block_94;
}
block_94:
{
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_1);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_1, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_1, 0);
lean_dec(x_89);
lean_ctor_set(x_1, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_71);
lean_ctor_set(x_91, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_83);
lean_dec(x_71);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; size_t x_128; size_t x_129; uint8_t x_130; 
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
x_102 = lean_array_get_size(x_76);
x_103 = l_Array_toSubarray___redArg(x_76, x_100, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
x_105 = lean_array_size(x_80);
x_106 = 0;
x_107 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_80, x_105, x_106, x_104, x_7);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
lean_inc(x_79);
lean_ctor_set(x_72, 2, x_110);
lean_ctor_set(x_72, 1, x_111);
lean_ctor_set(x_72, 0, x_79);
lean_inc(x_71);
x_112 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_71, x_72, x_4, x_109);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_73);
x_115 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_128 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_129 = lean_ptr_addr(x_116);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
lean_dec(x_71);
x_119 = x_130;
goto block_127;
}
else
{
size_t x_131; size_t x_132; uint8_t x_133; 
x_131 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_132 = lean_ptr_addr(x_113);
x_133 = lean_usize_dec_eq(x_131, x_132);
x_119 = x_133;
goto block_127;
}
block_127:
{
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_1, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_1, 0);
lean_dec(x_122);
lean_ctor_set(x_1, 1, x_116);
lean_ctor_set(x_1, 0, x_113);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_116);
if (lean_is_scalar(x_118)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_118;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_117);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_116);
lean_dec(x_113);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_118;
}
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_117);
return x_126;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_72, 0);
x_135 = lean_ctor_get(x_72, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_72);
x_136 = lean_ctor_get(x_2, 0);
x_137 = lean_ctor_get(x_2, 1);
x_138 = lean_ctor_get(x_2, 2);
x_139 = lean_name_eq(x_134, x_136);
lean_dec(x_134);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; size_t x_150; size_t x_151; uint8_t x_152; 
lean_dec(x_135);
lean_inc(x_73);
x_140 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6, x_7);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_150 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_151 = lean_ptr_addr(x_141);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
x_144 = x_152;
goto block_149;
}
else
{
size_t x_153; uint8_t x_154; 
x_153 = lean_ptr_addr(x_71);
x_154 = lean_usize_dec_eq(x_153, x_153);
x_144 = x_154;
goto block_149;
}
block_149:
{
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_145 = x_1;
} else {
 lean_dec_ref(x_1);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_71);
lean_ctor_set(x_146, 1, x_141);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec(x_141);
lean_dec(x_71);
if (lean_is_scalar(x_143)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_143;
}
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; size_t x_181; size_t x_182; uint8_t x_183; 
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
x_157 = lean_array_get_size(x_135);
x_158 = l_Array_toSubarray___redArg(x_135, x_155, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
x_160 = lean_array_size(x_138);
x_161 = 0;
x_162 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_138, x_160, x_161, x_159, x_7);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_box(0);
lean_inc(x_137);
x_167 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_167, 0, x_137);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
lean_inc(x_71);
x_168 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_71, x_167, x_4, x_164);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_73);
x_171 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_181 = lean_ptr_addr(x_73);
lean_dec(x_73);
x_182 = lean_ptr_addr(x_172);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_dec(x_71);
x_175 = x_183;
goto block_180;
}
else
{
size_t x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_185 = lean_ptr_addr(x_169);
x_186 = lean_usize_dec_eq(x_184, x_185);
x_175 = x_186;
goto block_180;
}
block_180:
{
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
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_172);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_173);
return x_178;
}
else
{
lean_object* x_179; 
lean_dec(x_172);
lean_dec(x_169);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_173);
return x_179;
}
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; size_t x_201; size_t x_202; uint8_t x_203; 
lean_dec(x_72);
x_187 = lean_ctor_get(x_1, 1);
lean_inc(x_187);
lean_inc(x_187);
x_188 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_187, x_2, x_3, x_4, x_5, x_6, x_7);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_201 = lean_ptr_addr(x_187);
lean_dec(x_187);
x_202 = lean_ptr_addr(x_189);
x_203 = lean_usize_dec_eq(x_201, x_202);
if (x_203 == 0)
{
x_192 = x_203;
goto block_200;
}
else
{
size_t x_204; uint8_t x_205; 
x_204 = lean_ptr_addr(x_71);
x_205 = lean_usize_dec_eq(x_204, x_204);
x_192 = x_205;
goto block_200;
}
block_200:
{
if (x_192 == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_1);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_1, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_1, 0);
lean_dec(x_195);
lean_ctor_set(x_1, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_191;
}
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_190);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_1);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_71);
lean_ctor_set(x_197, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_191;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_190);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_189);
lean_dec(x_71);
if (lean_is_scalar(x_191)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_191;
}
lean_ctor_set(x_199, 0, x_1);
lean_ctor_set(x_199, 1, x_190);
return x_199;
}
}
}
}
case 1:
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_1, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_1, 1);
lean_inc(x_207);
x_24 = x_206;
x_25 = x_207;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_70;
}
case 2:
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_1, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_1, 1);
lean_inc(x_209);
x_24 = x_208;
x_25 = x_209;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_70;
}
case 4:
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_1, 0);
lean_inc(x_210);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_214 = lean_ctor_get(x_210, 2);
x_215 = lean_ctor_get(x_210, 3);
x_216 = lean_unsigned_to_nat(0u);
lean_inc(x_215);
x_217 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_216, x_215, x_2, x_3, x_4, x_5, x_6, x_7);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; size_t x_220; size_t x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ptr_addr(x_215);
lean_dec(x_215);
x_221 = lean_ptr_addr(x_219);
x_222 = lean_usize_dec_eq(x_220, x_221);
if (x_222 == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_1);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_1, 0);
lean_dec(x_224);
lean_ctor_set(x_210, 3, x_219);
lean_ctor_set(x_217, 0, x_1);
return x_217;
}
else
{
lean_object* x_225; 
lean_dec(x_1);
lean_ctor_set(x_210, 3, x_219);
x_225 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_225, 0, x_210);
lean_ctor_set(x_217, 0, x_225);
return x_217;
}
}
else
{
lean_dec(x_219);
lean_free_object(x_210);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_ctor_set(x_217, 0, x_1);
return x_217;
}
}
else
{
lean_object* x_226; lean_object* x_227; size_t x_228; size_t x_229; uint8_t x_230; 
x_226 = lean_ctor_get(x_217, 0);
x_227 = lean_ctor_get(x_217, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_217);
x_228 = lean_ptr_addr(x_215);
lean_dec(x_215);
x_229 = lean_ptr_addr(x_226);
x_230 = lean_usize_dec_eq(x_228, x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_231 = x_1;
} else {
 lean_dec_ref(x_1);
 x_231 = lean_box(0);
}
lean_ctor_set(x_210, 3, x_226);
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(4, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_210);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_227);
return x_233;
}
else
{
lean_object* x_234; 
lean_dec(x_226);
lean_free_object(x_210);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_1);
lean_ctor_set(x_234, 1, x_227);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; size_t x_245; uint8_t x_246; 
x_235 = lean_ctor_get(x_210, 0);
x_236 = lean_ctor_get(x_210, 1);
x_237 = lean_ctor_get(x_210, 2);
x_238 = lean_ctor_get(x_210, 3);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_210);
x_239 = lean_unsigned_to_nat(0u);
lean_inc(x_238);
x_240 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_239, x_238, x_2, x_3, x_4, x_5, x_6, x_7);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_245 = lean_ptr_addr(x_241);
x_246 = lean_usize_dec_eq(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_247 = x_1;
} else {
 lean_dec_ref(x_1);
 x_247 = lean_box(0);
}
x_248 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_248, 0, x_235);
lean_ctor_set(x_248, 1, x_236);
lean_ctor_set(x_248, 2, x_237);
lean_ctor_set(x_248, 3, x_241);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(4, 1, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
if (lean_is_scalar(x_243)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_243;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_242);
return x_250;
}
else
{
lean_object* x_251; 
lean_dec(x_241);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
if (lean_is_scalar(x_243)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_243;
}
lean_ctor_set(x_251, 0, x_1);
lean_ctor_set(x_251, 1, x_242);
return x_251;
}
}
}
default: 
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_1);
lean_ctor_set(x_252, 1, x_7);
return x_252;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
block_70:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_24, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 4);
lean_inc(x_34);
x_35 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_34, x_26, x_27, x_28, x_29, x_30, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_24, x_33, x_32, x_36, x_28, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_25, x_26, x_27, x_28, x_29, x_30, x_40);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_47 = lean_ptr_addr(x_42);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_44);
x_8 = x_43;
x_9 = x_39;
x_10 = x_42;
x_11 = x_48;
goto block_15;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_50 = lean_ptr_addr(x_39);
x_51 = lean_usize_dec_eq(x_49, x_50);
x_8 = x_43;
x_9 = x_39;
x_10 = x_42;
x_11 = x_51;
goto block_15;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_57 = lean_ptr_addr(x_52);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_54);
x_16 = x_53;
x_17 = x_39;
x_18 = x_52;
x_19 = x_58;
goto block_23;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_60 = lean_ptr_addr(x_39);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_16 = x_53;
x_17 = x_39;
x_18 = x_52;
x_19 = x_61;
goto block_23;
}
}
default: 
{
uint8_t x_62; 
lean_dec(x_39);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_41, 0);
lean_dec(x_63);
x_64 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
x_65 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_64);
lean_ctor_set(x_41, 0, x_65);
return x_41;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_dec(x_41);
x_67 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
x_68 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_box(x_10);
x_14 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_18, x_28);
lean_inc(x_17);
lean_ctor_set(x_15, 1, x_29);
if (x_27 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_31 = l_Lean_Compiler_LCNF_Param_toArg(x_30);
lean_dec(x_30);
x_32 = lean_array_push(x_16, x_31);
lean_ctor_set(x_4, 1, x_32);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
x_33 = lean_array_uget(x_1, x_3);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_18, x_35);
lean_inc(x_17);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_19);
if (x_34 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_37);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_array_fget(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_39 = l_Lean_Compiler_LCNF_Param_toArg(x_38);
lean_dec(x_38);
x_40 = lean_array_push(x_16, x_39);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_37);
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = lean_array_uget(x_1, x_3);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_44, x_52);
lean_inc(x_43);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_45);
if (x_51 == 0)
{
lean_object* x_55; 
lean_dec(x_44);
lean_dec(x_43);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_42);
x_6 = x_55;
x_7 = x_5;
goto block_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_array_fget(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_57 = l_Lean_Compiler_LCNF_Param_toArg(x_56);
lean_dec(x_56);
x_58 = lean_array_push(x_42, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_6 = x_59;
x_7 = x_5;
goto block_11;
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_12);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6(x_1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
x_7 = l_Lean_MessageData_ofExpr(x_5);
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
x_11 = l_Lean_MessageData_ofExpr(x_9);
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
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6;
x_2 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5;
x_3 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4;
x_4 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3;
x_5 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2;
x_6 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1;
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
static double _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_st_ref_take(x_5, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 4);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; double x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_30 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_inc(x_7);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_31);
x_32 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
x_33 = lean_box(0);
x_34 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_35 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_float(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_35, sizeof(void*)*2 + 8, x_32);
x_36 = lean_unbox(x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 16, x_36);
x_37 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_38);
lean_ctor_set(x_13, 0, x_8);
x_39 = l_Lean_PersistentArray_push___redArg(x_28, x_13);
lean_ctor_set(x_21, 0, x_39);
x_40 = lean_st_ref_set(x_5, x_20, x_23);
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
uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
lean_dec(x_21);
x_49 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_50 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_inc(x_7);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_15);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_51);
x_52 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
x_53 = lean_box(0);
x_54 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_56);
x_57 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_19);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_8);
x_59 = l_Lean_PersistentArray_push___redArg(x_48, x_13);
x_60 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_47);
lean_ctor_set(x_20, 4, x_60);
x_61 = lean_st_ref_set(x_5, x_20, x_23);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; double x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
x_68 = lean_ctor_get(x_20, 2);
x_69 = lean_ctor_get(x_20, 3);
x_70 = lean_ctor_get(x_20, 5);
x_71 = lean_ctor_get(x_20, 6);
x_72 = lean_ctor_get(x_20, 7);
x_73 = lean_ctor_get(x_20, 8);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_74 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_75 = lean_ctor_get(x_21, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_76 = x_21;
} else {
 lean_dec_ref(x_21);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_78 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_inc(x_7);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_15);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_79);
x_80 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
x_81 = lean_box(0);
x_82 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_83 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_float(x_83, sizeof(void*)*2, x_80);
lean_ctor_set_float(x_83, sizeof(void*)*2 + 8, x_80);
x_84 = lean_unbox(x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*2 + 16, x_84);
x_85 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
x_86 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_19);
lean_ctor_set(x_86, 2, x_85);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_86);
lean_ctor_set(x_13, 0, x_8);
x_87 = l_Lean_PersistentArray_push___redArg(x_75, x_13);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 1, 8);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint64(x_88, sizeof(void*)*1, x_74);
x_89 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_67);
lean_ctor_set(x_89, 2, x_68);
lean_ctor_set(x_89, 3, x_69);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_70);
lean_ctor_set(x_89, 6, x_71);
lean_ctor_set(x_89, 7, x_72);
lean_ctor_set(x_89, 8, x_73);
x_90 = lean_st_ref_set(x_5, x_89, x_23);
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
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint64_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; double x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
lean_dec(x_19);
x_96 = lean_ctor_get(x_20, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_20, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_20, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_20, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_20, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_20, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_20, 7);
lean_inc(x_102);
x_103 = lean_ctor_get(x_20, 8);
lean_inc(x_103);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 x_104 = x_20;
} else {
 lean_dec_ref(x_20);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_106 = lean_ctor_get(x_21, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_107 = x_21;
} else {
 lean_dec_ref(x_21);
 x_107 = lean_box(0);
}
x_108 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_109 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_inc(x_7);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
lean_ctor_set(x_110, 3, x_7);
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_2);
x_112 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
x_113 = lean_box(0);
x_114 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_115 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_float(x_115, sizeof(void*)*2, x_112);
lean_ctor_set_float(x_115, sizeof(void*)*2 + 8, x_112);
x_116 = lean_unbox(x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*2 + 16, x_116);
x_117 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
x_118 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_111);
lean_ctor_set(x_118, 2, x_117);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_118);
lean_ctor_set(x_13, 0, x_8);
x_119 = l_Lean_PersistentArray_push___redArg(x_106, x_13);
if (lean_is_scalar(x_107)) {
 x_120 = lean_alloc_ctor(0, 1, 8);
} else {
 x_120 = x_107;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set_uint64(x_120, sizeof(void*)*1, x_105);
if (lean_is_scalar(x_104)) {
 x_121 = lean_alloc_ctor(0, 9, 0);
} else {
 x_121 = x_104;
}
lean_ctor_set(x_121, 0, x_96);
lean_ctor_set(x_121, 1, x_97);
lean_ctor_set(x_121, 2, x_98);
lean_ctor_set(x_121, 3, x_99);
lean_ctor_set(x_121, 4, x_120);
lean_ctor_set(x_121, 5, x_100);
lean_ctor_set(x_121, 6, x_101);
lean_ctor_set(x_121, 7, x_102);
lean_ctor_set(x_121, 8, x_103);
x_122 = lean_st_ref_set(x_5, x_121, x_95);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; double x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_127 = lean_ctor_get(x_13, 0);
lean_inc(x_127);
lean_dec(x_13);
x_128 = lean_st_ref_take(x_5, x_14);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 7);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 8);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 lean_ctor_release(x_129, 6);
 lean_ctor_release(x_129, 7);
 lean_ctor_release(x_129, 8);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get_uint64(x_130, sizeof(void*)*1);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_127);
lean_dec(x_127);
x_146 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7;
lean_inc(x_7);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_15);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set(x_147, 3, x_7);
if (lean_is_scalar(x_132)) {
 x_148 = lean_alloc_ctor(3, 2, 0);
} else {
 x_148 = x_132;
 lean_ctor_set_tag(x_148, 3);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_2);
x_149 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8;
x_150 = lean_box(0);
x_151 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_152 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set_float(x_152, sizeof(void*)*2, x_149);
lean_ctor_set_float(x_152, sizeof(void*)*2 + 8, x_149);
x_153 = lean_unbox(x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 16, x_153);
x_154 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10;
x_155 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_155, 2, x_154);
lean_inc(x_8);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_8);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_PersistentArray_push___redArg(x_143, x_156);
if (lean_is_scalar(x_144)) {
 x_158 = lean_alloc_ctor(0, 1, 8);
} else {
 x_158 = x_144;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set_uint64(x_158, sizeof(void*)*1, x_142);
if (lean_is_scalar(x_141)) {
 x_159 = lean_alloc_ctor(0, 9, 0);
} else {
 x_159 = x_141;
}
lean_ctor_set(x_159, 0, x_133);
lean_ctor_set(x_159, 1, x_134);
lean_ctor_set(x_159, 2, x_135);
lean_ctor_set(x_159, 3, x_136);
lean_ctor_set(x_159, 4, x_158);
lean_ctor_set(x_159, 5, x_137);
lean_ctor_set(x_159, 6, x_138);
lean_ctor_set(x_159, 7, x_139);
lean_ctor_set(x_159, 8, x_140);
x_160 = lean_st_ref_set(x_5, x_159, x_131);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_redArg", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceArity", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", used params: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18() {
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
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_290; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_290 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; size_t x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; size_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_335; uint8_t x_382; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
 x_293 = lean_box(0);
}
x_294 = l_Lean_RBMap_size___redArg(x_291);
x_295 = lean_array_get_size(x_11);
x_382 = lean_nat_dec_eq(x_294, x_295);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_unsigned_to_nat(0u);
x_384 = lean_nat_dec_eq(x_294, x_383);
lean_dec(x_294);
x_335 = x_384;
goto block_381;
}
else
{
lean_dec(x_294);
x_335 = x_382;
goto block_381;
}
block_315:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_308 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
lean_inc(x_300);
lean_inc(x_301);
lean_inc(x_8);
x_309 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_309, 0, x_8);
lean_ctor_set(x_309, 1, x_301);
lean_ctor_set(x_309, 2, x_300);
x_310 = lean_mk_empty_array_with_capacity(x_306);
x_311 = lean_nat_dec_lt(x_306, x_295);
if (x_311 == 0)
{
lean_dec(x_295);
lean_dec(x_291);
x_16 = x_309;
x_17 = x_296;
x_18 = x_307;
x_19 = x_299;
x_20 = x_301;
x_21 = x_308;
x_22 = x_304;
x_23 = x_306;
x_24 = x_298;
x_25 = x_297;
x_26 = x_300;
x_27 = x_302;
x_28 = x_303;
x_29 = x_305;
x_30 = x_310;
goto block_289;
}
else
{
uint8_t x_312; 
x_312 = lean_nat_dec_le(x_295, x_295);
if (x_312 == 0)
{
lean_dec(x_295);
lean_dec(x_291);
x_16 = x_309;
x_17 = x_296;
x_18 = x_307;
x_19 = x_299;
x_20 = x_301;
x_21 = x_308;
x_22 = x_304;
x_23 = x_306;
x_24 = x_298;
x_25 = x_297;
x_26 = x_300;
x_27 = x_302;
x_28 = x_303;
x_29 = x_305;
x_30 = x_310;
goto block_289;
}
else
{
size_t x_313; lean_object* x_314; 
x_313 = lean_usize_of_nat(x_295);
lean_dec(x_295);
x_314 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_291, x_11, x_297, x_313, x_310);
lean_dec(x_291);
x_16 = x_309;
x_17 = x_296;
x_18 = x_307;
x_19 = x_299;
x_20 = x_301;
x_21 = x_308;
x_22 = x_304;
x_23 = x_306;
x_24 = x_298;
x_25 = x_297;
x_26 = x_300;
x_27 = x_302;
x_28 = x_303;
x_29 = x_305;
x_30 = x_314;
goto block_289;
}
}
}
block_334:
{
size_t x_323; size_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_323 = lean_array_size(x_11);
x_324 = 0;
lean_inc(x_11);
lean_inc(x_317);
x_325 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(x_317, x_323, x_324, x_11);
x_326 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
lean_inc(x_8);
x_327 = l_Lean_Name_append(x_8, x_326);
x_328 = lean_unsigned_to_nat(0u);
x_329 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11;
x_330 = lean_nat_dec_lt(x_328, x_295);
if (x_330 == 0)
{
lean_dec(x_317);
x_296 = x_319;
x_297 = x_324;
x_298 = x_320;
x_299 = x_316;
x_300 = x_325;
x_301 = x_327;
x_302 = x_323;
x_303 = x_321;
x_304 = x_322;
x_305 = x_318;
x_306 = x_328;
x_307 = x_329;
goto block_315;
}
else
{
uint8_t x_331; 
x_331 = lean_nat_dec_le(x_295, x_295);
if (x_331 == 0)
{
lean_dec(x_317);
x_296 = x_319;
x_297 = x_324;
x_298 = x_320;
x_299 = x_316;
x_300 = x_325;
x_301 = x_327;
x_302 = x_323;
x_303 = x_321;
x_304 = x_322;
x_305 = x_318;
x_306 = x_328;
x_307 = x_329;
goto block_315;
}
else
{
size_t x_332; lean_object* x_333; 
x_332 = lean_usize_of_nat(x_295);
x_333 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(x_317, x_11, x_324, x_332, x_329);
x_296 = x_319;
x_297 = x_324;
x_298 = x_320;
x_299 = x_316;
x_300 = x_325;
x_301 = x_327;
x_302 = x_323;
x_303 = x_321;
x_304 = x_322;
x_305 = x_318;
x_306 = x_328;
x_307 = x_333;
goto block_315;
}
}
}
block_381:
{
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; 
lean_dec(x_293);
lean_dec(x_1);
x_336 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
x_337 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg(x_336, x_4, x_292);
x_338 = !lean_is_exclusive(x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_339 = lean_ctor_get(x_337, 0);
x_340 = lean_ctor_get(x_337, 1);
x_341 = lean_box(x_335);
lean_inc(x_291);
x_342 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 3, 2);
lean_closure_set(x_342, 0, x_291);
lean_closure_set(x_342, 1, x_341);
x_343 = lean_unbox(x_339);
lean_dec(x_339);
if (x_343 == 0)
{
lean_free_object(x_337);
x_316 = x_335;
x_317 = x_342;
x_318 = x_2;
x_319 = x_3;
x_320 = x_4;
x_321 = x_5;
x_322 = x_340;
goto block_334;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_344 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15;
lean_inc(x_8);
x_345 = l_Lean_MessageData_ofName(x_8);
lean_ctor_set_tag(x_337, 7);
lean_ctor_set(x_337, 1, x_345);
lean_ctor_set(x_337, 0, x_344);
x_346 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17;
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_337);
lean_ctor_set(x_347, 1, x_346);
x_348 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_291);
x_349 = lean_box(0);
x_350 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__8(x_348, x_349);
x_351 = lean_box(0);
x_352 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(x_350, x_351);
x_353 = l_Lean_MessageData_ofList(x_352);
x_354 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_344);
x_356 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(x_336, x_355, x_3, x_4, x_5, x_340);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
x_316 = x_335;
x_317 = x_342;
x_318 = x_2;
x_319 = x_3;
x_320 = x_4;
x_321 = x_5;
x_322 = x_357;
goto block_334;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_358 = lean_ctor_get(x_337, 0);
x_359 = lean_ctor_get(x_337, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_337);
x_360 = lean_box(x_335);
lean_inc(x_291);
x_361 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 3, 2);
lean_closure_set(x_361, 0, x_291);
lean_closure_set(x_361, 1, x_360);
x_362 = lean_unbox(x_358);
lean_dec(x_358);
if (x_362 == 0)
{
x_316 = x_335;
x_317 = x_361;
x_318 = x_2;
x_319 = x_3;
x_320 = x_4;
x_321 = x_5;
x_322 = x_359;
goto block_334;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_363 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15;
lean_inc(x_8);
x_364 = l_Lean_MessageData_ofName(x_8);
x_365 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17;
x_367 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_291);
x_369 = lean_box(0);
x_370 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__8(x_368, x_369);
x_371 = lean_box(0);
x_372 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(x_370, x_371);
x_373 = l_Lean_MessageData_ofList(x_372);
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_363);
x_376 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(x_336, x_375, x_3, x_4, x_5, x_359);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_316 = x_335;
x_317 = x_361;
x_318 = x_2;
x_319 = x_3;
x_320 = x_4;
x_321 = x_5;
x_322 = x_377;
goto block_334;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_295);
lean_dec(x_291);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_378 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18;
x_379 = lean_array_push(x_378, x_1);
if (lean_is_scalar(x_293)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_293;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_292);
return x_380;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_290);
if (x_385 == 0)
{
return x_290;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_290, 0);
x_387 = lean_ctor_get(x_290, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_290);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
block_289:
{
lean_object* x_31; uint8_t x_32; 
lean_inc(x_28);
lean_inc(x_24);
lean_inc(x_17);
lean_inc(x_29);
lean_inc(x_7);
x_31 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(x_21, x_7, x_16, x_29, x_17, x_24, x_28, x_22);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Compiler_LCNF_Code_inferType(x_15, x_29, x_17, x_24, x_28, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_18);
x_39 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_18, x_37, x_29, x_17, x_24, x_28, x_38);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
lean_inc(x_20);
x_43 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_18);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_14);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_12);
lean_ctor_set_uint8(x_43, sizeof(void*)*6 + 1, x_13);
lean_inc(x_43);
x_44 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_43, x_28, x_41);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
lean_inc(x_23);
lean_ctor_set(x_44, 1, x_48);
lean_ctor_set(x_44, 0, x_23);
x_49 = lean_st_mk_ref(x_44, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_25, x_11, x_50, x_29, x_17, x_24, x_28, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_mk_empty_array_with_capacity(x_23);
x_57 = lean_array_get_size(x_54);
lean_inc(x_54);
x_58 = l_Array_toSubarray___redArg(x_54, x_23, x_57);
lean_ctor_set(x_52, 1, x_56);
lean_ctor_set(x_52, 0, x_58);
x_59 = lean_array_size(x_26);
x_60 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_26, x_59, x_25, x_52, x_55);
lean_dec(x_26);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_64);
x_68 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_inc(x_28);
lean_inc(x_17);
x_69 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_67, x_68, x_29, x_17, x_24, x_28, x_62);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_70);
lean_ctor_set(x_7, 0, x_61);
x_74 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_75 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_75, 0, x_8);
lean_ctor_set(x_75, 1, x_9);
lean_ctor_set(x_75, 2, x_10);
lean_ctor_set(x_75, 3, x_54);
lean_ctor_set(x_75, 4, x_7);
lean_ctor_set(x_75, 5, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_75, sizeof(void*)*6 + 1, x_13);
lean_inc(x_75);
x_76 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_75, x_28, x_71);
lean_dec(x_28);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_50, x_77);
lean_dec(x_50);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_17, x_79);
lean_dec(x_17);
lean_dec(x_30);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_84 = lean_array_push(x_83, x_43);
x_85 = lean_array_push(x_84, x_75);
lean_ctor_set(x_80, 0, x_85);
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_87 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_88 = lean_array_push(x_87, x_43);
x_89 = lean_array_push(x_88, x_75);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_free_object(x_61);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_43);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_91 = !lean_is_exclusive(x_69);
if (x_91 == 0)
{
return x_69;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_69, 0);
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_69);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_61, 1);
lean_inc(x_95);
lean_dec(x_61);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_97, 0, x_20);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
x_98 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_inc(x_28);
lean_inc(x_17);
x_99 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_97, x_98, x_29, x_17, x_24, x_28, x_62);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_7, 0, x_104);
x_105 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_106 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_106, 0, x_8);
lean_ctor_set(x_106, 1, x_9);
lean_ctor_set(x_106, 2, x_10);
lean_ctor_set(x_106, 3, x_54);
lean_ctor_set(x_106, 4, x_7);
lean_ctor_set(x_106, 5, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_106, sizeof(void*)*6 + 1, x_13);
lean_inc(x_106);
x_107 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_106, x_28, x_101);
lean_dec(x_28);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_ref_get(x_50, x_108);
lean_dec(x_50);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_17, x_110);
lean_dec(x_17);
lean_dec(x_30);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_115 = lean_array_push(x_114, x_43);
x_116 = lean_array_push(x_115, x_106);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_43);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_118 = lean_ctor_get(x_99, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_120 = x_99;
} else {
 lean_dec_ref(x_99);
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
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; size_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_122 = lean_ctor_get(x_52, 0);
x_123 = lean_ctor_get(x_52, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_52);
x_124 = lean_mk_empty_array_with_capacity(x_23);
x_125 = lean_array_get_size(x_122);
lean_inc(x_122);
x_126 = l_Array_toSubarray___redArg(x_122, x_23, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = lean_array_size(x_26);
x_129 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_26, x_128, x_25, x_127, x_123);
lean_dec(x_26);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_135, 0, x_20);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_132);
x_136 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_inc(x_28);
lean_inc(x_17);
x_137 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_135, x_136, x_29, x_17, x_24, x_28, x_131);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_141, 0, x_140);
if (lean_is_scalar(x_133)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_133;
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_7, 0, x_142);
x_143 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_144 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_144, 0, x_8);
lean_ctor_set(x_144, 1, x_9);
lean_ctor_set(x_144, 2, x_10);
lean_ctor_set(x_144, 3, x_122);
lean_ctor_set(x_144, 4, x_7);
lean_ctor_set(x_144, 5, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_144, sizeof(void*)*6 + 1, x_13);
lean_inc(x_144);
x_145 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_144, x_28, x_139);
lean_dec(x_28);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_st_ref_get(x_50, x_146);
lean_dec(x_50);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_17, x_148);
lean_dec(x_17);
lean_dec(x_30);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_153 = lean_array_push(x_152, x_43);
x_154 = lean_array_push(x_153, x_144);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_151;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_133);
lean_dec(x_122);
lean_dec(x_50);
lean_dec(x_43);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_156 = lean_ctor_get(x_137, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_137, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_158 = x_137;
} else {
 lean_dec_ref(x_137);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_160 = lean_ctor_get(x_44, 1);
lean_inc(x_160);
lean_dec(x_44);
x_161 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
lean_inc(x_23);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_23);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_st_mk_ref(x_162, x_160);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_25, x_11, x_164, x_29, x_17, x_24, x_28, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_mk_empty_array_with_capacity(x_23);
x_171 = lean_array_get_size(x_167);
lean_inc(x_167);
x_172 = l_Array_toSubarray___redArg(x_167, x_23, x_171);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
x_174 = lean_array_size(x_26);
x_175 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_26, x_174, x_25, x_173, x_168);
lean_dec(x_26);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_181, 0, x_20);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_178);
x_182 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_inc(x_28);
lean_inc(x_17);
x_183 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_181, x_182, x_29, x_17, x_24, x_28, x_177);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_187, 0, x_186);
if (lean_is_scalar(x_179)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_179;
}
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_7, 0, x_188);
x_189 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_190 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_190, 0, x_8);
lean_ctor_set(x_190, 1, x_9);
lean_ctor_set(x_190, 2, x_10);
lean_ctor_set(x_190, 3, x_167);
lean_ctor_set(x_190, 4, x_7);
lean_ctor_set(x_190, 5, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_190, sizeof(void*)*6 + 1, x_13);
lean_inc(x_190);
x_191 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_190, x_28, x_185);
lean_dec(x_28);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_st_ref_get(x_164, x_192);
lean_dec(x_164);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_17, x_194);
lean_dec(x_17);
lean_dec(x_30);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_199 = lean_array_push(x_198, x_43);
x_200 = lean_array_push(x_199, x_190);
if (lean_is_scalar(x_197)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_197;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_196);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_179);
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_43);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_202 = lean_ctor_get(x_183, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_183, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_204 = x_183;
} else {
 lean_dec_ref(x_183);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_34);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_206 = !lean_is_exclusive(x_39);
if (x_206 == 0)
{
return x_39;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_39, 0);
x_208 = lean_ctor_get(x_39, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_39);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_34);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_210 = !lean_is_exclusive(x_36);
if (x_210 == 0)
{
return x_36;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_36, 0);
x_212 = lean_ctor_get(x_36, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_36);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_214 = !lean_is_exclusive(x_31);
if (x_214 == 0)
{
return x_31;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_31, 0);
x_216 = lean_ctor_get(x_31, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_31);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_31, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_31, 1);
lean_inc(x_219);
lean_dec(x_31);
x_220 = l_Lean_Compiler_LCNF_Code_inferType(x_15, x_29, x_17, x_24, x_28, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_18);
x_223 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_18, x_221, x_29, x_17, x_24, x_28, x_222);
lean_dec(x_221);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; size_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_box(0);
lean_inc(x_20);
x_227 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_227, 0, x_20);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_224);
lean_ctor_set(x_227, 3, x_18);
lean_ctor_set(x_227, 4, x_218);
lean_ctor_set(x_227, 5, x_14);
lean_ctor_set_uint8(x_227, sizeof(void*)*6, x_12);
lean_ctor_set_uint8(x_227, sizeof(void*)*6 + 1, x_13);
lean_inc(x_227);
x_228 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_227, x_28, x_225);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
lean_inc(x_23);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_23);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_st_mk_ref(x_232, x_229);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_25, x_11, x_234, x_29, x_17, x_24, x_28, x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_mk_empty_array_with_capacity(x_23);
x_241 = lean_array_get_size(x_237);
lean_inc(x_237);
x_242 = l_Array_toSubarray___redArg(x_237, x_23, x_241);
if (lean_is_scalar(x_239)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_239;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
x_244 = lean_array_size(x_26);
x_245 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_26, x_244, x_25, x_243, x_238);
lean_dec(x_26);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
x_251 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_251, 0, x_20);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_248);
x_252 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5;
lean_inc(x_28);
lean_inc(x_17);
x_253 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_251, x_252, x_29, x_17, x_24, x_28, x_247);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_257, 0, x_256);
if (lean_is_scalar(x_249)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_249;
}
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
x_261 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_261, 0, x_8);
lean_ctor_set(x_261, 1, x_9);
lean_ctor_set(x_261, 2, x_10);
lean_ctor_set(x_261, 3, x_237);
lean_ctor_set(x_261, 4, x_259);
lean_ctor_set(x_261, 5, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_261, sizeof(void*)*6 + 1, x_13);
lean_inc(x_261);
x_262 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_261, x_28, x_255);
lean_dec(x_28);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_get(x_234, x_263);
lean_dec(x_234);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_17, x_265);
lean_dec(x_17);
lean_dec(x_30);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
x_270 = lean_array_push(x_269, x_227);
x_271 = lean_array_push(x_270, x_261);
if (lean_is_scalar(x_268)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_268;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_267);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_249);
lean_dec(x_237);
lean_dec(x_234);
lean_dec(x_227);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_273 = lean_ctor_get(x_253, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_253, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_275 = x_253;
} else {
 lean_dec_ref(x_253);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_218);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_277 = lean_ctor_get(x_223, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_223, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_279 = x_223;
} else {
 lean_dec_ref(x_223);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_218);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_281 = lean_ctor_get(x_220, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_220, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_283 = x_220;
} else {
 lean_dec_ref(x_220);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_285 = lean_ctor_get(x_31, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_31, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_287 = x_31;
} else {
 lean_dec_ref(x_31);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_389 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18;
x_390 = lean_array_push(x_389, x_1);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_6);
return x_391;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Compiler_LCNF_Decl_reduceArity(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_append___redArg(x_4, x_19);
lean_dec(x_19);
x_10 = x_21;
x_11 = x_20;
goto block_15;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_10 = x_22;
x_11 = x_23;
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(x_2, x_14, x_15, x_8, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = l_Lean_Compiler_LCNF_reduceArity___closed__0;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_9);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_reduceArity___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ReduceArity", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2433u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0 = _init_l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__0);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__1);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__2);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__3);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__4);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__5);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__6);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__7);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__8();
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__9);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10___redArg___closed__10);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
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
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__18);
l_Lean_Compiler_LCNF_reduceArity___closed__0 = _init_l_Lean_Compiler_LCNF_reduceArity___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity___closed__0);
l_Lean_Compiler_LCNF_reduceArity = _init_l_Lean_Compiler_LCNF_reduceArity();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2433_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
