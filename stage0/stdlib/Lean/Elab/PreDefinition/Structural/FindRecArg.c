// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.FindRecArg
// Imports: public import Lean.Elab.PreDefinition.TerminationMeasure public import Lean.Elab.PreDefinition.Structural.Basic public import Lean.Elab.PreDefinition.Structural.RecArgInfo import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_prettyParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Elab_Structural_prettyParam___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_prettyParam___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_prettyParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_prettyParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Structural_prettyParameterSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_prettyParameterSet___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_prettyParameterSet___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_prettyParameterSet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parameters "};
static const lean_object* l_Lean_Elab_Structural_prettyParameterSet___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_prettyParameterSet___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_prettyParameterSet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_prettyParameterSet___closed__2;
static const lean_string_object l_Lean_Elab_Structural_prettyParameterSet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "parameter "};
static const lean_object* l_Lean_Elab_Structural_prettyParameterSet___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_prettyParameterSet___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_prettyParameterSet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_prettyParameterSet___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Elab.PreDefinition.Structural.FindRecArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Elab.Structural.getRecArgInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "its type is not an inductive"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__1;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "its type "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__3;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = " is an inductive family and indices are not pairwise distinct"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__5;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "{indInfo.name} not in {indInfo.all}"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__7;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "its type is an inductive datatype"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__9;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\nand the datatype parameter"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__11;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\ndepends on the function parameter"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__12 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__13;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "\nwhich is not fixed."};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__14 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__15;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " is an inductive family"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__16 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__17;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nand index"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__18 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__19;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\ndepends on the non index"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__20 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__21;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = " is an inductive family and indices are not variables"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__22 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__23;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__24;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "it is a let-binding"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__25 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__26;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: fixedParamPerm.size = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__27 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__28;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "the index #"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__29 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__30;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " exceeds "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__31 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__31_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__32;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ", the number of parameters"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__33 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__33_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__34;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "it is unchanged in the recursive calls"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__35 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__35_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__36;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not considering parameter "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "cannot use specified measure for structural recursion:"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3;
static const lean_array_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "getRecArgInfos report: "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__1;
static const lean_ctor_object l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value)}};
static const lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_inductiveGroups___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_inductiveGroups___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_inductiveGroups___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Elab.Structural.argsInGroup"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_maxCombinationSize;
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Skipping arguments of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", as "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " has no compatible argument.\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Too many possible combinations of parameters of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " (or "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "please indicate the recursive argument explicitly using `termination_by structural`).\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "no parameters suitable for structural recursion"};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value)}};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__2;
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inductive groups: "};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__4;
static const lean_array_object l_Lean_Elab_Structural_findRecArgCandidates___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__5_value;
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "recArgInfos:"};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__7;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "the type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = " does not have a `.brecOn` recursor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Cannot use "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_tryCandidates___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "failed to infer structural recursion:\n"};
static const lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_tryCandidates___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Structural_tryCandidates___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tryCandidates:\n"};
static const lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_tryCandidates___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParam___closed__1(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParam___closed__0));
v___x_25_ = l_Lean_stringToMessageData(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam(lean_object* v_xs_26_, lean_object* v_i_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = l_Lean_instInhabitedExpr;
v_x_34_ = lean_array_get_borrowed(v___x_33_, v_xs_26_, v_i_27_);
v___x_35_ = l_Lean_Expr_fvarId_x21(v_x_34_);
v___x_36_ = l_Lean_FVarId_getUserName___redArg(v___x_35_, v_a_28_, v_a_30_, v_a_31_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; uint8_t v___x_38_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
lean_dec_ref_known(v___x_36_, 1);
v___x_38_ = l_Lean_Name_hasMacroScopes(v_a_37_);
lean_dec(v_a_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_x_34_);
v___x_39_ = l_Lean_MessageData_ofExpr(v_x_34_);
v___x_40_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_39_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_41_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParam___closed__1, &l_Lean_Elab_Structural_prettyParam___closed__1_once, _init_l_Lean_Elab_Structural_prettyParam___closed__1);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_i_27_, v___x_42_);
v___x_44_ = l_Nat_reprFast(v___x_43_);
v___x_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___x_46_ = l_Lean_MessageData_ofFormat(v___x_45_);
v___x_47_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_41_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_47_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
return v___x_48_;
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_36_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_36_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam___boxed(lean_object* v_xs_57_, lean_object* v_i_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_Structural_prettyParam(v_xs_57_, v_i_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_i_58_);
lean_dec_ref(v_xs_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object* v_k_65_, lean_object* v_b_66_, lean_object* v_c_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
lean_inc(v___y_71_);
lean_inc_ref(v___y_70_);
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
v___x_73_ = lean_apply_7(v_k_65_, v_b_66_, v_c_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object* v_k_74_, lean_object* v_b_75_, lean_object* v_c_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_74_, v_b_75_, v_c_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(lean_object* v_e_83_, lean_object* v_k_84_, uint8_t v_cleanupAnnotations_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___f_91_; uint8_t v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_91_, 0, v_k_84_);
v___x_92_ = 1;
v___x_93_ = 0;
v___x_94_ = lean_box(0);
v___x_95_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_83_, v___x_92_, v___x_93_, v___x_92_, v___x_93_, v___x_94_, v___f_91_, v_cleanupAnnotations_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_95_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_95_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(lean_object* v_e_112_, lean_object* v_k_113_, lean_object* v_cleanupAnnotations_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_120_; lean_object* v_res_121_; 
v_cleanupAnnotations_boxed_120_ = lean_unbox(v_cleanupAnnotations_114_);
v_res_121_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_112_, v_k_113_, v_cleanupAnnotations_boxed_120_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_object* v_00_u03b1_122_, lean_object* v_e_123_, lean_object* v_k_124_, uint8_t v_cleanupAnnotations_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_123_, v_k_124_, v_cleanupAnnotations_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(lean_object* v_00_u03b1_132_, lean_object* v_e_133_, lean_object* v_k_134_, lean_object* v_cleanupAnnotations_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_141_; lean_object* v_res_142_; 
v_cleanupAnnotations_boxed_141_ = lean_unbox(v_cleanupAnnotations_135_);
v_res_142_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(v_00_u03b1_132_, v_e_133_, v_k_134_, v_cleanupAnnotations_boxed_141_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0(lean_object* v_recArgInfo_143_, lean_object* v_xs_144_, lean_object* v_ys_145_, lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_fixedParamPerm_152_; lean_object* v_recArgPos_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_fixedParamPerm_152_ = lean_ctor_get(v_recArgInfo_143_, 1);
lean_inc_ref(v_fixedParamPerm_152_);
v_recArgPos_153_ = lean_ctor_get(v_recArgInfo_143_, 2);
lean_inc(v_recArgPos_153_);
lean_dec_ref(v_recArgInfo_143_);
v___x_154_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_152_, v_xs_144_, v_ys_145_);
v___x_155_ = l_Lean_Elab_Structural_prettyParam(v___x_154_, v_recArgPos_153_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v_recArgPos_153_);
lean_dec_ref(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object* v_recArgInfo_156_, lean_object* v_xs_157_, lean_object* v_ys_158_, lean_object* v_x_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_156_, v_xs_157_, v_ys_158_, v_x_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec_ref(v_x_159_);
lean_dec_ref(v_xs_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object* v_xs_166_, lean_object* v_value_167_, lean_object* v_recArgInfo_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___f_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_174_, 0, v_recArgInfo_168_);
lean_closure_set(v___f_174_, 1, v_xs_166_);
v___x_175_ = 0;
v___x_176_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_167_, v___f_174_, v___x_175_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object* v_xs_177_, lean_object* v_value_178_, lean_object* v_recArgInfo_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_177_, v_value_178_, v_recArgInfo_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_185_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object* v_xs_189_, lean_object* v_as_190_, size_t v_sz_191_, size_t v_i_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = lean_usize_dec_lt(v_i_192_, v_sz_191_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec_ref(v_xs_189_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v_b_193_);
return v___x_200_;
}
else
{
lean_object* v_snd_201_; lean_object* v_snd_202_; lean_object* v_fst_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_285_; 
v_snd_201_ = lean_ctor_get(v_b_193_, 1);
lean_inc(v_snd_201_);
v_snd_202_ = lean_ctor_get(v_snd_201_, 1);
lean_inc(v_snd_202_);
v_fst_203_ = lean_ctor_get(v_b_193_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_b_193_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_b_193_, 1);
lean_dec(v_unused_286_);
v___x_205_ = v_b_193_;
v_isShared_206_ = v_isSharedCheck_285_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_fst_203_);
lean_dec(v_b_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_285_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_fst_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_283_; 
v_fst_207_ = lean_ctor_get(v_snd_201_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_snd_201_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_snd_201_, 1);
lean_dec(v_unused_284_);
v___x_209_ = v_snd_201_;
v_isShared_210_ = v_isSharedCheck_283_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_fst_207_);
lean_dec(v_snd_201_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_283_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_array_211_; lean_object* v_start_212_; lean_object* v_stop_213_; uint8_t v___x_214_; 
v_array_211_ = lean_ctor_get(v_snd_202_, 0);
v_start_212_ = lean_ctor_get(v_snd_202_, 1);
v_stop_213_ = lean_ctor_get(v_snd_202_, 2);
v___x_214_ = lean_nat_dec_lt(v_start_212_, v_stop_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_xs_189_);
if (v_isShared_210_ == 0)
{
v___x_216_ = v___x_209_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_fst_207_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_snd_202_);
v___x_216_ = v_reuseFailAlloc_221_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_216_);
v___x_218_ = v___x_205_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_203_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_279_; 
lean_inc(v_stop_213_);
lean_inc(v_start_212_);
lean_inc_ref(v_array_211_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_snd_202_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; 
v_unused_280_ = lean_ctor_get(v_snd_202_, 2);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_snd_202_, 1);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_snd_202_, 0);
lean_dec(v_unused_282_);
v___x_223_ = v_snd_202_;
v_isShared_224_ = v_isSharedCheck_279_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_snd_202_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_279_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_array_225_; lean_object* v_start_226_; lean_object* v_stop_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v_array_225_ = lean_ctor_get(v_fst_207_, 0);
v_start_226_ = lean_ctor_get(v_fst_207_, 1);
v_stop_227_ = lean_ctor_get(v_fst_207_, 2);
v___x_228_ = lean_array_fget(v_array_211_, v_start_212_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_add(v_start_212_, v___x_229_);
lean_dec(v_start_212_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_230_);
v___x_232_ = v___x_223_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_array_211_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_stop_213_);
v___x_232_ = v_reuseFailAlloc_278_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
uint8_t v___x_233_; 
v___x_233_ = lean_nat_dec_lt(v_start_226_, v_stop_227_);
if (v___x_233_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v___x_228_);
lean_dec_ref(v_xs_189_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_232_);
v___x_235_ = v___x_209_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_fst_207_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_232_);
v___x_235_ = v_reuseFailAlloc_240_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_235_);
v___x_237_ = v___x_205_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_203_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
}
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_274_; 
lean_inc(v_stop_227_);
lean_inc(v_start_226_);
lean_inc_ref(v_array_225_);
v_isSharedCheck_274_ = !lean_is_exclusive(v_fst_207_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_275_ = lean_ctor_get(v_fst_207_, 2);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_fst_207_, 1);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_fst_207_, 0);
lean_dec(v_unused_277_);
v___x_242_ = v_fst_207_;
v_isShared_243_ = v_isSharedCheck_274_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_fst_207_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_274_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_array_fget_borrowed(v_array_225_, v_start_226_);
lean_inc(v___x_244_);
lean_inc_ref(v_xs_189_);
v___x_245_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_189_, v___x_244_, v___x_228_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
v_a_247_ = lean_array_uget_borrowed(v_as_190_, v_i_192_);
v___x_248_ = lean_nat_add(v_start_226_, v___x_229_);
lean_dec(v_start_226_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_248_);
v___x_250_ = v___x_242_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_array_225_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_stop_227_);
v___x_250_ = v_reuseFailAlloc_265_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v_a_246_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v_a_247_);
v___x_253_ = l_Lean_MessageData_ofName(v_a_247_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_array_push(v_fst_203_, v___x_254_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_232_);
lean_ctor_set(v___x_209_, 0, v___x_250_);
v___x_257_ = v___x_209_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_232_);
v___x_257_ = v_reuseFailAlloc_264_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_257_);
lean_ctor_set(v___x_205_, 0, v___x_255_);
v___x_259_ = v___x_205_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
size_t v___x_260_; size_t v___x_261_; 
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_add(v_i_192_, v___x_260_);
v_i_192_ = v___x_261_;
v_b_193_ = v___x_259_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_del_object(v___x_242_);
lean_dec_ref(v___x_232_);
lean_dec(v_stop_227_);
lean_dec(v_start_226_);
lean_dec_ref(v_array_225_);
lean_del_object(v___x_209_);
lean_del_object(v___x_205_);
lean_dec(v_fst_203_);
lean_dec_ref(v_xs_189_);
v_a_266_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_245_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_245_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object* v_xs_287_, lean_object* v_as_288_, lean_object* v_sz_289_, lean_object* v_i_290_, lean_object* v_b_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
size_t v_sz_boxed_297_; size_t v_i_boxed_298_; lean_object* v_res_299_; 
v_sz_boxed_297_ = lean_unbox_usize(v_sz_289_);
lean_dec(v_sz_289_);
v_i_boxed_298_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_287_, v_as_288_, v_sz_boxed_297_, v_i_boxed_298_, v_b_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec_ref(v_as_288_);
return v_res_299_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__1));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__3));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object* v_fnNames_308_, lean_object* v_xs_309_, lean_object* v_values_310_, lean_object* v_recArgInfos_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_array_get_size(v_fnNames_308_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v_l_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; size_t v_sz_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v_l_321_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_322_ = lean_array_get_size(v_values_310_);
v___x_323_ = l_Array_toSubarray___redArg(v_values_310_, v___x_320_, v___x_322_);
v___x_324_ = lean_array_get_size(v_recArgInfos_311_);
v___x_325_ = l_Array_toSubarray___redArg(v_recArgInfos_311_, v___x_320_, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_323_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_l_321_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v_sz_328_ = lean_array_size(v_fnNames_308_);
v___x_329_ = ((size_t)0ULL);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_309_, v_fnNames_308_, v_sz_328_, v___x_329_, v___x_327_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_350_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_350_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fst_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_348_; 
v_fst_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_a_331_, 1);
lean_dec(v_unused_349_);
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_fst_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_339_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__2, &l_Lean_Elab_Structural_prettyParameterSet___closed__2_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2);
v___x_340_ = lean_array_to_list(v_fst_335_);
v___x_341_ = l_Lean_MessageData_andList(v___x_340_);
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 7);
lean_ctor_set(v___x_337_, 1, v___x_341_);
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_343_ = v___x_337_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_343_);
v___x_345_ = v___x_333_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_330_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_330_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_359_ = l_Lean_instInhabitedExpr;
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_array_get(v___x_359_, v_values_310_, v___x_360_);
lean_dec_ref(v_values_310_);
v___x_362_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_363_ = lean_array_get(v___x_362_, v_recArgInfos_311_, v___x_360_);
lean_dec_ref(v_recArgInfos_311_);
v___x_364_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_309_, v___x_361_, v___x_363_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_369_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__4, &l_Lean_Elab_Structural_prettyParameterSet___closed__4_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object* v_fnNames_375_, lean_object* v_xs_376_, lean_object* v_values_377_, lean_object* v_recArgInfos_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_375_, v_xs_376_, v_values_377_, v_recArgInfos_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec_ref(v_fnNames_375_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object* v_xs_385_, lean_object* v_v_386_, lean_object* v_i_387_){
_start:
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = lean_array_get_size(v_xs_385_);
v___x_389_ = lean_nat_dec_lt(v_i_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_dec(v_i_387_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_array_fget_borrowed(v_xs_385_, v_i_387_);
v___x_392_ = lean_expr_eqv(v___x_391_, v_v_386_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_i_387_, v___x_393_);
lean_dec(v_i_387_);
v_i_387_ = v___x_394_;
goto _start;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_i_387_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_397_, lean_object* v_v_398_, lean_object* v_i_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_397_, v_v_398_, v_i_399_);
lean_dec_ref(v_v_398_);
lean_dec_ref(v_xs_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object* v_xs_401_, lean_object* v_v_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_401_, v_v_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object* v_xs_405_, lean_object* v_v_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_405_, v_v_406_);
lean_dec_ref(v_v_406_);
lean_dec_ref(v_xs_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object* v_xs_408_, lean_object* v_v_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_408_, v_v_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_val_412_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_410_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v___x_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object* v_xs_420_, lean_object* v_v_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_420_, v_v_421_);
lean_dec_ref(v_v_421_);
lean_dec_ref(v_xs_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object* v_xs_423_, lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_){
_start:
{
lean_object* v_a_429_; uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_433_ == 0)
{
return v_b_427_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v___x_435_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_423_, v_a_434_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; uint8_t v___x_437_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = lean_nat_dec_lt(v_val_436_, v_b_427_);
if (v___x_437_ == 0)
{
lean_dec(v_val_436_);
v_a_429_ = v_b_427_;
goto v___jp_428_;
}
else
{
lean_dec(v_b_427_);
v_a_429_ = v_val_436_;
goto v___jp_428_;
}
}
else
{
lean_dec(v___x_435_);
v_a_429_ = v_b_427_;
goto v___jp_428_;
}
}
v___jp_428_:
{
size_t v___x_430_; size_t v___x_431_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_426_, v___x_430_);
v_i_426_ = v___x_431_;
v_b_427_ = v_a_429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object* v_xs_438_, lean_object* v_as_439_, lean_object* v_sz_440_, lean_object* v_i_441_, lean_object* v_b_442_){
_start:
{
size_t v_sz_boxed_443_; size_t v_i_boxed_444_; lean_object* v_res_445_; 
v_sz_boxed_443_ = lean_unbox_usize(v_sz_440_);
lean_dec(v_sz_440_);
v_i_boxed_444_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_438_, v_as_439_, v_sz_boxed_443_, v_i_boxed_444_, v_b_442_);
lean_dec_ref(v_as_439_);
lean_dec_ref(v_xs_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object* v_xs_446_, lean_object* v_indices_447_){
_start:
{
lean_object* v_minPos_448_; size_t v_sz_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_minPos_448_ = lean_array_get_size(v_xs_446_);
v_sz_449_ = lean_array_size(v_indices_447_);
v___x_450_ = ((size_t)0ULL);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_446_, v_indices_447_, v_sz_449_, v___x_450_, v_minPos_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* v_xs_452_, lean_object* v_indices_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_452_, v_indices_453_);
lean_dec_ref(v_indices_453_);
lean_dec_ref(v_xs_452_);
return v_res_454_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object* v_x_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_457_);
lean_dec(v_x_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object* v_fvarId_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_instBEqFVarId_beq(v_fvarId_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec(v_fvarId_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_468_; lean_object* v___x_469_; 
v_cellCount_468_ = lean_unsigned_to_nat(16u);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_470_; lean_object* v___x_471_; 
v_cellCount_470_ = lean_unsigned_to_nat(16u);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_472_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_473_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___x_472_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_476_, lean_object* v_fvarId_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; uint8_t v_fst_482_; lean_object* v_mctx_483_; lean_object* v___y_501_; lean_object* v_mctx_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_mctx_506_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref_n(v_mctx_506_, 2);
lean_dec(v___x_480_);
v___f_507_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_508_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_508_, 0, v_fvarId_477_);
v___x_509_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__3);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_mctx_506_);
v___x_511_ = l_Lean_Expr_hasFVar(v_e_476_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_Expr_hasMVar(v_e_476_);
if (v___x_512_ == 0)
{
lean_dec_ref_known(v___x_510_, 2);
lean_dec_ref(v___f_508_);
lean_dec_ref(v_e_476_);
v_fst_482_ = v___x_512_;
v_mctx_483_ = v_mctx_506_;
goto v___jp_481_;
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_mctx_506_);
v___x_513_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_508_, v___f_507_, v_e_476_, v___x_510_);
v___y_501_ = v___x_513_;
goto v___jp_500_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_mctx_506_);
v___x_514_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_508_, v___f_507_, v_e_476_, v___x_510_);
v___y_501_ = v___x_514_;
goto v___jp_500_;
}
v___jp_481_:
{
lean_object* v___x_484_; lean_object* v_cache_485_; lean_object* v_zetaDeltaFVarIds_486_; lean_object* v_postponed_487_; lean_object* v_diag_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_498_; 
v___x_484_ = lean_st_ref_take(v___y_478_);
v_cache_485_ = lean_ctor_get(v___x_484_, 1);
v_zetaDeltaFVarIds_486_ = lean_ctor_get(v___x_484_, 2);
v_postponed_487_ = lean_ctor_get(v___x_484_, 3);
v_diag_488_ = lean_ctor_get(v___x_484_, 4);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v___x_484_, 0);
lean_dec(v_unused_499_);
v___x_490_ = v___x_484_;
v_isShared_491_ = v_isSharedCheck_498_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_diag_488_);
lean_inc(v_postponed_487_);
lean_inc(v_zetaDeltaFVarIds_486_);
lean_inc(v_cache_485_);
lean_dec(v___x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_498_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_mctx_483_);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_mctx_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_cache_485_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_zetaDeltaFVarIds_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_postponed_487_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_diag_488_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_st_ref_put(v___y_478_, v___x_493_);
v___x_495_ = lean_box(v_fst_482_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
v___jp_500_:
{
lean_object* v_snd_502_; lean_object* v_fst_503_; lean_object* v_mctx_504_; uint8_t v___x_505_; 
v_snd_502_ = lean_ctor_get(v___y_501_, 1);
lean_inc(v_snd_502_);
v_fst_503_ = lean_ctor_get(v___y_501_, 0);
lean_inc(v_fst_503_);
lean_dec_ref(v___y_501_);
v_mctx_504_ = lean_ctor_get(v_snd_502_, 1);
lean_inc_ref(v_mctx_504_);
lean_dec(v_snd_502_);
v___x_505_ = lean_unbox(v_fst_503_);
lean_dec(v_fst_503_);
v_fst_482_ = v___x_505_;
v_mctx_483_ = v_mctx_504_;
goto v___jp_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_515_, lean_object* v_fvarId_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_515_, v_fvarId_516_, v___y_517_);
lean_dec(v___y_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_520_, lean_object* v_fvarId_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_520_, v_fvarId_521_, v___y_523_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_528_, lean_object* v_fvarId_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_528_, v_fvarId_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_535_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_536_, lean_object* v_as_537_, size_t v_i_538_, size_t v_stop_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_eq(v_i_538_, v_stop_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_array_uget_borrowed(v_as_537_, v_i_538_);
v___x_542_ = lean_expr_eqv(v_a_536_, v___x_541_);
if (v___x_542_ == 0)
{
size_t v___x_543_; size_t v___x_544_; 
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_538_, v___x_543_);
v_i_538_ = v___x_544_;
goto _start;
}
else
{
return v___x_542_;
}
}
else
{
uint8_t v___x_546_; 
v___x_546_ = 0;
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_547_, lean_object* v_as_548_, lean_object* v_i_549_, lean_object* v_stop_550_){
_start:
{
size_t v_i_boxed_551_; size_t v_stop_boxed_552_; uint8_t v_res_553_; lean_object* v_r_554_; 
v_i_boxed_551_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_stop_boxed_552_ = lean_unbox_usize(v_stop_550_);
lean_dec(v_stop_550_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_547_, v_as_548_, v_i_boxed_551_, v_stop_boxed_552_);
lean_dec_ref(v_as_548_);
lean_dec_ref(v_a_547_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_array_get_size(v_as_555_);
v___x_559_ = lean_nat_dec_lt(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
return v___x_559_;
}
else
{
if (v___x_559_ == 0)
{
return v___x_559_;
}
else
{
size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_558_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_556_, v_as_555_, v___x_560_, v___x_561_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_563_, lean_object* v_a_564_){
_start:
{
uint8_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_563_, v_a_564_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_as_563_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_570_, lean_object* v_indices_571_, lean_object* v_a_572_, lean_object* v_as_573_, size_t v_sz_574_, size_t v_i_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_a_572_);
lean_dec_ref(v_a_570_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_b_576_);
return v___x_583_;
}
else
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref(v_b_576_);
v_a_584_ = lean_array_uget_borrowed(v_as_573_, v_i_575_);
v___x_585_ = l_Lean_Expr_fvarId_x21(v_a_584_);
lean_inc_ref(v_a_570_);
v___x_586_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_570_, v___x_585_, v___y_578_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_607_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_607_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_607_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_607_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_a_592_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_598_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_571_, v_a_584_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
if (v___x_599_ == 0)
{
lean_del_object(v___x_589_);
v_a_592_ = v___x_597_;
goto v___jp_591_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref(v_a_570_);
lean_inc(v_a_584_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_a_572_);
lean_ctor_set(v___x_600_, 1, v_a_584_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_596_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_603_);
v___x_605_ = v___x_589_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_del_object(v___x_589_);
lean_dec(v_a_587_);
v_a_592_ = v___x_597_;
goto v___jp_591_;
}
v___jp_591_:
{
size_t v___x_593_; size_t v___x_594_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_575_, v___x_593_);
lean_inc_ref(v_a_592_);
v_i_575_ = v___x_594_;
v_b_576_ = v_a_592_;
goto _start;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_a_572_);
lean_dec_ref(v_a_570_);
v_a_608_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_586_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_586_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_616_, lean_object* v_indices_617_, lean_object* v_a_618_, lean_object* v_as_619_, lean_object* v_sz_620_, lean_object* v_i_621_, lean_object* v_b_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
size_t v_sz_boxed_628_; size_t v_i_boxed_629_; lean_object* v_res_630_; 
v_sz_boxed_628_ = lean_unbox_usize(v_sz_620_);
lean_dec(v_sz_620_);
v_i_boxed_629_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_616_, v_indices_617_, v_a_618_, v_as_619_, v_sz_boxed_628_, v_i_boxed_629_, v_b_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_as_619_);
lean_dec_ref(v_indices_617_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_631_, lean_object* v_indices_632_, lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_636_);
return v___x_643_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_645_; 
lean_dec_ref(v_b_636_);
v_a_644_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
lean_inc(v___y_640_);
lean_inc_ref(v___y_639_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v_a_644_);
v___x_645_ = lean_infer_type(v_a_644_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___x_648_; size_t v_sz_649_; size_t v___x_650_; lean_object* v___x_651_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = lean_box(0);
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_649_ = lean_array_size(v_ys_631_);
v___x_650_ = ((size_t)0ULL);
lean_inc(v_a_644_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_646_, v_indices_632_, v_a_644_, v_ys_631_, v_sz_649_, v___x_650_, v___x_648_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_671_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_671_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_671_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_671_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_669_; 
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_a_652_, 1);
lean_dec(v_unused_670_);
v___x_658_ = v_a_652_;
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_fst_656_);
lean_dec(v_a_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
if (lean_obj_tag(v_fst_656_) == 0)
{
size_t v___x_660_; size_t v___x_661_; 
lean_del_object(v___x_658_);
lean_del_object(v___x_654_);
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_add(v_i_635_, v___x_660_);
v_i_635_ = v___x_661_;
v_b_636_ = v___x_648_;
goto _start;
}
else
{
lean_object* v___x_664_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_647_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_647_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_664_);
v___x_666_ = v___x_654_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
else
{
return v___x_651_;
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_645_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_645_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_680_, lean_object* v_indices_681_, lean_object* v_as_682_, lean_object* v_sz_683_, lean_object* v_i_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
size_t v_sz_boxed_691_; size_t v_i_boxed_692_; lean_object* v_res_693_; 
v_sz_boxed_691_ = lean_unbox_usize(v_sz_683_);
lean_dec(v_sz_683_);
v_i_boxed_692_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_680_, v_indices_681_, v_as_682_, v_sz_boxed_691_, v_i_boxed_692_, v_b_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_as_682_);
lean_dec_ref(v_indices_681_);
lean_dec_ref(v_ys_680_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_694_, lean_object* v_ys_695_, lean_object* v_as_696_, size_t v_sz_697_, size_t v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_b_699_);
return v___x_706_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_708_; 
lean_dec_ref(v_b_699_);
v_a_707_ = lean_array_uget_borrowed(v_as_696_, v_i_698_);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v_a_707_);
v___x_708_ = lean_infer_type(v_a_707_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; size_t v_sz_712_; size_t v___x_713_; lean_object* v___x_714_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_box(0);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_712_ = lean_array_size(v_ys_695_);
v___x_713_ = ((size_t)0ULL);
lean_inc(v_a_707_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_709_, v_indices_694_, v_a_707_, v_ys_695_, v_sz_712_, v___x_713_, v___x_711_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_734_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_734_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_734_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_734_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_732_; 
v_fst_719_ = lean_ctor_get(v_a_715_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_715_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_a_715_, 1);
lean_dec(v_unused_733_);
v___x_721_ = v_a_715_;
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_fst_719_);
lean_dec(v_a_715_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
if (lean_obj_tag(v_fst_719_) == 0)
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
lean_del_object(v___x_721_);
lean_del_object(v___x_717_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_698_, v___x_723_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_695_, v_indices_694_, v_as_696_, v_sz_697_, v___x_724_, v___x_711_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_725_;
}
else
{
lean_object* v___x_727_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_710_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_710_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_727_);
v___x_729_ = v___x_717_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
else
{
return v___x_714_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_708_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_708_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_743_, lean_object* v_ys_744_, lean_object* v_as_745_, lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_755_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_743_, v_ys_744_, v_as_745_, v_sz_boxed_754_, v_i_boxed_755_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_as_745_);
lean_dec_ref(v_ys_744_);
lean_dec_ref(v_indices_743_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_757_, lean_object* v_indices_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; size_t v_sz_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_764_ = lean_box(0);
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_766_ = lean_array_size(v_indices_758_);
v___x_767_ = ((size_t)0ULL);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_758_, v_ys_757_, v_indices_758_, v_sz_766_, v___x_767_, v___x_765_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_781_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_781_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fst_773_; 
v_fst_773_ = lean_ctor_get(v_a_769_, 0);
lean_inc(v_fst_773_);
lean_dec(v_a_769_);
if (lean_obj_tag(v_fst_773_) == 0)
{
lean_object* v___x_775_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_764_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_764_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_val_777_; lean_object* v___x_779_; 
v_val_777_ = lean_ctor_get(v_fst_773_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_fst_773_, 1);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v_val_777_);
v___x_779_ = v___x_771_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_val_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_768_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_768_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_790_, lean_object* v_indices_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_790_, v_indices_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec_ref(v_indices_791_);
lean_dec_ref(v_ys_790_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_798_, lean_object* v_as_799_, size_t v_sz_800_, size_t v_i_801_, lean_object* v_b_802_, lean_object* v___y_803_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v_a_798_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_b_802_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v_b_802_);
v_a_807_ = lean_array_uget_borrowed(v_as_799_, v_i_801_);
v___x_808_ = l_Lean_Expr_fvarId_x21(v_a_807_);
lean_inc_ref(v_a_798_);
v___x_809_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_798_, v___x_808_, v___y_803_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_827_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_827_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_827_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_827_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; 
lean_del_object(v___x_812_);
v___x_816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_801_, v___x_817_);
v_i_801_ = v___x_818_;
v_b_802_ = v___x_816_;
goto _start;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
lean_inc(v_a_807_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_798_);
lean_ctor_set(v___x_820_, 1, v_a_807_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_814_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_823_);
v___x_825_ = v___x_812_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v_a_798_);
v_a_828_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_809_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_809_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_836_, lean_object* v_as_837_, lean_object* v_sz_838_, lean_object* v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
size_t v_sz_boxed_843_; size_t v_i_boxed_844_; lean_object* v_res_845_; 
v_sz_boxed_843_ = lean_unbox_usize(v_sz_838_);
lean_dec(v_sz_838_);
v_i_boxed_844_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_836_, v_as_837_, v_sz_boxed_843_, v_i_boxed_844_, v_b_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v_as_837_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_846_, lean_object* v_as_847_, size_t v_sz_848_, size_t v_i_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_lt(v_i_849_, v_sz_848_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v_b_850_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_a_860_; size_t v_sz_861_; size_t v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v_b_850_);
v___x_858_ = lean_box(0);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_860_ = lean_array_uget_borrowed(v_as_847_, v_i_849_);
v_sz_861_ = lean_array_size(v_ys_846_);
v___x_862_ = ((size_t)0ULL);
lean_inc(v_a_860_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_860_, v_ys_846_, v_sz_861_, v___x_862_, v___x_859_, v___y_852_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_883_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_883_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_881_; 
v_fst_868_ = lean_ctor_get(v_a_864_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_864_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v_a_864_, 1);
lean_dec(v_unused_882_);
v___x_870_ = v_a_864_;
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_fst_868_);
lean_dec(v_a_864_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
if (lean_obj_tag(v_fst_868_) == 0)
{
size_t v___x_872_; size_t v___x_873_; 
lean_del_object(v___x_870_);
lean_del_object(v___x_866_);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_849_, v___x_872_);
v_i_849_ = v___x_873_;
v_b_850_ = v___x_859_;
goto _start;
}
else
{
lean_object* v___x_876_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_858_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_868_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_858_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_876_);
v___x_878_ = v___x_866_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
else
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_884_, lean_object* v_as_885_, lean_object* v_sz_886_, lean_object* v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
size_t v_sz_boxed_894_; size_t v_i_boxed_895_; lean_object* v_res_896_; 
v_sz_boxed_894_ = lean_unbox_usize(v_sz_886_);
lean_dec(v_sz_886_);
v_i_boxed_895_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_884_, v_as_885_, v_sz_boxed_894_, v_i_boxed_895_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v_as_885_);
lean_dec_ref(v_ys_884_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_897_, lean_object* v_indParams_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_904_ = lean_box(0);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_906_ = lean_array_size(v_indParams_898_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_897_, v_indParams_898_, v_sz_906_, v___x_907_, v___x_905_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_fst_913_; 
v_fst_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_fst_913_);
lean_dec(v_a_909_);
if (lean_obj_tag(v_fst_913_) == 0)
{
lean_object* v___x_915_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_904_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_904_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v_val_917_; lean_object* v___x_919_; 
v_val_917_ = lean_ctor_get(v_fst_913_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v_fst_913_, 1);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_val_917_);
v___x_919_ = v___x_911_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_val_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_908_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_908_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_930_, lean_object* v_indParams_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_930_, v_indParams_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec_ref(v_indParams_931_);
lean_dec_ref(v_ys_930_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_938_, lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_938_, v_as_939_, v_sz_940_, v_i_941_, v_b_942_, v___y_944_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_949_, lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_960_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_949_, v_as_950_, v_sz_boxed_959_, v_i_boxed_960_, v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_panic_fn_borrowed(v___x_963_, v_msg_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_6888__overap_973_; lean_object* v___x_974_; 
v___f_972_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6888__overap_973_ = lean_panic_fn_borrowed(v___f_972_, v_msg_966_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_974_ = lean_apply_5(v___x_6888__overap_973_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, lean_box(0));
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_ref_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_ref_988_ = lean_ctor_get(v___y_985_, 5);
v___x_989_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_998_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_inc(v_ref_988_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_ref_988_);
lean_ctor_set(v___x_994_, 1, v_a_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 1);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_1010_ = lean_unsigned_to_nat(107u);
v___x_1011_ = lean_unsigned_to_nat(97u);
v___x_1012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1014_ = l_mkPanicMessageWithDecl(v___x_1013_, v___x_1012_, v___x_1011_, v___x_1010_, v___x_1009_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1015_, size_t v_sz_1016_, size_t v_i_1017_, lean_object* v_bs_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_lt(v_i_1017_, v_sz_1016_);
if (v___x_1019_ == 0)
{
return v_bs_1018_;
}
else
{
lean_object* v_v_1020_; lean_object* v___x_1021_; lean_object* v_bs_x27_1022_; lean_object* v___y_1024_; lean_object* v___x_1029_; 
v_v_1020_ = lean_array_uget(v_bs_1018_, v_i_1017_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v_bs_x27_1022_ = lean_array_uset(v_bs_1018_, v_i_1017_, v___x_1021_);
v___x_1029_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_1015_, v_v_1020_);
lean_dec(v_v_1020_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3);
v___x_1031_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1030_);
v___y_1024_ = v___x_1031_;
goto v___jp_1023_;
}
else
{
lean_object* v_val_1032_; 
v_val_1032_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1029_, 1);
v___y_1024_ = v_val_1032_;
goto v___jp_1023_;
}
v___jp_1023_:
{
size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1017_, v___x_1025_);
v___x_1027_ = lean_array_uset(v_bs_x27_1022_, v_i_1017_, v___y_1024_);
v_i_1017_ = v___x_1026_;
v_bs_1018_ = v___x_1027_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_bs_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1033_, v_sz_boxed_1037_, v_i_boxed_1038_, v_bs_1036_);
lean_dec_ref(v_xs_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(lean_object* v_as_1040_, lean_object* v_a_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_zero_1043_; uint8_t v_isZero_1044_; 
v_zero_1043_ = lean_unsigned_to_nat(0u);
v_isZero_1044_ = lean_nat_dec_eq(v_x_1042_, v_zero_1043_);
if (v_isZero_1044_ == 1)
{
lean_dec(v_x_1042_);
return v_isZero_1044_;
}
else
{
lean_object* v_one_1045_; lean_object* v_n_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_one_1045_ = lean_unsigned_to_nat(1u);
v_n_1046_ = lean_nat_sub(v_x_1042_, v_one_1045_);
lean_dec(v_x_1042_);
v___x_1047_ = lean_array_fget_borrowed(v_as_1040_, v_n_1046_);
v___x_1048_ = lean_expr_eqv(v_a_1041_, v___x_1047_);
if (v___x_1048_ == 0)
{
v_x_1042_ = v_n_1046_;
goto _start;
}
else
{
lean_dec(v_n_1046_);
return v_isZero_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_as_1050_, lean_object* v_a_1051_, lean_object* v_x_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1050_, v_a_1051_, v_x_1052_);
lean_dec_ref(v_a_1051_);
lean_dec_ref(v_as_1050_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(lean_object* v_as_1055_, lean_object* v_i_1056_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_array_get_size(v_as_1055_);
v___x_1058_ = lean_nat_dec_lt(v_i_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; 
lean_dec(v_i_1056_);
v___x_1059_ = 1;
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_fget_borrowed(v_as_1055_, v_i_1056_);
lean_inc(v_i_1056_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1055_, v___x_1060_, v_i_1056_);
if (v___x_1061_ == 0)
{
lean_dec(v_i_1056_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_i_1056_, v___x_1062_);
lean_dec(v_i_1056_);
v_i_1056_ = v___x_1063_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(lean_object* v_as_1065_, lean_object* v_i_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1065_, v_i_1066_);
lean_dec_ref(v_as_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_as_1069_){
_start:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1069_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_as_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_as_1072_);
lean_dec_ref(v_as_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_as_1075_, size_t v_i_1076_, size_t v_stop_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1076_, v_stop_1077_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = 1;
v___x_1080_ = lean_array_uget_borrowed(v_as_1075_, v_i_1076_);
v___x_1081_ = l_Lean_Expr_isFVar(v___x_1080_);
if (v___x_1081_ == 0)
{
return v___x_1079_;
}
else
{
if (v___x_1078_ == 0)
{
size_t v___x_1082_; size_t v___x_1083_; 
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1076_, v___x_1082_);
v_i_1076_ = v___x_1083_;
goto _start;
}
else
{
return v___x_1079_;
}
}
}
else
{
uint8_t v___x_1085_; 
v___x_1085_ = 0;
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_stop_1088_){
_start:
{
size_t v_i_boxed_1089_; size_t v_stop_boxed_1090_; uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_i_boxed_1089_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_stop_boxed_1090_ = lean_unbox_usize(v_stop_1088_);
lean_dec(v_stop_1088_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_as_1086_, v_i_boxed_1089_, v_stop_boxed_1090_);
lean_dec_ref(v_as_1086_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(lean_object* v_xs_1093_, lean_object* v_v_1094_, lean_object* v_i_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_array_get_size(v_xs_1093_);
v___x_1097_ = lean_nat_dec_lt(v_i_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_i_1095_);
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_array_fget_borrowed(v_xs_1093_, v_i_1095_);
v___x_1100_ = lean_name_eq(v___x_1099_, v_v_1094_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_nat_add(v_i_1095_, v___x_1101_);
lean_dec(v_i_1095_);
v_i_1095_ = v___x_1102_;
goto _start;
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_i_1095_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(lean_object* v_xs_1105_, lean_object* v_v_1106_, lean_object* v_i_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1105_, v_v_1106_, v_i_1107_);
lean_dec(v_v_1106_);
lean_dec_ref(v_xs_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(lean_object* v_xs_1109_, lean_object* v_v_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1109_, v_v_1110_, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(lean_object* v_xs_1113_, lean_object* v_v_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1113_, v_v_1114_);
lean_dec(v_v_1114_);
lean_dec_ref(v_xs_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_xs_1116_, lean_object* v_v_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1116_, v_v_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
else
{
lean_object* v_val_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_val_1120_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_val_1120_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_val_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_xs_1128_, lean_object* v_v_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_xs_1128_, v_v_1129_);
lean_dec(v_v_1129_);
lean_dec_ref(v_xs_1128_);
return v_res_1130_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1142_ = lean_unsigned_to_nat(59u);
v___x_1143_ = lean_unsigned_to_nat(96u);
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1146_ = l_mkPanicMessageWithDecl(v___x_1145_, v___x_1144_, v___x_1143_, v___x_1142_, v___x_1141_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1171_; lean_object* v_dummy_1172_; 
v___x_1171_ = lean_box(0);
v_dummy_1172_ = l_Lean_Expr_sort___override(v___x_1171_);
return v_dummy_1172_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1178_ = lean_unsigned_to_nat(2u);
v___x_1179_ = lean_unsigned_to_nat(68u);
v___x_1180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1182_ = l_mkPanicMessageWithDecl(v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_, v___x_1177_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1195_, lean_object* v_fixedParamPerm_1196_, lean_object* v_xs_1197_, lean_object* v_i_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v_lower_1343_; lean_object* v_upper_1344_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_array_get_size(v_fixedParamPerm_1196_);
v___x_1430_ = lean_array_get_size(v_xs_1197_);
v___x_1431_ = lean_nat_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___x_1432_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1433_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1432_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_nat_dec_lt(v_i_1198_, v___x_1430_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v_i_1198_, v___x_1436_);
lean_dec(v_i_1198_);
v___x_1438_ = l_Nat_reprFast(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1435_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Nat_reprFast(v___x_1430_);
v___x_1445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
v___x_1446_ = l_Lean_MessageData_ofFormat(v___x_1445_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1443_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1449_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
return v___x_1450_;
}
else
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1196_, v_i_1198_);
if (v___x_1451_ == 0)
{
v___y_1402_ = v_a_1199_;
v___y_1403_ = v_a_1200_;
v___y_1404_ = v_a_1201_;
v___y_1405_ = v_a_1202_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1453_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1452_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1210_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1209_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
v___jp_1211_:
{
uint8_t v___x_1223_; 
v___x_1223_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1221_);
if (v___x_1223_ == 0)
{
lean_object* v_name_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_name_1224_ = lean_ctor_get(v___y_1222_, 0);
lean_inc(v_name_1224_);
lean_dec_ref(v___y_1222_);
v___x_1225_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1226_ = l_Lean_MessageData_ofName(v_name_1224_);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_indentExpr(v___y_1219_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1231_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1196_, v_xs_1197_);
v___x_1234_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1233_, v___y_1221_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1233_, v___y_1218_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
lean_dec_ref(v___x_1233_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1287_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1287_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1287_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
if (lean_obj_tag(v_a_1237_) == 0)
{
lean_object* v_name_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___y_1219_);
v_name_1241_ = lean_ctor_get(v___y_1222_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___y_1222_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; lean_object* v_unused_1263_; 
v_unused_1262_ = lean_ctor_get(v___y_1222_, 2);
lean_dec(v_unused_1262_);
v_unused_1263_ = lean_ctor_get(v___y_1222_, 1);
lean_dec(v_unused_1263_);
v___x_1243_ = v___y_1222_;
v_isShared_1244_ = v_isSharedCheck_1261_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_name_1241_);
lean_dec(v___y_1222_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1261_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_array_mk(v___y_1214_);
v___x_1246_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___x_1245_, v_name_1241_);
lean_dec(v_name_1241_);
lean_dec_ref(v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 1)
{
lean_object* v_val_1247_; size_t v_sz_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_sz_1248_ = lean_array_size(v___y_1221_);
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1197_, v_sz_1248_, v___x_1249_, v___y_1221_);
v___x_1251_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1217_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 2, v___y_1218_);
lean_ctor_set(v___x_1243_, 1, v___y_1212_);
lean_ctor_set(v___x_1243_, 0, v___x_1251_);
v___x_1253_ = v___x_1243_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___y_1212_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v___y_1218_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1254_, 0, v_fnName_1195_);
lean_ctor_set(v___x_1254_, 1, v_fixedParamPerm_1196_);
lean_ctor_set(v___x_1254_, 2, v_i_1198_);
lean_ctor_set(v___x_1254_, 3, v___x_1250_);
lean_ctor_set(v___x_1254_, 4, v___x_1253_);
lean_ctor_set(v___x_1254_, 5, v_val_1247_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1254_);
v___x_1256_ = v___x_1239_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v___x_1246_);
lean_del_object(v___x_1243_);
lean_del_object(v___x_1239_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___x_1259_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1260_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1259_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
return v___x_1260_;
}
}
}
else
{
lean_object* v_val_1264_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1239_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_val_1264_ = lean_ctor_get(v_a_1237_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v_a_1237_, 1);
v_fst_1265_ = lean_ctor_get(v_val_1264_, 0);
v_snd_1266_ = lean_ctor_get(v_val_1264_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_val_1264_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1268_ = v_val_1264_;
v_isShared_1269_ = v_isSharedCheck_1286_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_val_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1286_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1270_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1271_ = l_Lean_indentExpr(v___y_1219_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 7);
lean_ctor_set(v___x_1268_, 1, v___x_1271_);
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1274_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_indentExpr(v_fst_1265_);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_indentExpr(v_snd_1266_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1283_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
return v___x_1284_;
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_a_1288_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1236_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1236_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_val_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_val_1296_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_a_1235_, 1);
v_fst_1297_ = lean_ctor_get(v_val_1296_, 0);
v_snd_1298_ = lean_ctor_get(v_val_1296_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_val_1296_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1300_ = v_val_1296_;
v_isShared_1301_ = v_isSharedCheck_1321_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_inc(v_fst_1297_);
lean_dec(v_val_1296_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1321_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_name_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v_name_1302_ = lean_ctor_get(v___y_1222_, 0);
lean_inc(v_name_1302_);
lean_dec_ref(v___y_1222_);
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1304_ = l_Lean_MessageData_ofName(v_name_1302_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 7);
lean_ctor_set(v___x_1300_, 1, v___x_1304_);
lean_ctor_set(v___x_1300_, 0, v___x_1303_);
v___x_1306_ = v___x_1300_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1307_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_indentExpr(v___y_1219_);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_indentExpr(v_fst_1297_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_indentExpr(v_snd_1298_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1318_, v___y_1215_, v___y_1220_, v___y_1213_, v___y_1216_);
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1214_);
lean_dec(v___y_1212_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_a_1322_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1234_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1234_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
v___jp_1330_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1345_ = l_Array_toSubarray___redArg(v___y_1331_, v_lower_1343_, v_upper_1344_);
v___x_1346_ = l_Subarray_copy___redArg(v___x_1345_);
v___x_1347_ = lean_array_get_size(v___x_1346_);
v___x_1348_ = lean_nat_dec_lt(v___y_1338_, v___x_1347_);
lean_dec(v___y_1338_);
if (v___x_1348_ == 0)
{
v___y_1212_ = v___y_1332_;
v___y_1213_ = v___y_1340_;
v___y_1214_ = v___y_1341_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1335_;
v___y_1218_ = v___y_1336_;
v___y_1219_ = v___y_1337_;
v___y_1220_ = v___y_1342_;
v___y_1221_ = v___x_1346_;
v___y_1222_ = v___y_1339_;
goto v___jp_1211_;
}
else
{
if (v___x_1348_ == 0)
{
v___y_1212_ = v___y_1332_;
v___y_1213_ = v___y_1340_;
v___y_1214_ = v___y_1341_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1335_;
v___y_1218_ = v___y_1336_;
v___y_1219_ = v___y_1337_;
v___y_1220_ = v___y_1342_;
v___y_1221_ = v___x_1346_;
v___y_1222_ = v___y_1339_;
goto v___jp_1211_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1347_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v___x_1346_, v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
v___y_1212_ = v___y_1332_;
v___y_1213_ = v___y_1340_;
v___y_1214_ = v___y_1341_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1335_;
v___y_1218_ = v___y_1336_;
v___y_1219_ = v___y_1337_;
v___y_1220_ = v___y_1342_;
v___y_1221_ = v___x_1346_;
v___y_1222_ = v___y_1339_;
goto v___jp_1211_;
}
else
{
lean_object* v_name_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v___x_1346_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1332_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_name_1352_ = lean_ctor_get(v___y_1339_, 0);
lean_inc(v_name_1352_);
lean_dec_ref(v___y_1339_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1354_ = l_Lean_MessageData_ofName(v_name_1352_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_indentExpr(v___y_1337_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1359_, v___y_1333_, v___y_1342_, v___y_1340_, v___y_1334_);
return v___x_1360_;
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = l_Lean_LocalDecl_type(v___y_1362_);
lean_dec_ref(v___y_1362_);
v___x_1368_ = l_Lean_Meta_whnfD(v___x_1367_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = l_Lean_Expr_getAppFn(v_a_1369_);
if (lean_obj_tag(v___x_1370_) == 4)
{
lean_object* v_declName_1371_; lean_object* v_us_1372_; lean_object* v___x_1373_; lean_object* v_env_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; 
v_declName_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_declName_1371_);
v_us_1372_ = lean_ctor_get(v___x_1370_, 1);
lean_inc(v_us_1372_);
lean_dec_ref_known(v___x_1370_, 2);
v___x_1373_ = lean_st_ref_get(v___y_1366_);
v_env_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_ref(v_env_1374_);
lean_dec(v___x_1373_);
v___x_1375_ = 0;
v___x_1376_ = l_Lean_Environment_find_x3f(v_env_1374_, v_declName_1371_, v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_dec(v_us_1372_);
lean_dec(v_a_1369_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
v___y_1207_ = v___y_1365_;
v___y_1208_ = v___y_1366_;
goto v___jp_1204_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_val_1377_) == 5)
{
lean_object* v_val_1378_; lean_object* v_toConstantVal_1379_; lean_object* v_numParams_1380_; lean_object* v_all_1381_; lean_object* v_nargs_1382_; lean_object* v_dummy_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_val_1378_ = lean_ctor_get(v_val_1377_, 0);
lean_inc_ref(v_val_1378_);
lean_dec_ref_known(v_val_1377_, 1);
v_toConstantVal_1379_ = lean_ctor_get(v_val_1378_, 0);
lean_inc_ref(v_toConstantVal_1379_);
v_numParams_1380_ = lean_ctor_get(v_val_1378_, 1);
v_all_1381_ = lean_ctor_get(v_val_1378_, 3);
lean_inc(v_all_1381_);
v_nargs_1382_ = l_Lean_Expr_getAppNumArgs(v_a_1369_);
v_dummy_1383_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1382_);
v___x_1384_ = lean_mk_array(v_nargs_1382_, v_dummy_1383_);
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_sub(v_nargs_1382_, v___x_1385_);
lean_dec(v_nargs_1382_);
lean_inc(v_a_1369_);
v___x_1387_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1369_, v___x_1384_, v___x_1386_);
v___x_1388_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1380_);
lean_inc_ref(v___x_1387_);
v___x_1389_ = l_Array_toSubarray___redArg(v___x_1387_, v___x_1388_, v_numParams_1380_);
v___x_1390_ = l_Subarray_copy___redArg(v___x_1389_);
v___x_1391_ = lean_array_get_size(v___x_1387_);
v___x_1392_ = lean_nat_dec_le(v_numParams_1380_, v___x_1388_);
if (v___x_1392_ == 0)
{
lean_inc(v_numParams_1380_);
v___y_1331_ = v___x_1387_;
v___y_1332_ = v_us_1372_;
v___y_1333_ = v___y_1363_;
v___y_1334_ = v___y_1366_;
v___y_1335_ = v_val_1378_;
v___y_1336_ = v___x_1390_;
v___y_1337_ = v_a_1369_;
v___y_1338_ = v___x_1388_;
v___y_1339_ = v_toConstantVal_1379_;
v___y_1340_ = v___y_1365_;
v___y_1341_ = v_all_1381_;
v___y_1342_ = v___y_1364_;
v_lower_1343_ = v_numParams_1380_;
v_upper_1344_ = v___x_1391_;
goto v___jp_1330_;
}
else
{
v___y_1331_ = v___x_1387_;
v___y_1332_ = v_us_1372_;
v___y_1333_ = v___y_1363_;
v___y_1334_ = v___y_1366_;
v___y_1335_ = v_val_1378_;
v___y_1336_ = v___x_1390_;
v___y_1337_ = v_a_1369_;
v___y_1338_ = v___x_1388_;
v___y_1339_ = v_toConstantVal_1379_;
v___y_1340_ = v___y_1365_;
v___y_1341_ = v_all_1381_;
v___y_1342_ = v___y_1364_;
v_lower_1343_ = v___x_1388_;
v_upper_1344_ = v___x_1391_;
goto v___jp_1330_;
}
}
else
{
lean_dec(v_val_1377_);
lean_dec(v_us_1372_);
lean_dec(v_a_1369_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
v___y_1207_ = v___y_1365_;
v___y_1208_ = v___y_1366_;
goto v___jp_1204_;
}
}
}
else
{
lean_dec_ref(v___x_1370_);
lean_dec(v_a_1369_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
v___y_1207_ = v___y_1365_;
v___y_1208_ = v___y_1366_;
goto v___jp_1204_;
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_a_1393_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1368_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1368_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
v___jp_1401_:
{
lean_object* v_x_1406_; lean_object* v___x_1407_; 
v_x_1406_ = lean_array_fget_borrowed(v_xs_1197_, v_i_1198_);
v___x_1407_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1406_, v___y_1402_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = 0;
v___x_1410_ = l_Lean_LocalDecl_isLet(v_a_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
v___y_1362_ = v_a_1408_;
v___y_1363_ = v___y_1402_;
v___y_1364_ = v___y_1403_;
v___y_1365_ = v___y_1404_;
v___y_1366_ = v___y_1405_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1408_);
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1412_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1411_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_i_1198_);
lean_dec_ref(v_fixedParamPerm_1196_);
lean_dec(v_fnName_1195_);
v_a_1421_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1407_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1407_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1462_, lean_object* v_fixedParamPerm_1463_, lean_object* v_xs_1464_, lean_object* v_i_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1462_, v_fixedParamPerm_1463_, v_xs_1464_, v_i_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec_ref(v_xs_1464_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_msg_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1480_, v_msg_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(lean_object* v_as_1488_, lean_object* v_a_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1488_, v_a_1489_, v_x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(lean_object* v_as_1493_, lean_object* v_a_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(v_as_1493_, v_a_1494_, v_x_1495_, v_x_1496_);
lean_dec_ref(v_a_1494_);
lean_dec_ref(v_as_1493_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1499_, lean_object* v_e_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = l_Lean_indentD(v_e_1500_);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1499_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1503_, lean_object* v_fnName_1504_, lean_object* v_fixedParamPerm_1505_, lean_object* v_args_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1503_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1504_, v_fixedParamPerm_1505_, v_args_1506_, v_a_1513_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1514_;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_fixedParamPerm_1505_);
lean_dec(v_fnName_1504_);
v_a_1515_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1512_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1512_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1523_, lean_object* v_fnName_1524_, lean_object* v_fixedParamPerm_1525_, lean_object* v_args_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1523_, v_fnName_1524_, v_fixedParamPerm_1525_, v_args_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_args_1526_);
return v_res_1532_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1543_ = l_Lean_MessageData_ofFormat(v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1544_, lean_object* v_fnName_1545_, lean_object* v_fixedParamPerm_1546_, lean_object* v_args_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_fst_1556_; lean_object* v_snd_1557_; uint8_t v___x_1562_; 
v___x_1562_ = lean_nat_dec_lt(v_a_1548_, v_upperBound_1544_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec(v_a_1548_);
lean_dec_ref(v_fixedParamPerm_1546_);
lean_dec(v_fnName_1545_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_b_1549_);
return v___x_1563_;
}
else
{
lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1610_; 
v_fst_1564_ = lean_ctor_get(v_b_1549_, 0);
v_snd_1565_ = lean_ctor_get(v_b_1549_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_b_1549_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1567_ = v_b_1549_;
v_isShared_1568_ = v_isSharedCheck_1610_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_snd_1565_);
lean_inc(v_fst_1564_);
lean_dec(v_b_1549_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1610_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; 
lean_inc(v_a_1548_);
lean_inc_ref(v_fixedParamPerm_1546_);
lean_inc(v_fnName_1545_);
v___x_1569_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1545_, v_fixedParamPerm_1546_, v_args_1547_, v_a_1548_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1567_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_array_push(v_fst_1564_, v_a_1570_);
v_fst_1556_ = v___x_1571_;
v_snd_1557_ = v_snd_1565_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1609_; 
v_a_1572_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1574_ = v___x_1569_;
v_isShared_1575_ = v_isSharedCheck_1609_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1569_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1609_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___y_1577_; uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_Exception_isInterrupt(v_a_1572_);
if (v___x_1607_ == 0)
{
uint8_t v___x_1608_; 
lean_inc(v_a_1572_);
v___x_1608_ = l_Lean_Exception_isRuntime(v_a_1572_);
v___y_1577_ = v___x_1608_;
goto v___jp_1576_;
}
else
{
v___y_1577_ = v___x_1607_;
goto v___jp_1576_;
}
v___jp_1576_:
{
if (v___y_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_del_object(v___x_1574_);
v___x_1578_ = l_Lean_Elab_Structural_prettyParam(v_args_1547_, v_a_1548_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 7);
lean_ctor_set(v___x_1567_, 1, v_a_1579_);
lean_ctor_set(v___x_1567_, 0, v___x_1580_);
v___x_1582_ = v___x_1567_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_a_1579_);
v___x_1582_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
lean_inc(v_fnName_1545_);
v___x_1585_ = l_Lean_MessageData_ofName(v_fnName_1545_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_Exception_toMessageData(v_a_1572_);
v___x_1590_ = l_Lean_indentD(v___x_1589_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1588_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_snd_1565_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v_fst_1556_ = v_fst_1564_;
v_snd_1557_ = v___x_1594_;
goto v___jp_1555_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1572_);
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
lean_dec(v_a_1548_);
lean_dec_ref(v_fixedParamPerm_1546_);
lean_dec(v_fnName_1545_);
v_a_1596_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1578_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1578_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v___x_1605_; 
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
lean_dec(v_a_1548_);
lean_dec_ref(v_fixedParamPerm_1546_);
lean_dec(v_fnName_1545_);
if (v_isShared_1575_ == 0)
{
v___x_1605_ = v___x_1574_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1572_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
v___jp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_fst_1556_);
lean_ctor_set(v___x_1558_, 1, v_snd_1557_);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_a_1548_, v___x_1559_);
lean_dec(v_a_1548_);
v_a_1548_ = v___x_1560_;
v_b_1549_ = v___x_1558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1611_, lean_object* v_fnName_1612_, lean_object* v_fixedParamPerm_1613_, lean_object* v_args_1614_, lean_object* v_a_1615_, lean_object* v_b_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1611_, v_fnName_1612_, v_fixedParamPerm_1613_, v_args_1614_, v_a_1615_, v_b_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v_args_1614_);
lean_dec(v_upperBound_1611_);
return v_res_1622_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1623_; double v___x_1624_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_float_of_nat(v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1626_, lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_ref_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1679_; 
v_ref_1633_ = lean_ctor_get(v___y_1630_, 5);
v___x_1634_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1679_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1679_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v_traceState_1640_; lean_object* v_env_1641_; lean_object* v_nextMacroScope_1642_; lean_object* v_ngen_1643_; lean_object* v_auxDeclNGen_1644_; lean_object* v_cache_1645_; lean_object* v_messages_1646_; lean_object* v_infoState_1647_; lean_object* v_snapshotTasks_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1678_; 
v___x_1639_ = lean_st_ref_take(v___y_1631_);
v_traceState_1640_ = lean_ctor_get(v___x_1639_, 4);
v_env_1641_ = lean_ctor_get(v___x_1639_, 0);
v_nextMacroScope_1642_ = lean_ctor_get(v___x_1639_, 1);
v_ngen_1643_ = lean_ctor_get(v___x_1639_, 2);
v_auxDeclNGen_1644_ = lean_ctor_get(v___x_1639_, 3);
v_cache_1645_ = lean_ctor_get(v___x_1639_, 5);
v_messages_1646_ = lean_ctor_get(v___x_1639_, 6);
v_infoState_1647_ = lean_ctor_get(v___x_1639_, 7);
v_snapshotTasks_1648_ = lean_ctor_get(v___x_1639_, 8);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1650_ = v___x_1639_;
v_isShared_1651_ = v_isSharedCheck_1678_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_snapshotTasks_1648_);
lean_inc(v_infoState_1647_);
lean_inc(v_messages_1646_);
lean_inc(v_cache_1645_);
lean_inc(v_traceState_1640_);
lean_inc(v_auxDeclNGen_1644_);
lean_inc(v_ngen_1643_);
lean_inc(v_nextMacroScope_1642_);
lean_inc(v_env_1641_);
lean_dec(v___x_1639_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1678_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
uint64_t v_tid_1652_; lean_object* v_traces_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1677_; 
v_tid_1652_ = lean_ctor_get_uint64(v_traceState_1640_, sizeof(void*)*1);
v_traces_1653_ = lean_ctor_get(v_traceState_1640_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_traceState_1640_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1655_ = v_traceState_1640_;
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_traces_1653_);
lean_dec(v_traceState_1640_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; double v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1659_ = 0;
v___x_1660_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1661_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1661_, 0, v_cls_1626_);
lean_ctor_set(v___x_1661_, 1, v___x_1657_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
lean_ctor_set_float(v___x_1661_, sizeof(void*)*3, v___x_1658_);
lean_ctor_set_float(v___x_1661_, sizeof(void*)*3 + 8, v___x_1658_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*3 + 16, v___x_1659_);
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1663_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v_a_1635_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
lean_inc(v_ref_1633_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_ref_1633_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_PersistentArray_push___redArg(v_traces_1653_, v___x_1664_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1665_);
v___x_1667_ = v___x_1655_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1665_);
lean_ctor_set_uint64(v_reuseFailAlloc_1676_, sizeof(void*)*1, v_tid_1652_);
v___x_1667_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v___x_1667_);
v___x_1669_ = v___x_1650_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_env_1641_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_nextMacroScope_1642_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_ngen_1643_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_auxDeclNGen_1644_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1675_, 5, v_cache_1645_);
lean_ctor_set(v_reuseFailAlloc_1675_, 6, v_messages_1646_);
lean_ctor_set(v_reuseFailAlloc_1675_, 7, v_infoState_1647_);
lean_ctor_set(v_reuseFailAlloc_1675_, 8, v_snapshotTasks_1648_);
v___x_1669_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = lean_st_ref_put(v___y_1631_, v___x_1669_);
v___x_1671_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1671_);
v___x_1673_ = v___x_1637_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1680_, lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1680_, v_msg_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1687_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___f_1692_; 
v___x_1691_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1692_, 0, v___x_1691_);
return v___f_1692_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1697_; lean_object* v_recArgInfos_1698_; lean_object* v___x_1699_; 
v_report_1697_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1698_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_recArgInfos_1698_);
lean_ctor_set(v___x_1699_, 1, v_report_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1712_ = l_Lean_Name_append(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1716_, lean_object* v_fixedParamPerm_1717_, lean_object* v_xs_1718_, lean_object* v_fnName_1719_, lean_object* v_ys_1720_, lean_object* v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1716_) == 1)
{
lean_object* v_val_1727_; lean_object* v_ref_1728_; lean_object* v_fileName_1729_; lean_object* v_fileMap_1730_; lean_object* v_options_1731_; lean_object* v_currRecDepth_1732_; lean_object* v_maxRecDepth_1733_; lean_object* v_ref_1734_; lean_object* v_currNamespace_1735_; lean_object* v_openDecls_1736_; lean_object* v_initHeartbeats_1737_; lean_object* v_maxHeartbeats_1738_; lean_object* v_quotContext_1739_; lean_object* v_currMacroScope_1740_; uint8_t v_diag_1741_; lean_object* v_cancelTk_x3f_1742_; uint8_t v_suppressElabErrors_1743_; lean_object* v_inheritedTraceOptions_1744_; lean_object* v___f_1745_; lean_object* v_args_1746_; lean_object* v___f_1747_; lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_val_1727_ = lean_ctor_get(v_termMeasure_x3f_1716_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v_termMeasure_x3f_1716_, 1);
v_ref_1728_ = lean_ctor_get(v_val_1727_, 0);
lean_inc(v_ref_1728_);
v_fileName_1729_ = lean_ctor_get(v___y_1724_, 0);
v_fileMap_1730_ = lean_ctor_get(v___y_1724_, 1);
v_options_1731_ = lean_ctor_get(v___y_1724_, 2);
v_currRecDepth_1732_ = lean_ctor_get(v___y_1724_, 3);
v_maxRecDepth_1733_ = lean_ctor_get(v___y_1724_, 4);
v_ref_1734_ = lean_ctor_get(v___y_1724_, 5);
v_currNamespace_1735_ = lean_ctor_get(v___y_1724_, 6);
v_openDecls_1736_ = lean_ctor_get(v___y_1724_, 7);
v_initHeartbeats_1737_ = lean_ctor_get(v___y_1724_, 8);
v_maxHeartbeats_1738_ = lean_ctor_get(v___y_1724_, 9);
v_quotContext_1739_ = lean_ctor_get(v___y_1724_, 10);
v_currMacroScope_1740_ = lean_ctor_get(v___y_1724_, 11);
v_diag_1741_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*14);
v_cancelTk_x3f_1742_ = lean_ctor_get(v___y_1724_, 12);
v_suppressElabErrors_1743_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1744_ = lean_ctor_get(v___y_1724_, 13);
v___f_1745_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1717_);
v_args_1746_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1717_, v_xs_1718_, v_ys_1720_);
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1747_, 0, v_val_1727_);
lean_closure_set(v___f_1747_, 1, v_fnName_1719_);
lean_closure_set(v___f_1747_, 2, v_fixedParamPerm_1717_);
lean_closure_set(v___f_1747_, 3, v_args_1746_);
v_ref_1748_ = l_Lean_replaceRef(v_ref_1728_, v_ref_1734_);
lean_dec(v_ref_1728_);
lean_inc_ref(v_inheritedTraceOptions_1744_);
lean_inc(v_cancelTk_x3f_1742_);
lean_inc(v_currMacroScope_1740_);
lean_inc(v_quotContext_1739_);
lean_inc(v_maxHeartbeats_1738_);
lean_inc(v_initHeartbeats_1737_);
lean_inc(v_openDecls_1736_);
lean_inc(v_currNamespace_1735_);
lean_inc(v_maxRecDepth_1733_);
lean_inc(v_currRecDepth_1732_);
lean_inc_ref(v_options_1731_);
lean_inc_ref(v_fileMap_1730_);
lean_inc_ref(v_fileName_1729_);
v___x_1749_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1749_, 0, v_fileName_1729_);
lean_ctor_set(v___x_1749_, 1, v_fileMap_1730_);
lean_ctor_set(v___x_1749_, 2, v_options_1731_);
lean_ctor_set(v___x_1749_, 3, v_currRecDepth_1732_);
lean_ctor_set(v___x_1749_, 4, v_maxRecDepth_1733_);
lean_ctor_set(v___x_1749_, 5, v_ref_1748_);
lean_ctor_set(v___x_1749_, 6, v_currNamespace_1735_);
lean_ctor_set(v___x_1749_, 7, v_openDecls_1736_);
lean_ctor_set(v___x_1749_, 8, v_initHeartbeats_1737_);
lean_ctor_set(v___x_1749_, 9, v_maxHeartbeats_1738_);
lean_ctor_set(v___x_1749_, 10, v_quotContext_1739_);
lean_ctor_set(v___x_1749_, 11, v_currMacroScope_1740_);
lean_ctor_set(v___x_1749_, 12, v_cancelTk_x3f_1742_);
lean_ctor_set(v___x_1749_, 13, v_inheritedTraceOptions_1744_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*14, v_diag_1741_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*14 + 1, v_suppressElabErrors_1743_);
v___x_1750_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1747_, v___f_1745_, v___y_1722_, v___y_1723_, v___x_1749_, v___y_1725_);
lean_dec_ref_known(v___x_1749_, 14);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1763_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1763_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1763_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1755_ = lean_unsigned_to_nat(1u);
v___x_1756_ = lean_mk_empty_array_with_capacity(v___x_1755_);
v___x_1757_ = lean_array_push(v___x_1756_, v_a_1751_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1759_);
v___x_1761_ = v___x_1753_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1764_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1750_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1750_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_args_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v_termMeasure_x3f_1716_);
lean_inc_ref(v_fixedParamPerm_1717_);
v_args_1772_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1717_, v_xs_1718_, v_ys_1720_);
v___x_1773_ = lean_array_get_size(v_args_1772_);
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1773_, v_fnName_1719_, v_fixedParamPerm_1717_, v_args_1772_, v___x_1774_, v___x_1775_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v_args_1772_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1811_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1811_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1811_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1810_; 
v_fst_1781_ = lean_ctor_get(v_a_1777_, 0);
v_snd_1782_ = lean_ctor_get(v_a_1777_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1777_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1784_ = v_a_1777_;
v_isShared_1785_ = v_isSharedCheck_1810_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v_a_1777_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1810_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_options_1793_; uint8_t v_hasTrace_1794_; 
v_options_1793_ = lean_ctor_get(v___y_1724_, 2);
v_hasTrace_1794_ = lean_ctor_get_uint8(v_options_1793_, sizeof(void*)*1);
if (v_hasTrace_1794_ == 0)
{
goto v___jp_1786_;
}
else
{
lean_object* v_inheritedTraceOptions_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_inheritedTraceOptions_1795_ = lean_ctor_get(v___y_1724_, 13);
v___x_1796_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1795_, v_options_1793_, v___x_1797_);
if (v___x_1798_ == 0)
{
goto v___jp_1786_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1782_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v_snd_1782_);
v___x_1801_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1796_, v___x_1800_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_dec_ref_known(v___x_1801_, 1);
goto v___jp_1786_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_del_object(v___x_1784_);
lean_dec(v_snd_1782_);
lean_dec(v_fst_1781_);
lean_del_object(v___x_1779_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
v___jp_1786_:
{
lean_object* v___x_1788_; 
if (v_isShared_1785_ == 0)
{
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_fst_1781_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_snd_1782_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1788_);
v___x_1790_ = v___x_1779_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
else
{
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1812_, lean_object* v_fixedParamPerm_1813_, lean_object* v_xs_1814_, lean_object* v_fnName_1815_, lean_object* v_ys_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1812_, v_fixedParamPerm_1813_, v_xs_1814_, v_fnName_1815_, v_ys_1816_, v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_x_1817_);
lean_dec_ref(v_xs_1814_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1824_, lean_object* v_fixedParamPerm_1825_, lean_object* v_xs_1826_, lean_object* v_value_1827_, lean_object* v_termMeasure_x3f_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___f_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; 
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1834_, 0, v_termMeasure_x3f_1828_);
lean_closure_set(v___f_1834_, 1, v_fixedParamPerm_1825_);
lean_closure_set(v___f_1834_, 2, v_xs_1826_);
lean_closure_set(v___f_1834_, 3, v_fnName_1824_);
v___x_1835_ = 0;
v___x_1836_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1827_, v___f_1834_, v___x_1835_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1837_, lean_object* v_fixedParamPerm_1838_, lean_object* v_xs_1839_, lean_object* v_value_1840_, lean_object* v_termMeasure_x3f_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1837_, v_fixedParamPerm_1838_, v_xs_1839_, v_value_1840_, v_termMeasure_x3f_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1848_, lean_object* v_fnName_1849_, lean_object* v_fixedParamPerm_1850_, lean_object* v_args_1851_, lean_object* v_inst_1852_, lean_object* v_R_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_, lean_object* v_c_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1848_, v_fnName_1849_, v_fixedParamPerm_1850_, v_args_1851_, v_a_1854_, v_b_1855_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1863_, lean_object* v_fnName_1864_, lean_object* v_fixedParamPerm_1865_, lean_object* v_args_1866_, lean_object* v_inst_1867_, lean_object* v_R_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v_c_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1863_, v_fnName_1864_, v_fixedParamPerm_1865_, v_args_1866_, v_inst_1867_, v_R_1868_, v_a_1869_, v_b_1870_, v_c_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec_ref(v_args_1866_);
lean_dec(v_upperBound_1863_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_m_1878_, lean_object* v_query_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v_zero_1883_; uint8_t v_isZero_1884_; 
v_zero_1883_ = lean_unsigned_to_nat(0u);
v_isZero_1884_ = lean_nat_dec_eq(v_x_1881_, v_zero_1883_);
if (v_isZero_1884_ == 1)
{
lean_dec(v_x_1882_);
lean_dec(v_x_1881_);
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_box(2);
return v___x_1885_;
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_val_1886_ = lean_ctor_get(v_x_1880_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1880_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v_x_1880_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v_x_1880_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_val_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_keyArray_1894_; lean_object* v_valueArray_1895_; lean_object* v___x_1896_; uint8_t v_isSome_1897_; 
v_keyArray_1894_ = lean_ctor_get(v_m_1878_, 1);
v_valueArray_1895_ = lean_ctor_get(v_m_1878_, 2);
v___x_1896_ = lean_array_fget_borrowed(v_keyArray_1894_, v_x_1882_);
v_isSome_1897_ = lean_noption_is_some(v___x_1896_);
if (v_isSome_1897_ == 0)
{
lean_dec(v_x_1881_);
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_x_1882_);
return v___x_1898_;
}
else
{
lean_object* v_val_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_x_1882_);
v_val_1899_ = lean_ctor_get(v_x_1880_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_x_1880_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v_x_1880_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_val_1899_);
lean_dec(v_x_1880_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_one_1907_; lean_object* v_n_1908_; lean_object* v___y_1910_; 
v_one_1907_ = lean_unsigned_to_nat(1u);
v_n_1908_ = lean_nat_sub(v_x_1881_, v_one_1907_);
lean_dec(v_x_1881_);
if (v_isSome_1897_ == 0)
{
goto v___jp_1916_;
}
else
{
lean_object* v___x_1918_; uint8_t v_isSome_1919_; 
v___x_1918_ = lean_array_fget_borrowed(v_valueArray_1895_, v_x_1882_);
v_isSome_1919_ = lean_noption_is_some(v___x_1918_);
if (v_isSome_1919_ == 0)
{
goto v___jp_1916_;
}
else
{
lean_object* v_val_1920_; uint8_t v___x_1921_; 
lean_inc(v___x_1896_);
v_val_1920_ = lean_noption_get(v___x_1896_);
v___x_1921_ = lean_nat_dec_eq(v_val_1920_, v_query_1879_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
lean_dec(v_val_1920_);
v___x_1922_ = lean_array_get_size(v_keyArray_1894_);
v___x_1923_ = lean_nat_add(v_x_1882_, v_one_1907_);
lean_dec(v_x_1882_);
v___x_1924_ = lean_nat_dec_lt(v___x_1923_, v___x_1922_);
if (v___x_1924_ == 0)
{
lean_dec(v___x_1923_);
v_x_1881_ = v_n_1908_;
v_x_1882_ = v_zero_1883_;
goto _start;
}
else
{
v_x_1881_ = v_n_1908_;
v_x_1882_ = v___x_1923_;
goto _start;
}
}
else
{
lean_object* v_val_1927_; lean_object* v___x_1928_; 
lean_dec(v_n_1908_);
lean_dec(v_x_1880_);
lean_inc(v___x_1918_);
v_val_1927_ = lean_noption_get(v___x_1918_);
v___x_1928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1928_, 0, v_x_1882_);
lean_ctor_set(v___x_1928_, 1, v_val_1920_);
lean_ctor_set(v___x_1928_, 2, v_val_1927_);
return v___x_1928_;
}
}
}
v___jp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1911_ = lean_array_get_size(v_keyArray_1894_);
v___x_1912_ = lean_nat_add(v_x_1882_, v_one_1907_);
lean_dec(v_x_1882_);
v___x_1913_ = lean_nat_dec_lt(v___x_1912_, v___x_1911_);
if (v___x_1913_ == 0)
{
lean_dec(v___x_1912_);
v_x_1880_ = v___y_1910_;
v_x_1881_ = v_n_1908_;
v_x_1882_ = v_zero_1883_;
goto _start;
}
else
{
v_x_1880_ = v___y_1910_;
v_x_1881_ = v_n_1908_;
v_x_1882_ = v___x_1912_;
goto _start;
}
}
v___jp_1916_:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v___x_1917_; 
lean_inc(v_x_1882_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_x_1882_);
v___y_1910_ = v___x_1917_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v_x_1880_;
goto v___jp_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_m_1929_, lean_object* v_query_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_m_1929_, v_query_1930_, v_x_1931_, v_x_1932_, v_x_1933_);
lean_dec(v_query_1930_);
lean_dec_ref(v_m_1929_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1935_, lean_object* v_query_1936_){
_start:
{
lean_object* v_keyArray_1937_; lean_object* v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v_fold_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_keyArray_1937_ = lean_ctor_get(v_m_1935_, 1);
v___x_1938_ = lean_array_get_size(v_keyArray_1937_);
v___x_1939_ = lean_uint64_of_nat(v_query_1936_);
v___x_1940_ = 32ULL;
v___x_1941_ = lean_uint64_shift_right(v___x_1939_, v___x_1940_);
v_fold_1942_ = lean_uint64_xor(v___x_1939_, v___x_1941_);
v___x_1943_ = 16ULL;
v___x_1944_ = lean_uint64_shift_right(v_fold_1942_, v___x_1943_);
v___x_1945_ = lean_uint64_xor(v_fold_1942_, v___x_1944_);
v___x_1946_ = lean_uint64_to_usize(v___x_1945_);
v___x_1947_ = lean_usize_of_nat(v___x_1938_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_sub(v___x_1947_, v___x_1948_);
v___x_1950_ = lean_usize_land(v___x_1946_, v___x_1949_);
v___x_1951_ = lean_usize_to_nat(v___x_1950_);
v___x_1952_ = lean_box(0);
v___x_1953_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_m_1935_, v_query_1936_, v___x_1952_, v___x_1938_, v___x_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg___boxed(lean_object* v_m_1954_, lean_object* v_query_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_1954_, v_query_1955_);
lean_dec(v_query_1955_);
lean_dec_ref(v_m_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg(lean_object* v_m_1957_, lean_object* v_query_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_1957_, v_query_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_index_1960_; lean_object* v_key_1961_; lean_object* v_value_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_index_1960_ = lean_ctor_get(v___x_1959_, 0);
v_key_1961_ = lean_ctor_get(v___x_1959_, 1);
v_value_1962_ = lean_ctor_get(v___x_1959_, 2);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1959_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_value_1962_);
lean_inc(v_key_1961_);
lean_inc(v_index_1960_);
lean_dec(v___x_1959_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_index_1960_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_key_1961_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_value_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v___x_1970_; 
lean_dec(v___x_1959_);
v___x_1970_ = lean_box(1);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg___boxed(lean_object* v_m_1971_, lean_object* v_query_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg(v_m_1971_, v_query_1972_);
lean_dec(v_query_1972_);
lean_dec_ref(v_m_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg(lean_object* v_m_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg(v_m_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
uint8_t v___x_1977_; 
lean_dec_ref_known(v___x_1976_, 3);
v___x_1977_ = 1;
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = 0;
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg___boxed(lean_object* v_m_1979_, lean_object* v_a_1980_){
_start:
{
uint8_t v_res_1981_; lean_object* v_r_1982_; 
v_res_1981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg(v_m_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_m_1979_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5(lean_object* v___x_1983_, lean_object* v_as_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_b_1987_){
_start:
{
lean_object* v_a_1989_; uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1993_ == 0)
{
return v_b_1987_;
}
else
{
lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2010_; 
v_fst_1994_ = lean_ctor_get(v_b_1987_, 0);
v_snd_1995_ = lean_ctor_get(v_b_1987_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_b_1987_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1997_ = v_b_1987_;
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1995_);
lean_inc(v_fst_1994_);
lean_dec(v_b_1987_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_a_1999_; lean_object* v_recArgPos_2000_; uint8_t v___x_2001_; 
v_a_1999_ = lean_array_uget_borrowed(v_as_1984_, v_i_1986_);
v_recArgPos_2000_ = lean_ctor_get(v_a_1999_, 2);
v___x_2001_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg(v___x_1983_, v_recArgPos_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_inc(v_a_1999_);
v___x_2002_ = lean_array_push(v_snd_1995_, v_a_1999_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2002_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_fst_1994_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v_a_1989_ = v___x_2004_;
goto v___jp_1988_;
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_inc(v_a_1999_);
v___x_2006_ = lean_array_push(v_fst_1994_, v_a_1999_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2006_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_snd_1995_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v_a_1989_ = v___x_2008_;
goto v___jp_1988_;
}
}
}
}
v___jp_1988_:
{
size_t v___x_1990_; size_t v___x_1991_; 
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1986_, v___x_1990_);
v_i_1986_ = v___x_1991_;
v_b_1987_ = v_a_1989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5___boxed(lean_object* v___x_2011_, lean_object* v_as_2012_, lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_b_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5(v___x_2011_, v_as_2012_, v_sz_boxed_2016_, v_i_boxed_2017_, v_b_2015_);
lean_dec_ref(v_as_2012_);
lean_dec_ref(v___x_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg(lean_object* v_b_2019_, lean_object* v_acc_2020_, lean_object* v_i_2021_){
_start:
{
lean_object* v___y_2023_; lean_object* v_keyArray_2031_; lean_object* v_valueArray_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_keyArray_2031_ = lean_ctor_get(v_b_2019_, 1);
v_valueArray_2032_ = lean_ctor_get(v_b_2019_, 2);
v___x_2033_ = lean_array_get_size(v_keyArray_2031_);
v___x_2034_ = lean_nat_dec_lt(v_i_2021_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec(v_i_2021_);
return v_acc_2020_;
}
else
{
lean_object* v___x_2035_; uint8_t v_isSome_2036_; 
v___x_2035_ = lean_array_fget_borrowed(v_keyArray_2031_, v_i_2021_);
v_isSome_2036_ = lean_noption_is_some(v___x_2035_);
if (v_isSome_2036_ == 0)
{
goto v___jp_2027_;
}
else
{
lean_object* v___x_2037_; uint8_t v_isSome_2038_; 
v___x_2037_ = lean_array_fget_borrowed(v_valueArray_2032_, v_i_2021_);
v_isSome_2038_ = lean_noption_is_some(v___x_2037_);
if (v_isSome_2038_ == 0)
{
goto v___jp_2027_;
}
else
{
lean_object* v_val_2039_; lean_object* v_val_2040_; lean_object* v_i_2042_; lean_object* v___x_2047_; 
lean_inc(v___x_2035_);
v_val_2039_ = lean_noption_get(v___x_2035_);
lean_inc(v___x_2037_);
v_val_2040_ = lean_noption_get(v___x_2037_);
v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_acc_2020_, v_val_2039_);
switch(lean_obj_tag(v___x_2047_))
{
case 0:
{
lean_object* v_index_2048_; lean_object* v_size_2049_; lean_object* v___x_2050_; 
v_index_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_index_2048_);
lean_dec_ref_known(v___x_2047_, 3);
v_size_2049_ = lean_ctor_get(v_acc_2020_, 0);
lean_inc(v_size_2049_);
v___x_2050_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2020_, v_size_2049_, v_index_2048_, v_val_2039_, v_val_2040_);
lean_dec(v_index_2048_);
v___y_2023_ = v___x_2050_;
goto v___jp_2022_;
}
case 1:
{
lean_object* v_index_2051_; 
v_index_2051_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_index_2051_);
lean_dec_ref_known(v___x_2047_, 1);
v_i_2042_ = v_index_2051_;
goto v___jp_2041_;
}
default: 
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2020_, v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_index_2054_; 
v_index_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_index_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v_i_2042_ = v_index_2054_;
goto v___jp_2041_;
}
else
{
lean_dec(v_val_2040_);
lean_dec(v_val_2039_);
v___y_2023_ = v_acc_2020_;
goto v___jp_2022_;
}
}
}
v___jp_2041_:
{
lean_object* v_size_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_size_2043_ = lean_ctor_get(v_acc_2020_, 0);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_add(v_size_2043_, v___x_2044_);
v___x_2046_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2020_, v___x_2045_, v_i_2042_, v_val_2039_, v_val_2040_);
lean_dec(v_i_2042_);
v___y_2023_ = v___x_2046_;
goto v___jp_2022_;
}
}
}
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_i_2021_, v___x_2024_);
lean_dec(v_i_2021_);
v_acc_2020_ = v___y_2023_;
v_i_2021_ = v___x_2025_;
goto _start;
}
v___jp_2027_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_i_2021_, v___x_2028_);
lean_dec(v_i_2021_);
v_i_2021_ = v___x_2029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_2055_, lean_object* v_acc_2056_, lean_object* v_i_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg(v_b_2055_, v_acc_2056_, v_i_2057_);
lean_dec_ref(v_b_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg(lean_object* v_init_2059_, lean_object* v_b_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg(v_b_2060_, v_init_2059_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg___boxed(lean_object* v_init_2063_, lean_object* v_b_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg(v_init_2063_, v_b_2064_);
lean_dec_ref(v_b_2064_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(lean_object* v_m_2066_){
_start:
{
lean_object* v_keyArray_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_cellCount_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_target_2074_; lean_object* v___x_2075_; 
v_keyArray_2067_ = lean_ctor_get(v_m_2066_, 1);
v___x_2068_ = lean_array_get_size(v_keyArray_2067_);
v___x_2069_ = lean_unsigned_to_nat(2u);
v_cellCount_2070_ = lean_nat_mul(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2070_);
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2070_);
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2070_);
v_target_2074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2074_, 0, v___x_2071_);
lean_ctor_set(v_target_2074_, 1, v___x_2072_);
lean_ctor_set(v_target_2074_, 2, v___x_2073_);
v___x_2075_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg(v_target_2074_, v_m_2066_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg___boxed(lean_object* v_m_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(v_m_2076_);
lean_dec_ref(v_m_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_){
_start:
{
lean_object* v___y_2083_; uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2087_ == 0)
{
return v_b_2081_;
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2089_; lean_object* v___y_2091_; lean_object* v_i_2092_; lean_object* v___y_2098_; lean_object* v___y_2108_; lean_object* v_i_2109_; lean_object* v___x_2124_; 
v_a_2088_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
v___x_2089_ = lean_box(0);
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_2081_, v_a_2088_);
switch(lean_obj_tag(v___x_2124_))
{
case 0:
{
lean_dec_ref_known(v___x_2124_, 3);
v___y_2083_ = v_b_2081_;
goto v___jp_2082_;
}
case 1:
{
lean_object* v_index_2125_; lean_object* v_size_2126_; lean_object* v_keyArray_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_index_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_index_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v_size_2126_ = lean_ctor_get(v_b_2081_, 0);
v_keyArray_2127_ = lean_ctor_get(v_b_2081_, 1);
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = lean_nat_add(v_size_2126_, v___x_2128_);
v___x_2130_ = lean_array_get_size(v_keyArray_2127_);
v___x_2131_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_dec(v___x_2129_);
lean_dec(v_index_2125_);
goto v___jp_2114_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2132_ = lean_unsigned_to_nat(4u);
v___x_2133_ = lean_nat_mul(v___x_2129_, v___x_2132_);
v___x_2134_ = lean_unsigned_to_nat(3u);
v___x_2135_ = lean_nat_mul(v___x_2130_, v___x_2134_);
v___x_2136_ = lean_nat_dec_le(v___x_2133_, v___x_2135_);
lean_dec(v___x_2135_);
lean_dec(v___x_2133_);
if (v___x_2136_ == 0)
{
lean_dec(v___x_2129_);
lean_dec(v_index_2125_);
goto v___jp_2114_;
}
else
{
lean_object* v___x_2137_; 
lean_inc(v_a_2088_);
v___x_2137_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_2081_, v___x_2129_, v_index_2125_, v_a_2088_, v___x_2089_);
lean_dec(v_index_2125_);
v___y_2083_ = v___x_2137_;
goto v___jp_2082_;
}
}
}
default: 
{
lean_object* v_size_2138_; lean_object* v_keyArray_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v_size_2138_ = lean_ctor_get(v_b_2081_, 0);
v_keyArray_2139_ = lean_ctor_get(v_b_2081_, 1);
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_add(v_size_2138_, v___x_2140_);
v___x_2142_ = lean_array_get_size(v_keyArray_2139_);
v___x_2143_ = lean_nat_dec_lt(v___x_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_dec(v___x_2141_);
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(v_b_2081_);
lean_dec_ref(v_b_2081_);
v___y_2098_ = v___x_2144_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2145_ = lean_unsigned_to_nat(4u);
v___x_2146_ = lean_nat_mul(v___x_2141_, v___x_2145_);
lean_dec(v___x_2141_);
v___x_2147_ = lean_unsigned_to_nat(3u);
v___x_2148_ = lean_nat_mul(v___x_2142_, v___x_2147_);
v___x_2149_ = lean_nat_dec_le(v___x_2146_, v___x_2148_);
lean_dec(v___x_2148_);
lean_dec(v___x_2146_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(v_b_2081_);
lean_dec_ref(v_b_2081_);
v___y_2098_ = v___x_2150_;
goto v___jp_2097_;
}
else
{
v___y_2098_ = v_b_2081_;
goto v___jp_2097_;
}
}
}
}
v___jp_2090_:
{
lean_object* v_size_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_size_2093_ = lean_ctor_get(v___y_2091_, 0);
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_add(v_size_2093_, v___x_2094_);
lean_inc(v_a_2088_);
v___x_2096_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2091_, v___x_2095_, v_i_2092_, v_a_2088_, v___x_2089_);
lean_dec(v_i_2092_);
v___y_2083_ = v___x_2096_;
goto v___jp_2082_;
}
v___jp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v___y_2098_, v_a_2088_);
switch(lean_obj_tag(v___x_2099_))
{
case 0:
{
lean_object* v_index_2100_; lean_object* v_size_2101_; lean_object* v___x_2102_; 
v_index_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_index_2100_);
lean_dec_ref_known(v___x_2099_, 3);
v_size_2101_ = lean_ctor_get(v___y_2098_, 0);
lean_inc(v_size_2101_);
lean_inc(v_a_2088_);
v___x_2102_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2098_, v_size_2101_, v_index_2100_, v_a_2088_, v___x_2089_);
lean_dec(v_index_2100_);
v___y_2083_ = v___x_2102_;
goto v___jp_2082_;
}
case 1:
{
lean_object* v_index_2103_; 
v_index_2103_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_index_2103_);
lean_dec_ref_known(v___x_2099_, 1);
v___y_2091_ = v___y_2098_;
v_i_2092_ = v_index_2103_;
goto v___jp_2090_;
}
default: 
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2098_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_index_2106_; 
v_index_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_index_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_2091_ = v___y_2098_;
v_i_2092_ = v_index_2106_;
goto v___jp_2090_;
}
else
{
v___y_2083_ = v___y_2098_;
goto v___jp_2082_;
}
}
}
}
v___jp_2107_:
{
lean_object* v_size_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_size_2110_ = lean_ctor_get(v___y_2108_, 0);
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_add(v_size_2110_, v___x_2111_);
lean_inc(v_a_2088_);
v___x_2113_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2108_, v___x_2112_, v_i_2109_, v_a_2088_, v___x_2089_);
lean_dec(v_i_2109_);
v___y_2083_ = v___x_2113_;
goto v___jp_2082_;
}
v___jp_2114_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(v_b_2081_);
lean_dec_ref(v_b_2081_);
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v___x_2115_, v_a_2088_);
switch(lean_obj_tag(v___x_2116_))
{
case 0:
{
lean_object* v_index_2117_; lean_object* v_size_2118_; lean_object* v___x_2119_; 
v_index_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_index_2117_);
lean_dec_ref_known(v___x_2116_, 3);
v_size_2118_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_size_2118_);
lean_inc(v_a_2088_);
v___x_2119_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2115_, v_size_2118_, v_index_2117_, v_a_2088_, v___x_2089_);
lean_dec(v_index_2117_);
v___y_2083_ = v___x_2119_;
goto v___jp_2082_;
}
case 1:
{
lean_object* v_index_2120_; 
v_index_2120_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_index_2120_);
lean_dec_ref_known(v___x_2116_, 1);
v___y_2108_ = v___x_2115_;
v_i_2109_ = v_index_2120_;
goto v___jp_2107_;
}
default: 
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2115_, v___x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_index_2123_; 
v_index_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_index_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___y_2108_ = v___x_2115_;
v_i_2109_ = v_index_2123_;
goto v___jp_2107_;
}
else
{
v___y_2083_ = v___x_2115_;
goto v___jp_2082_;
}
}
}
}
}
v___jp_2082_:
{
size_t v___x_2084_; size_t v___x_2085_; 
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_add(v_i_2080_, v___x_2084_);
v_i_2080_ = v___x_2085_;
v_b_2081_ = v___y_2083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2151_, lean_object* v_sz_2152_, lean_object* v_i_2153_, lean_object* v_b_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2152_);
lean_dec(v_sz_2152_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2151_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2154_);
lean_dec_ref(v_as_2151_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_as_2158_, size_t v_sz_2159_, size_t v_i_2160_, lean_object* v_b_2161_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_usize_dec_lt(v_i_2160_, v_sz_2159_);
if (v___x_2162_ == 0)
{
return v_b_2161_;
}
else
{
lean_object* v_a_2163_; lean_object* v_indicesPos_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; 
v_a_2163_ = lean_array_uget_borrowed(v_as_2158_, v_i_2160_);
v_indicesPos_2164_ = lean_ctor_get(v_a_2163_, 3);
v_sz_2165_ = lean_array_size(v_indicesPos_2164_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_indicesPos_2164_, v_sz_2165_, v___x_2166_, v_b_2161_);
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2160_, v___x_2168_);
v_i_2160_ = v___x_2169_;
v_b_2161_ = v___x_2167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_as_2171_, lean_object* v_sz_2172_, lean_object* v_i_2173_, lean_object* v_b_2174_){
_start:
{
size_t v_sz_boxed_2175_; size_t v_i_boxed_2176_; lean_object* v_res_2177_; 
v_sz_boxed_2175_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2176_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_as_2171_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2174_);
lean_dec_ref(v_as_2171_);
return v_res_2177_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v_cellCount_2178_; lean_object* v___x_2179_; 
v_cellCount_2178_ = lean_unsigned_to_nat(16u);
v___x_2179_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_indicesPos_2183_; 
v___x_2180_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_2181_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2182_ = lean_unsigned_to_nat(0u);
v_indicesPos_2183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_indicesPos_2183_, 0, v___x_2182_);
lean_ctor_set(v_indicesPos_2183_, 1, v___x_2181_);
lean_ctor_set(v_indicesPos_2183_, 2, v___x_2180_);
return v_indicesPos_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2186_){
_start:
{
lean_object* v_indicesPos_2187_; size_t v_sz_2188_; size_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2195_; 
v_indicesPos_2187_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2188_ = lean_array_size(v_recArgInfos_2186_);
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_recArgInfos_2186_, v_sz_2188_, v___x_2189_, v_indicesPos_2187_);
v___x_2191_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__5(v___x_2190_, v_recArgInfos_2186_, v_sz_2188_, v___x_2189_, v___x_2191_);
lean_dec_ref(v___x_2190_);
v_fst_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_fst_2193_);
v_snd_2194_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_snd_2194_);
lean_dec_ref(v___x_2192_);
v___x_2195_ = l_Array_append___redArg(v_snd_2194_, v_fst_2193_);
lean_dec(v_fst_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2196_);
lean_dec_ref(v_recArgInfos_2196_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2198_, lean_object* v_m_2199_, lean_object* v_query_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2199_, v_query_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___boxed(lean_object* v_00_u03b2_2202_, lean_object* v_m_2203_, lean_object* v_query_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(v_00_u03b2_2202_, v_m_2203_, v_query_2204_);
lean_dec(v_query_2204_);
lean_dec_ref(v_m_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_00_u03b2_2206_, lean_object* v_m_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___redArg(v_m_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_00_u03b2_2209_, v_m_2210_);
lean_dec_ref(v_m_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v_00_u03b2_2212_, lean_object* v_m_2213_, lean_object* v_a_2214_){
_start:
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___redArg(v_m_2213_, v_a_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_m_2217_, lean_object* v_a_2218_){
_start:
{
uint8_t v_res_2219_; lean_object* v_r_2220_; 
v_res_2219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v_00_u03b2_2216_, v_m_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_m_2217_);
v_r_2220_ = lean_box(v_res_2219_);
return v_r_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2221_, lean_object* v_m_2222_, lean_object* v_query_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_m_2222_, v_query_2223_, v_x_2224_, v_x_2225_, v_x_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_m_2230_, lean_object* v_query_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2229_, v_m_2230_, v_query_2231_, v_x_2232_, v_x_2233_, v_x_2234_, v_x_2235_);
lean_dec(v_query_2231_);
lean_dec_ref(v_m_2230_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2(lean_object* v_00_u03b2_2237_, lean_object* v_init_2238_, lean_object* v_b_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___redArg(v_init_2238_, v_b_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_init_2242_, lean_object* v_b_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2(v_00_u03b2_2241_, v_init_2242_, v_b_2243_);
lean_dec_ref(v_b_2243_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6(lean_object* v_00_u03b2_2245_, lean_object* v_m_2246_, lean_object* v_query_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___redArg(v_m_2246_, v_query_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2249_, lean_object* v_m_2250_, lean_object* v_query_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_spec__6(v_00_u03b2_2249_, v_m_2250_, v_query_2251_);
lean_dec(v_query_2251_);
lean_dec_ref(v_m_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2253_, lean_object* v_b_2254_, lean_object* v_acc_2255_, lean_object* v_i_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___redArg(v_b_2254_, v_acc_2255_, v_i_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2258_, lean_object* v_b_2259_, lean_object* v_acc_2260_, lean_object* v_i_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_spec__2_spec__3(v_00_u03b2_2258_, v_b_2259_, v_acc_2260_, v_i_2261_);
lean_dec_ref(v_b_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2263_, lean_object* v_a_2264_, lean_object* v_toPure_2265_, uint8_t v_____do__lift_2266_){
_start:
{
if (v_____do__lift_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_array_push(v___y_2263_, v_a_2264_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2268_);
return v___x_2269_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_a_2264_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___y_2263_);
v___x_2271_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2270_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2272_, lean_object* v_a_2273_, lean_object* v_toPure_2274_, lean_object* v_____do__lift_2275_){
_start:
{
uint8_t v_____do__lift_192__boxed_2276_; lean_object* v_res_2277_; 
v_____do__lift_192__boxed_2276_ = lean_unbox(v_____do__lift_2275_);
v_res_2277_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2272_, v_a_2273_, v_toPure_2274_, v_____do__lift_192__boxed_2276_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2278_, lean_object* v_a_2279_, lean_object* v_x_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_apply_2(v_eq_2278_, v_x_2280_, v_a_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2282_, lean_object* v___x_2283_, lean_object* v_toBind_2284_, lean_object* v_eq_2285_, lean_object* v_inst_2286_, lean_object* v_a_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___f_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
lean_inc(v_toPure_2282_);
lean_inc(v_a_2287_);
lean_inc_ref(v___y_2289_);
v___f_2290_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2290_, 0, v___y_2289_);
lean_closure_set(v___f_2290_, 1, v_a_2287_);
lean_closure_set(v___f_2290_, 2, v_toPure_2282_);
v___x_2291_ = lean_array_get_size(v___y_2289_);
v___x_2292_ = lean_nat_dec_lt(v___x_2283_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v___y_2289_);
lean_dec(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec(v_eq_2285_);
v___x_2293_ = lean_box(v___x_2292_);
v___x_2294_ = lean_apply_2(v_toPure_2282_, lean_box(0), v___x_2293_);
v___x_2295_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2294_, v___f_2290_);
return v___x_2295_;
}
else
{
if (v___x_2292_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v___y_2289_);
lean_dec(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec(v_eq_2285_);
v___x_2296_ = lean_box(v___x_2292_);
v___x_2297_ = lean_apply_2(v_toPure_2282_, lean_box(0), v___x_2296_);
v___x_2298_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2297_, v___f_2290_);
return v___x_2298_;
}
else
{
lean_object* v___f_2299_; size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec(v_toPure_2282_);
v___f_2299_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2299_, 0, v_eq_2285_);
lean_closure_set(v___f_2299_, 1, v_a_2287_);
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2291_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2286_, v___f_2299_, v___y_2289_, v___x_2300_, v___x_2301_);
v___x_2303_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2302_, v___f_2290_);
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2304_, lean_object* v___x_2305_, lean_object* v_toBind_2306_, lean_object* v_eq_2307_, lean_object* v_inst_2308_, lean_object* v_a_2309_, lean_object* v_x_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2304_, v___x_2305_, v_toBind_2306_, v_eq_2307_, v_inst_2308_, v_a_2309_, v_x_2310_, v___y_2311_);
lean_dec(v___x_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2313_, lean_object* v_____s_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_apply_2(v_toPure_2313_, lean_box(0), v_____s_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2318_, lean_object* v_eq_2319_, lean_object* v_xs_2320_){
_start:
{
lean_object* v_toApplicative_2321_; lean_object* v_toBind_2322_; lean_object* v_toPure_2323_; lean_object* v___x_2324_; lean_object* v_ret_2325_; lean_object* v___f_2326_; lean_object* v___f_2327_; size_t v_sz_2328_; size_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_toApplicative_2321_ = lean_ctor_get(v_inst_2318_, 0);
v_toBind_2322_ = lean_ctor_get(v_inst_2318_, 1);
lean_inc_n(v_toBind_2322_, 2);
v_toPure_2323_ = lean_ctor_get(v_toApplicative_2321_, 1);
v___x_2324_ = lean_unsigned_to_nat(0u);
v_ret_2325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2318_);
lean_inc_n(v_toPure_2323_, 2);
v___f_2326_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2326_, 0, v_toPure_2323_);
lean_closure_set(v___f_2326_, 1, v___x_2324_);
lean_closure_set(v___f_2326_, 2, v_toBind_2322_);
lean_closure_set(v___f_2326_, 3, v_eq_2319_);
lean_closure_set(v___f_2326_, 4, v_inst_2318_);
v___f_2327_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2327_, 0, v_toPure_2323_);
v_sz_2328_ = lean_array_size(v_xs_2320_);
v___x_2329_ = ((size_t)0ULL);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2318_, v_xs_2320_, v___f_2326_, v_sz_2328_, v___x_2329_, v_ret_2325_);
v___x_2331_ = lean_apply_4(v_toBind_2322_, lean_box(0), lean_box(0), v___x_2330_, v___f_2327_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2332_, lean_object* v_00_u03b1_2333_, lean_object* v_inst_2334_, lean_object* v_eq_2335_, lean_object* v_xs_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2334_, v_eq_2335_, v_xs_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_bs_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2341_ == 0)
{
return v_bs_2340_;
}
else
{
lean_object* v_v_2342_; lean_object* v_indGroupInst_2343_; lean_object* v___x_2344_; lean_object* v_bs_x27_2345_; size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v_v_2342_ = lean_array_uget_borrowed(v_bs_2340_, v_i_2339_);
v_indGroupInst_2343_ = lean_ctor_get(v_v_2342_, 4);
lean_inc_ref(v_indGroupInst_2343_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v_bs_x27_2345_ = lean_array_uset(v_bs_2340_, v_i_2339_, v___x_2344_);
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_add(v_i_2339_, v___x_2346_);
v___x_2348_ = lean_array_uset(v_bs_x27_2345_, v_i_2339_, v_indGroupInst_2343_);
v_i_2339_ = v___x_2347_;
v_bs_2340_ = v___x_2348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2350_, lean_object* v_i_2351_, lean_object* v_bs_2352_){
_start:
{
size_t v_sz_boxed_2353_; size_t v_i_boxed_2354_; lean_object* v_res_2355_; 
v_sz_boxed_2353_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2353_, v_i_boxed_2354_, v_bs_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2356_, lean_object* v_a_2357_, lean_object* v_as_2358_, size_t v_i_2359_, size_t v_stop_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_usize_dec_eq(v_i_2359_, v_stop_2360_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_array_uget_borrowed(v_as_2358_, v_i_2359_);
lean_inc_ref(v_eq_2356_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v_a_2357_);
lean_inc(v___x_2367_);
v___x_2368_ = lean_apply_7(v_eq_2356_, v___x_2367_, v_a_2357_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, lean_box(0));
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2380_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_unbox(v_a_2369_);
if (v___x_2373_ == 0)
{
size_t v___x_2374_; size_t v___x_2375_; 
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
v___x_2374_ = ((size_t)1ULL);
v___x_2375_ = lean_usize_add(v_i_2359_, v___x_2374_);
v_i_2359_ = v___x_2375_;
goto _start;
}
else
{
lean_object* v___x_2378_; 
lean_dec(v_a_2357_);
lean_dec_ref(v_eq_2356_);
if (v_isShared_2372_ == 0)
{
v___x_2378_ = v___x_2371_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2369_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_dec(v_a_2357_);
lean_dec_ref(v_eq_2356_);
return v___x_2368_;
}
}
else
{
uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_a_2357_);
lean_dec_ref(v_eq_2356_);
v___x_2381_ = 0;
v___x_2382_ = lean_box(v___x_2381_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2384_, lean_object* v_a_2385_, lean_object* v_as_2386_, lean_object* v_i_2387_, lean_object* v_stop_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
size_t v_i_boxed_2394_; size_t v_stop_boxed_2395_; lean_object* v_res_2396_; 
v_i_boxed_2394_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_stop_boxed_2395_ = lean_unbox_usize(v_stop_2388_);
lean_dec(v_stop_2388_);
v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2384_, v_a_2385_, v_as_2386_, v_i_boxed_2394_, v_stop_boxed_2395_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v_as_2386_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2397_, lean_object* v_a_2398_, uint8_t v_____do__lift_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
if (v_____do__lift_2399_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_array_push(v_b_2397_, v_a_2398_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec(v_a_2398_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_b_2397_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2410_, lean_object* v_a_2411_, lean_object* v_____do__lift_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v_____do__lift_1292__boxed_2418_; lean_object* v_res_2419_; 
v_____do__lift_1292__boxed_2418_ = lean_unbox(v_____do__lift_2412_);
v_res_2419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2410_, v_a_2411_, v_____do__lift_1292__boxed_2418_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2420_, lean_object* v_as_2421_, size_t v_sz_2422_, size_t v_i_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_a_2431_; lean_object* v___y_2436_; uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_lt(v_i_2423_, v_sz_2422_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v_eq_2420_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_b_2424_);
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; lean_object* v_a_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2457_ = lean_unsigned_to_nat(0u);
v_a_2458_ = lean_array_uget_borrowed(v_as_2421_, v_i_2423_);
v___x_2459_ = lean_array_get_size(v_b_2424_);
v___x_2460_ = lean_nat_dec_lt(v___x_2457_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_inc(v_a_2458_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2424_, v_a_2458_, v___x_2460_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
v___y_2436_ = v___x_2461_;
goto v___jp_2435_;
}
else
{
if (v___x_2460_ == 0)
{
lean_object* v___x_2462_; 
lean_inc(v_a_2458_);
v___x_2462_ = lean_array_push(v_b_2424_, v_a_2458_);
v_a_2431_ = v___x_2462_;
goto v___jp_2430_;
}
else
{
size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = lean_usize_of_nat(v___x_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_eq_2420_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2420_, v_a_2458_, v_b_2424_, v___x_2463_, v___x_2464_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_unbox(v_a_2466_);
lean_dec(v_a_2466_);
lean_inc(v_a_2458_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2424_, v_a_2458_, v___x_2467_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
v___y_2436_ = v___x_2468_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_b_2424_);
lean_dec_ref(v_eq_2420_);
v_a_2469_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2465_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2465_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
v___jp_2430_:
{
size_t v___x_2432_; size_t v___x_2433_; 
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2423_, v___x_2432_);
v_i_2423_ = v___x_2433_;
v_b_2424_ = v_a_2431_;
goto _start;
}
v___jp_2435_:
{
if (lean_obj_tag(v___y_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2446_; 
v_a_2437_ = lean_ctor_get(v___y_2436_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___y_2436_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2439_ = v___y_2436_;
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___y_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; 
lean_dec_ref(v_eq_2420_);
v_a_2441_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v_a_2437_, 1);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
else
{
lean_object* v_a_2445_; 
lean_del_object(v___x_2439_);
v_a_2445_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v_a_2437_, 1);
v_a_2431_ = v_a_2445_;
goto v___jp_2430_;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v_eq_2420_);
v_a_2447_ = lean_ctor_get(v___y_2436_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___y_2436_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___y_2436_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___y_2436_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2477_, lean_object* v_as_2478_, lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2477_, v_as_2478_, v_sz_boxed_2487_, v_i_boxed_2488_, v_b_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_as_2478_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2490_, lean_object* v_xs_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_ret_2497_; size_t v_sz_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v_ret_2497_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2498_ = lean_array_size(v_xs_2491_);
v___x_2499_ = ((size_t)0ULL);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2490_, v_xs_2491_, v_sz_2498_, v___x_2499_, v_ret_2497_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2501_, lean_object* v_xs_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2501_, v_xs_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec_ref(v_xs_2502_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___x_2516_; size_t v_sz_2517_; size_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2516_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2517_ = lean_array_size(v_recArgInfos_2510_);
v___x_2518_ = ((size_t)0ULL);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2517_, v___x_2518_, v_recArgInfos_2510_);
v___x_2520_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2516_, v___x_2519_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec_ref(v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2528_, lean_object* v_eq_2529_, lean_object* v_xs_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2529_, v_xs_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_eq_2538_, lean_object* v_xs_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2537_, v_eq_2538_, v_xs_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec_ref(v_xs_2539_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2546_, lean_object* v_eq_2547_, lean_object* v_a_2548_, lean_object* v_as_2549_, size_t v_i_2550_, size_t v_stop_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2547_, v_a_2548_, v_as_2549_, v_i_2550_, v_stop_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_eq_2559_, lean_object* v_a_2560_, lean_object* v_as_2561_, lean_object* v_i_2562_, lean_object* v_stop_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
size_t v_i_boxed_2569_; size_t v_stop_boxed_2570_; lean_object* v_res_2571_; 
v_i_boxed_2569_ = lean_unbox_usize(v_i_2562_);
lean_dec(v_i_2562_);
v_stop_boxed_2570_ = lean_unbox_usize(v_stop_2563_);
lean_dec(v_stop_2563_);
v_res_2571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2558_, v_eq_2559_, v_a_2560_, v_as_2561_, v_i_boxed_2569_, v_stop_boxed_2570_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v_as_2561_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2572_, lean_object* v_eq_2573_, lean_object* v_as_2574_, size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_b_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2573_, v_as_2574_, v_sz_2575_, v_i_2576_, v_b_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_eq_2585_, lean_object* v_as_2586_, lean_object* v_sz_2587_, lean_object* v_i_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
size_t v_sz_boxed_2595_; size_t v_i_boxed_2596_; lean_object* v_res_2597_; 
v_sz_boxed_2595_ = lean_unbox_usize(v_sz_2587_);
lean_dec(v_sz_2587_);
v_i_boxed_2596_ = lean_unbox_usize(v_i_2588_);
lean_dec(v_i_2588_);
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2584_, v_eq_2585_, v_as_2586_, v_sz_boxed_2595_, v_i_boxed_2596_, v_b_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v_as_2586_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Expr_hasMVar(v_e_2598_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_e_2598_);
return v___x_2602_;
}
else
{
lean_object* v___x_2603_; lean_object* v_mctx_2604_; lean_object* v___x_2605_; lean_object* v_fst_2606_; lean_object* v_snd_2607_; lean_object* v___x_2608_; lean_object* v_cache_2609_; lean_object* v_zetaDeltaFVarIds_2610_; lean_object* v_postponed_2611_; lean_object* v_diag_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2621_; 
v___x_2603_ = lean_st_ref_get(v___y_2599_);
v_mctx_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc_ref(v_mctx_2604_);
lean_dec(v___x_2603_);
v___x_2605_ = l_Lean_instantiateMVarsCore(v_mctx_2604_, v_e_2598_);
v_fst_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_fst_2606_);
v_snd_2607_ = lean_ctor_get(v___x_2605_, 1);
lean_inc(v_snd_2607_);
lean_dec_ref(v___x_2605_);
v___x_2608_ = lean_st_ref_take(v___y_2599_);
v_cache_2609_ = lean_ctor_get(v___x_2608_, 1);
v_zetaDeltaFVarIds_2610_ = lean_ctor_get(v___x_2608_, 2);
v_postponed_2611_ = lean_ctor_get(v___x_2608_, 3);
v_diag_2612_ = lean_ctor_get(v___x_2608_, 4);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2608_, 0);
lean_dec(v_unused_2622_);
v___x_2614_ = v___x_2608_;
v_isShared_2615_ = v_isSharedCheck_2621_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_diag_2612_);
lean_inc(v_postponed_2611_);
lean_inc(v_zetaDeltaFVarIds_2610_);
lean_inc(v_cache_2609_);
lean_dec(v___x_2608_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2621_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_snd_2607_);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_snd_2607_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_cache_2609_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_zetaDeltaFVarIds_2610_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_postponed_2611_);
lean_ctor_set(v_reuseFailAlloc_2620_, 4, v_diag_2612_);
v___x_2617_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_st_ref_put(v___y_2599_, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_fst_2606_);
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2623_, v___y_2624_);
lean_dec(v___y_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2627_, v___y_2629_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2640_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2643_ = lean_unsigned_to_nat(109u);
v___x_2644_ = lean_unsigned_to_nat(216u);
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2647_ = l_mkPanicMessageWithDecl(v___x_2646_, v___x_2645_, v___x_2644_, v___x_2643_, v___x_2642_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2648_, size_t v_sz_2649_, size_t v_i_2650_, lean_object* v_bs_2651_){
_start:
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_usize_dec_lt(v_i_2650_, v_sz_2649_);
if (v___x_2652_ == 0)
{
return v_bs_2651_;
}
else
{
lean_object* v_v_2653_; lean_object* v___x_2654_; lean_object* v_bs_x27_2655_; lean_object* v___y_2657_; lean_object* v___x_2662_; 
v_v_2653_ = lean_array_uget(v_bs_2651_, v_i_2650_);
v___x_2654_ = lean_unsigned_to_nat(0u);
v_bs_x27_2655_ = lean_array_uset(v_bs_2651_, v_i_2650_, v___x_2654_);
v___x_2662_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2648_, v_v_2653_);
lean_dec(v_v_2653_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2664_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2663_);
v___y_2657_ = v___x_2664_;
goto v___jp_2656_;
}
else
{
lean_object* v_val_2665_; 
v_val_2665_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_val_2665_);
lean_dec_ref_known(v___x_2662_, 1);
v___y_2657_ = v_val_2665_;
goto v___jp_2656_;
}
v___jp_2656_:
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((size_t)1ULL);
v___x_2659_ = lean_usize_add(v_i_2650_, v___x_2658_);
v___x_2660_ = lean_array_uset(v_bs_x27_2655_, v_i_2650_, v___y_2657_);
v_i_2650_ = v___x_2659_;
v_bs_2651_ = v___x_2660_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2666_, lean_object* v_sz_2667_, lean_object* v_i_2668_, lean_object* v_bs_2669_){
_start:
{
size_t v_sz_boxed_2670_; size_t v_i_boxed_2671_; lean_object* v_res_2672_; 
v_sz_boxed_2670_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2671_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2666_, v_sz_boxed_2670_, v_i_boxed_2671_, v_bs_2669_);
lean_dec_ref(v___x_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2673_, size_t v_i_2674_, lean_object* v_bs_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_usize_dec_lt(v_i_2674_, v_sz_2673_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_bs_2675_);
return v___x_2682_;
}
else
{
lean_object* v_v_2683_; lean_object* v___x_2684_; 
v_v_2683_ = lean_array_uget_borrowed(v_bs_2675_, v_i_2674_);
lean_inc(v_v_2683_);
v___x_2684_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2683_, v___y_2677_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v_bs_x27_2687_; size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = lean_unsigned_to_nat(0u);
v_bs_x27_2687_ = lean_array_uset(v_bs_2675_, v_i_2674_, v___x_2686_);
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2674_, v___x_2688_);
v___x_2690_ = lean_array_uset(v_bs_x27_2687_, v_i_2674_, v_a_2685_);
v_i_2674_ = v___x_2689_;
v_bs_2675_ = v___x_2690_;
goto _start;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v_bs_2675_);
v_a_2692_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2684_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2684_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2700_, lean_object* v_i_2701_, lean_object* v_bs_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
size_t v_sz_boxed_2708_; size_t v_i_boxed_2709_; lean_object* v_res_2710_; 
v_sz_boxed_2708_ = lean_unbox_usize(v_sz_2700_);
lean_dec(v_sz_2700_);
v_i_boxed_2709_ = lean_unbox_usize(v_i_2701_);
lean_dec(v_i_2701_);
v_res_2710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2708_, v_i_boxed_2709_, v_bs_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2710_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2711_, lean_object* v___x_2712_, lean_object* v_as_2713_, size_t v_i_2714_, size_t v_stop_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = lean_usize_dec_eq(v_i_2714_, v_stop_2715_);
if (v___x_2716_ == 0)
{
uint8_t v___x_2717_; uint8_t v___y_2719_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2717_ = 1;
v___x_2723_ = lean_array_uget_borrowed(v_as_2713_, v_i_2714_);
v___x_2724_ = l_Lean_Expr_isFVar(v___x_2723_);
if (v___x_2724_ == 0)
{
v___y_2719_ = v_a_2711_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = lean_nat_dec_eq(v___x_2712_, v___x_2725_);
v___y_2719_ = v___x_2726_;
goto v___jp_2718_;
}
v___jp_2718_:
{
if (v___y_2719_ == 0)
{
size_t v___x_2720_; size_t v___x_2721_; 
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_add(v_i_2714_, v___x_2720_);
v_i_2714_ = v___x_2721_;
goto _start;
}
else
{
return v___x_2717_;
}
}
}
else
{
uint8_t v___x_2727_; 
v___x_2727_ = 0;
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2728_, lean_object* v___x_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_stop_2732_){
_start:
{
uint8_t v_a_9779__boxed_2733_; size_t v_i_boxed_2734_; size_t v_stop_boxed_2735_; uint8_t v_res_2736_; lean_object* v_r_2737_; 
v_a_9779__boxed_2733_ = lean_unbox(v_a_2728_);
v_i_boxed_2734_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_stop_boxed_2735_ = lean_unbox_usize(v_stop_2732_);
lean_dec(v_stop_2732_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9779__boxed_2733_, v___x_2729_, v_as_2730_, v_i_boxed_2734_, v_stop_boxed_2735_);
lean_dec_ref(v_as_2730_);
lean_dec(v___x_2729_);
v_r_2737_ = lean_box(v_res_2736_);
return v_r_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_ys_2740_, lean_object* v___x_2741_, lean_object* v_recArgInfo_2742_, lean_object* v___x_2743_, lean_object* v___x_2744_, lean_object* v_group_2745_, lean_object* v_as_2746_, size_t v_sz_2747_, size_t v_i_2748_, lean_object* v_b_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_a_2756_; uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_lt(v_i_2748_, v_sz_2747_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_b_2749_);
return v___x_2761_;
}
else
{
lean_object* v_snd_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2920_; 
v_snd_2762_ = lean_ctor_get(v_b_2749_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_b_2749_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v_b_2749_, 0);
lean_dec(v_unused_2921_);
v___x_2764_ = v_b_2749_;
v_isShared_2765_ = v_isSharedCheck_2920_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_snd_2762_);
lean_dec(v_b_2749_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2920_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_next_2766_; lean_object* v_upperBound_2767_; lean_object* v___x_2768_; 
v_next_2766_ = lean_ctor_get(v_snd_2762_, 0);
lean_inc(v_next_2766_);
v_upperBound_2767_ = lean_ctor_get(v_snd_2762_, 1);
v___x_2768_ = lean_box(0);
if (lean_obj_tag(v_next_2766_) == 0)
{
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
goto v___jp_2769_;
}
else
{
lean_object* v_val_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2919_; 
v_val_2774_ = lean_ctor_get(v_next_2766_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_next_2766_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2776_ = v_next_2766_;
v_isShared_2777_ = v_isSharedCheck_2919_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_val_2774_);
lean_dec(v_next_2766_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2919_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
uint8_t v___x_2778_; 
v___x_2778_ = lean_nat_dec_lt(v_val_2774_, v_upperBound_2767_);
if (v___x_2778_ == 0)
{
lean_del_object(v___x_2776_);
lean_dec(v_val_2774_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
goto v___jp_2769_;
}
else
{
lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2916_; 
lean_inc(v_upperBound_2767_);
lean_del_object(v___x_2764_);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_snd_2762_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2917_ = lean_ctor_get(v_snd_2762_, 1);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_snd_2762_, 0);
lean_dec(v_unused_2918_);
v___x_2780_ = v_snd_2762_;
v_isShared_2781_ = v_isSharedCheck_2916_;
goto v_resetjp_2779_;
}
else
{
lean_dec(v_snd_2762_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2916_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; 
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc_ref(v___x_2738_);
v___x_2782_ = lean_infer_type(v___x_2738_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_Meta_whnfD(v_a_2783_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v_a_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v_a_2786_ = lean_array_uget_borrowed(v_as_2746_, v_i_2748_);
v___x_2787_ = 0;
lean_inc(v_a_2786_);
v___x_2788_ = l_Lean_Meta_forallMetaTelescope(v_a_2786_, v___x_2787_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v_snd_2790_; lean_object* v_fst_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2891_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v_snd_2790_ = lean_ctor_get(v_a_2789_, 1);
v_fst_2791_ = lean_ctor_get(v_a_2789_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_a_2789_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2793_ = v_a_2789_;
v_isShared_2794_ = v_isSharedCheck_2891_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_snd_2790_);
lean_inc(v_fst_2791_);
lean_dec(v_a_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2891_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_snd_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2889_; 
v_snd_2795_ = lean_ctor_get(v_snd_2790_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_snd_2790_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v_snd_2790_, 0);
lean_dec(v_unused_2890_);
v___x_2797_ = v_snd_2790_;
v_isShared_2798_ = v_isSharedCheck_2889_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_snd_2795_);
lean_dec(v_snd_2790_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2889_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2795_, v_a_2785_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_nat_add(v_val_2774_, v___x_2801_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2802_);
v___x_2804_ = v___x_2776_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2804_);
v___x_2806_ = v___x_2780_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_upperBound_2767_);
v___x_2806_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_unbox(v_a_2800_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2809_; 
lean_dec(v_a_2800_);
lean_del_object(v___x_2793_);
lean_dec(v_fst_2791_);
lean_dec(v_val_2774_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2806_);
lean_ctor_set(v___x_2797_, 0, v___x_2768_);
v___x_2809_ = v___x_2797_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2806_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
v_a_2756_ = v___x_2809_;
goto v___jp_2755_;
}
}
else
{
size_t v_sz_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v_sz_2811_ = lean_array_size(v_fst_2791_);
v___x_2812_ = ((size_t)0ULL);
v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2811_, v___x_2812_, v_fst_2791_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = lean_nat_dec_eq(v___x_2739_, v___x_2819_);
v___x_2866_ = lean_array_get_size(v_a_2814_);
v___x_2867_ = lean_nat_dec_lt(v___x_2819_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_dec(v_a_2800_);
goto v___jp_2821_;
}
else
{
if (v___x_2867_ == 0)
{
lean_dec(v_a_2800_);
goto v___jp_2821_;
}
else
{
size_t v___x_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = lean_usize_of_nat(v___x_2866_);
v___x_2869_ = lean_unbox(v_a_2800_);
lean_dec(v_a_2800_);
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2869_, v___x_2739_, v_a_2814_, v___x_2812_, v___x_2868_);
if (v___x_2870_ == 0)
{
goto v___jp_2821_;
}
else
{
if (v___x_2820_ == 0)
{
lean_dec(v_a_2814_);
lean_del_object(v___x_2793_);
lean_dec(v_val_2774_);
goto v___jp_2815_;
}
else
{
goto v___jp_2821_;
}
}
}
}
v___jp_2815_:
{
lean_object* v___x_2817_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2806_);
lean_ctor_set(v___x_2797_, 0, v___x_2768_);
v___x_2817_ = v___x_2797_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2806_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
v_a_2756_ = v___x_2817_;
goto v___jp_2755_;
}
}
v___jp_2821_:
{
if (v___x_2820_ == 0)
{
uint8_t v___x_2822_; 
lean_del_object(v___x_2797_);
v___x_2822_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2814_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2824_; 
lean_dec(v_a_2814_);
lean_dec(v_val_2774_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v___x_2806_);
lean_ctor_set(v___x_2793_, 0, v___x_2768_);
v___x_2824_ = v___x_2793_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v___x_2806_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
v_a_2756_ = v___x_2824_;
goto v___jp_2755_;
}
}
else
{
lean_object* v___x_2826_; 
v___x_2826_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2740_, v_a_2814_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2857_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2857_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2857_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
if (lean_obj_tag(v_a_2827_) == 1)
{
lean_object* v___x_2832_; 
lean_dec_ref_known(v_a_2827_, 1);
lean_del_object(v___x_2829_);
lean_dec(v_a_2814_);
lean_dec(v_val_2774_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v___x_2806_);
lean_ctor_set(v___x_2793_, 0, v___x_2768_);
v___x_2832_ = v___x_2793_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2806_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
v_a_2756_ = v___x_2832_;
goto v___jp_2755_;
}
}
else
{
lean_object* v_fnName_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_a_2827_);
lean_dec_ref(v___x_2738_);
v_fnName_2834_ = lean_ctor_get(v_recArgInfo_2742_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_recArgInfo_2742_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; lean_object* v_unused_2853_; lean_object* v_unused_2854_; lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2852_ = lean_ctor_get(v_recArgInfo_2742_, 5);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_recArgInfo_2742_, 4);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_recArgInfo_2742_, 3);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_recArgInfo_2742_, 2);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_recArgInfo_2742_, 1);
lean_dec(v_unused_2856_);
v___x_2836_ = v_recArgInfo_2742_;
v_isShared_2837_ = v_isSharedCheck_2851_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_fnName_2834_);
lean_dec(v_recArgInfo_2742_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2851_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
size_t v_sz_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v_sz_2838_ = lean_array_size(v_a_2814_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2741_, v_sz_2838_, v___x_2812_, v_a_2814_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 5, v_val_2774_);
lean_ctor_set(v___x_2836_, 4, v_group_2745_);
lean_ctor_set(v___x_2836_, 3, v___x_2839_);
lean_ctor_set(v___x_2836_, 2, v___x_2744_);
lean_ctor_set(v___x_2836_, 1, v___x_2743_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_fnName_2834_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_group_2745_);
lean_ctor_set(v_reuseFailAlloc_2850_, 5, v_val_2774_);
v___x_2841_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 1, v___x_2806_);
lean_ctor_set(v___x_2793_, 0, v___x_2843_);
v___x_2845_ = v___x_2793_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2806_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2845_);
v___x_2847_ = v___x_2829_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2814_);
lean_dec_ref(v___x_2806_);
lean_del_object(v___x_2793_);
lean_dec(v_val_2774_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2858_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2826_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2826_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
else
{
lean_dec(v_a_2814_);
lean_del_object(v___x_2793_);
lean_dec(v_val_2774_);
goto v___jp_2815_;
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v___x_2806_);
lean_dec(v_a_2800_);
lean_del_object(v___x_2797_);
lean_del_object(v___x_2793_);
lean_dec(v_val_2774_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2871_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2813_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2813_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_del_object(v___x_2797_);
lean_del_object(v___x_2793_);
lean_dec(v_fst_2791_);
lean_del_object(v___x_2780_);
lean_del_object(v___x_2776_);
lean_dec(v_val_2774_);
lean_dec(v_upperBound_2767_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2881_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2799_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2799_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_a_2785_);
lean_del_object(v___x_2780_);
lean_del_object(v___x_2776_);
lean_dec(v_val_2774_);
lean_dec(v_upperBound_2767_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2892_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2788_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2788_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2780_);
lean_del_object(v___x_2776_);
lean_dec(v_val_2774_);
lean_dec(v_upperBound_2767_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2900_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2784_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2784_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2780_);
lean_del_object(v___x_2776_);
lean_dec(v_val_2774_);
lean_dec(v_upperBound_2767_);
lean_dec_ref(v_group_2745_);
lean_dec(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_recArgInfo_2742_);
lean_dec_ref(v___x_2738_);
v_a_2908_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2782_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2782_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
}
v___jp_2769_:
{
lean_object* v___x_2771_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2768_);
v___x_2771_ = v___x_2764_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_snd_2762_);
v___x_2771_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
}
}
}
v___jp_2755_:
{
size_t v___x_2757_; size_t v___x_2758_; 
v___x_2757_ = ((size_t)1ULL);
v___x_2758_ = lean_usize_add(v_i_2748_, v___x_2757_);
v_i_2748_ = v___x_2758_;
v_b_2749_ = v_a_2756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2922_ = _args[0];
lean_object* v___x_2923_ = _args[1];
lean_object* v_ys_2924_ = _args[2];
lean_object* v___x_2925_ = _args[3];
lean_object* v_recArgInfo_2926_ = _args[4];
lean_object* v___x_2927_ = _args[5];
lean_object* v___x_2928_ = _args[6];
lean_object* v_group_2929_ = _args[7];
lean_object* v_as_2930_ = _args[8];
lean_object* v_sz_2931_ = _args[9];
lean_object* v_i_2932_ = _args[10];
lean_object* v_b_2933_ = _args[11];
lean_object* v___y_2934_ = _args[12];
lean_object* v___y_2935_ = _args[13];
lean_object* v___y_2936_ = _args[14];
lean_object* v___y_2937_ = _args[15];
lean_object* v___y_2938_ = _args[16];
_start:
{
size_t v_sz_boxed_2939_; size_t v_i_boxed_2940_; lean_object* v_res_2941_; 
v_sz_boxed_2939_ = lean_unbox_usize(v_sz_2931_);
lean_dec(v_sz_2931_);
v_i_boxed_2940_ = lean_unbox_usize(v_i_2932_);
lean_dec(v_i_2932_);
v_res_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2922_, v___x_2923_, v_ys_2924_, v___x_2925_, v_recArgInfo_2926_, v___x_2927_, v___x_2928_, v_group_2929_, v_as_2930_, v_sz_boxed_2939_, v_i_boxed_2940_, v_b_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v_as_2930_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v_ys_2924_);
lean_dec(v___x_2923_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2942_, lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v_ys_2945_, lean_object* v_recArgInfo_2946_, lean_object* v___x_2947_, lean_object* v___x_2948_, lean_object* v_group_2949_, lean_object* v_as_2950_, size_t v_sz_2951_, size_t v_i_2952_, lean_object* v_b_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_a_2960_; uint8_t v___x_2964_; 
v___x_2964_ = lean_usize_dec_lt(v_i_2952_, v_sz_2951_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_b_2953_);
return v___x_2965_;
}
else
{
lean_object* v_snd_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3124_; 
v_snd_2966_ = lean_ctor_get(v_b_2953_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_b_2953_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_b_2953_, 0);
lean_dec(v_unused_3125_);
v___x_2968_ = v_b_2953_;
v_isShared_2969_ = v_isSharedCheck_3124_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_snd_2966_);
lean_dec(v_b_2953_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3124_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_next_2970_; lean_object* v_upperBound_2971_; lean_object* v___x_2972_; 
v_next_2970_ = lean_ctor_get(v_snd_2966_, 0);
lean_inc(v_next_2970_);
v_upperBound_2971_ = lean_ctor_get(v_snd_2966_, 1);
v___x_2972_ = lean_box(0);
if (lean_obj_tag(v_next_2970_) == 0)
{
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
goto v___jp_2973_;
}
else
{
lean_object* v_val_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3123_; 
v_val_2978_ = lean_ctor_get(v_next_2970_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_next_2970_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_2980_ = v_next_2970_;
v_isShared_2981_ = v_isSharedCheck_3123_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_val_2978_);
lean_dec(v_next_2970_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3123_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_nat_dec_lt(v_val_2978_, v_upperBound_2971_);
if (v___x_2982_ == 0)
{
lean_del_object(v___x_2980_);
lean_dec(v_val_2978_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
goto v___jp_2973_;
}
else
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3120_; 
lean_inc(v_upperBound_2971_);
lean_del_object(v___x_2968_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_snd_2966_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; lean_object* v_unused_3122_; 
v_unused_3121_ = lean_ctor_get(v_snd_2966_, 1);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_snd_2966_, 0);
lean_dec(v_unused_3122_);
v___x_2984_ = v_snd_2966_;
v_isShared_2985_ = v_isSharedCheck_3120_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v_snd_2966_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3120_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; 
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___x_2942_);
v___x_2986_ = lean_infer_type(v___x_2942_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = l_Lean_Meta_whnfD(v_a_2987_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_a_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_a_2990_ = lean_array_uget_borrowed(v_as_2950_, v_i_2952_);
v___x_2991_ = 0;
lean_inc(v_a_2990_);
v___x_2992_ = l_Lean_Meta_forallMetaTelescope(v_a_2990_, v___x_2991_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_snd_2994_; lean_object* v_fst_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3095_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v_snd_2994_ = lean_ctor_get(v_a_2993_, 1);
v_fst_2995_ = lean_ctor_get(v_a_2993_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_a_2993_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_2997_ = v_a_2993_;
v_isShared_2998_ = v_isSharedCheck_3095_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_snd_2994_);
lean_inc(v_fst_2995_);
lean_dec(v_a_2993_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3095_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_snd_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3093_; 
v_snd_2999_ = lean_ctor_get(v_snd_2994_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_snd_2994_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v_snd_2994_, 0);
lean_dec(v_unused_3094_);
v___x_3001_ = v_snd_2994_;
v_isShared_3002_ = v_isSharedCheck_3093_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_snd_2999_);
lean_dec(v_snd_2994_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3093_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2999_, v_a_2989_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_val_2978_, v___x_3005_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_3006_);
v___x_3008_ = v___x_2980_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_3008_);
v___x_3010_ = v___x_2984_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_upperBound_2971_);
v___x_3010_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_unbox(v_a_3004_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3013_; 
lean_dec(v_a_3004_);
lean_del_object(v___x_2997_);
lean_dec(v_fst_2995_);
lean_dec(v_val_2978_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3010_);
lean_ctor_set(v___x_3001_, 0, v___x_2972_);
v___x_3013_ = v___x_3001_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3010_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
v_a_2960_ = v___x_3013_;
goto v___jp_2959_;
}
}
else
{
size_t v_sz_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v_sz_3015_ = lean_array_size(v_fst_2995_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_3015_, v___x_3016_, v_fst_2995_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_nat_dec_eq(v___x_2943_, v___x_3023_);
v___x_3070_ = lean_array_get_size(v_a_3018_);
v___x_3071_ = lean_nat_dec_lt(v___x_3023_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec(v_a_3004_);
goto v___jp_3025_;
}
else
{
if (v___x_3071_ == 0)
{
lean_dec(v_a_3004_);
goto v___jp_3025_;
}
else
{
size_t v___x_3072_; uint8_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = lean_usize_of_nat(v___x_3070_);
v___x_3073_ = lean_unbox(v_a_3004_);
lean_dec(v_a_3004_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_3073_, v___x_2943_, v_a_3018_, v___x_3016_, v___x_3072_);
if (v___x_3074_ == 0)
{
goto v___jp_3025_;
}
else
{
if (v___x_3024_ == 0)
{
lean_dec(v_a_3018_);
lean_del_object(v___x_2997_);
lean_dec(v_val_2978_);
goto v___jp_3019_;
}
else
{
goto v___jp_3025_;
}
}
}
}
v___jp_3019_:
{
lean_object* v___x_3021_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3010_);
lean_ctor_set(v___x_3001_, 0, v___x_2972_);
v___x_3021_ = v___x_3001_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3010_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
v_a_2960_ = v___x_3021_;
goto v___jp_2959_;
}
}
v___jp_3025_:
{
if (v___x_3024_ == 0)
{
uint8_t v___x_3026_; 
lean_del_object(v___x_3001_);
v___x_3026_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_3018_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3028_; 
lean_dec(v_a_3018_);
lean_dec(v_val_2978_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v___x_3010_);
lean_ctor_set(v___x_2997_, 0, v___x_2972_);
v___x_3028_ = v___x_2997_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3010_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
v_a_2960_ = v___x_3028_;
goto v___jp_2959_;
}
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2945_, v_a_3018_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3061_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3061_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3061_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
if (lean_obj_tag(v_a_3031_) == 1)
{
lean_object* v___x_3036_; 
lean_dec_ref_known(v_a_3031_, 1);
lean_del_object(v___x_3033_);
lean_dec(v_a_3018_);
lean_dec(v_val_2978_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v___x_3010_);
lean_ctor_set(v___x_2997_, 0, v___x_2972_);
v___x_3036_ = v___x_2997_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3010_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
v_a_2960_ = v___x_3036_;
goto v___jp_2959_;
}
}
else
{
lean_object* v_fnName_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_3031_);
lean_dec_ref(v___x_2942_);
v_fnName_3038_ = lean_ctor_get(v_recArgInfo_2946_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_recArgInfo_2946_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; lean_object* v_unused_3057_; lean_object* v_unused_3058_; lean_object* v_unused_3059_; lean_object* v_unused_3060_; 
v_unused_3056_ = lean_ctor_get(v_recArgInfo_2946_, 5);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v_recArgInfo_2946_, 4);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v_recArgInfo_2946_, 3);
lean_dec(v_unused_3058_);
v_unused_3059_ = lean_ctor_get(v_recArgInfo_2946_, 2);
lean_dec(v_unused_3059_);
v_unused_3060_ = lean_ctor_get(v_recArgInfo_2946_, 1);
lean_dec(v_unused_3060_);
v___x_3040_ = v_recArgInfo_2946_;
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_fnName_3038_);
lean_dec(v_recArgInfo_2946_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3055_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
size_t v_sz_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v_sz_3042_ = lean_array_size(v_a_3018_);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2944_, v_sz_3042_, v___x_3016_, v_a_3018_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 5, v_val_2978_);
lean_ctor_set(v___x_3040_, 4, v_group_2949_);
lean_ctor_set(v___x_3040_, 3, v___x_3043_);
lean_ctor_set(v___x_3040_, 2, v___x_2948_);
lean_ctor_set(v___x_3040_, 1, v___x_2947_);
v___x_3045_ = v___x_3040_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_fnName_3038_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_3054_, 2, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_3054_, 3, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_group_2949_);
lean_ctor_set(v_reuseFailAlloc_3054_, 5, v_val_2978_);
v___x_3045_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v___x_3010_);
lean_ctor_set(v___x_2997_, 0, v___x_3047_);
v___x_3049_ = v___x_2997_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3010_);
v___x_3049_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3049_);
v___x_3051_ = v___x_3033_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_a_3018_);
lean_dec_ref(v___x_3010_);
lean_del_object(v___x_2997_);
lean_dec(v_val_2978_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3062_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3030_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3030_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
else
{
lean_dec(v_a_3018_);
lean_del_object(v___x_2997_);
lean_dec(v_val_2978_);
goto v___jp_3019_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v___x_3010_);
lean_dec(v_a_3004_);
lean_del_object(v___x_3001_);
lean_del_object(v___x_2997_);
lean_dec(v_val_2978_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3075_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3017_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3017_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_3001_);
lean_del_object(v___x_2997_);
lean_dec(v_fst_2995_);
lean_del_object(v___x_2984_);
lean_del_object(v___x_2980_);
lean_dec(v_val_2978_);
lean_dec(v_upperBound_2971_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3085_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3003_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3003_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_2989_);
lean_del_object(v___x_2984_);
lean_del_object(v___x_2980_);
lean_dec(v_val_2978_);
lean_dec(v_upperBound_2971_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3096_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_2992_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_2992_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_del_object(v___x_2984_);
lean_del_object(v___x_2980_);
lean_dec(v_val_2978_);
lean_dec(v_upperBound_2971_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3104_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_2988_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_2988_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_del_object(v___x_2984_);
lean_del_object(v___x_2980_);
lean_dec(v_val_2978_);
lean_dec(v_upperBound_2971_);
lean_dec_ref(v_group_2949_);
lean_dec(v___x_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_recArgInfo_2946_);
lean_dec_ref(v___x_2942_);
v_a_3112_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_2986_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_2986_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
}
v___jp_2973_:
{
lean_object* v___x_2975_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2972_);
v___x_2975_ = v___x_2968_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_snd_2966_);
v___x_2975_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
}
}
v___jp_2959_:
{
size_t v___x_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = lean_usize_add(v_i_2952_, v___x_2961_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2942_, v___x_2943_, v_ys_2945_, v___x_2944_, v_recArgInfo_2946_, v___x_2947_, v___x_2948_, v_group_2949_, v_as_2950_, v_sz_2951_, v___x_2962_, v_a_2960_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_3126_ = _args[0];
lean_object* v___x_3127_ = _args[1];
lean_object* v___x_3128_ = _args[2];
lean_object* v_ys_3129_ = _args[3];
lean_object* v_recArgInfo_3130_ = _args[4];
lean_object* v___x_3131_ = _args[5];
lean_object* v___x_3132_ = _args[6];
lean_object* v_group_3133_ = _args[7];
lean_object* v_as_3134_ = _args[8];
lean_object* v_sz_3135_ = _args[9];
lean_object* v_i_3136_ = _args[10];
lean_object* v_b_3137_ = _args[11];
lean_object* v___y_3138_ = _args[12];
lean_object* v___y_3139_ = _args[13];
lean_object* v___y_3140_ = _args[14];
lean_object* v___y_3141_ = _args[15];
lean_object* v___y_3142_ = _args[16];
_start:
{
size_t v_sz_boxed_3143_; size_t v_i_boxed_3144_; lean_object* v_res_3145_; 
v_sz_boxed_3143_ = lean_unbox_usize(v_sz_3135_);
lean_dec(v_sz_3135_);
v_i_boxed_3144_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3126_, v___x_3127_, v___x_3128_, v_ys_3129_, v_recArgInfo_3130_, v___x_3131_, v___x_3132_, v_group_3133_, v_as_3134_, v_sz_boxed_3143_, v_i_boxed_3144_, v_b_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v_as_3134_);
lean_dec_ref(v_ys_3129_);
lean_dec_ref(v___x_3128_);
lean_dec(v___x_3127_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3146_, lean_object* v_fixedParamPerm_3147_, lean_object* v_xs_3148_, lean_object* v_recArgPos_3149_, lean_object* v_a_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v_ys_3153_, lean_object* v_x_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_toIndGroupInfo_3160_; lean_object* v_all_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3200_; 
v_toIndGroupInfo_3160_ = lean_ctor_get(v_group_3146_, 0);
lean_inc_ref(v_toIndGroupInfo_3160_);
v_all_3161_ = lean_ctor_get(v_toIndGroupInfo_3160_, 0);
lean_inc_ref(v_ys_3153_);
lean_inc_ref(v_fixedParamPerm_3147_);
v___x_3162_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3147_, v_xs_3148_, v_ys_3153_);
v___x_3163_ = l_Lean_instInhabitedExpr;
v___x_3164_ = lean_array_get(v___x_3163_, v___x_3162_, v_recArgPos_3149_);
v___x_3165_ = lean_array_get_size(v_all_3161_);
v___x_3166_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3160_);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_toIndGroupInfo_3160_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; lean_object* v_unused_3202_; 
v_unused_3201_ = lean_ctor_get(v_toIndGroupInfo_3160_, 1);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_toIndGroupInfo_3160_, 0);
lean_dec(v_unused_3202_);
v___x_3168_ = v_toIndGroupInfo_3160_;
v_isShared_3169_ = v_isSharedCheck_3200_;
goto v_resetjp_3167_;
}
else
{
lean_dec(v_toIndGroupInfo_3160_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3200_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3165_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3166_);
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___x_3166_);
v___x_3172_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; size_t v_sz_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3173_ = lean_box(0);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
v_sz_3175_ = lean_array_size(v_a_3150_);
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3164_, v___x_3151_, v___x_3162_, v_ys_3153_, v___x_3152_, v_fixedParamPerm_3147_, v_recArgPos_3149_, v_group_3146_, v_a_3150_, v_sz_3175_, v___x_3176_, v___x_3174_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec_ref(v_ys_3153_);
lean_dec_ref(v___x_3162_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3190_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3190_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3190_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_fst_3182_; 
v_fst_3182_ = lean_ctor_get(v_a_3178_, 0);
lean_inc(v_fst_3182_);
lean_dec(v_a_3178_);
if (lean_obj_tag(v_fst_3182_) == 0)
{
lean_object* v___x_3184_; 
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3173_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3173_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
else
{
lean_object* v_val_3186_; lean_object* v___x_3188_; 
v_val_3186_ = lean_ctor_get(v_fst_3182_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_fst_3182_, 1);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v_val_3186_);
v___x_3188_ = v___x_3180_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_val_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
v_a_3191_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3177_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3177_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3203_, lean_object* v_fixedParamPerm_3204_, lean_object* v_xs_3205_, lean_object* v_recArgPos_3206_, lean_object* v_a_3207_, lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v_ys_3210_, lean_object* v_x_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3203_, v_fixedParamPerm_3204_, v_xs_3205_, v_recArgPos_3206_, v_a_3207_, v___x_3208_, v___x_3209_, v_ys_3210_, v_x_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v_x_3211_);
lean_dec(v___x_3208_);
lean_dec_ref(v_a_3207_);
lean_dec_ref(v_xs_3205_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3218_, lean_object* v_a_3219_, lean_object* v_xs_3220_, lean_object* v_value_3221_, lean_object* v_as_3222_, size_t v_i_3223_, size_t v_stop_3224_, lean_object* v_b_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_a_3232_; lean_object* v_val_3237_; uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_eq(v_i_3223_, v_stop_3224_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_fixedParamPerm_3241_; lean_object* v_recArgPos_3242_; lean_object* v_indGroupInst_3243_; lean_object* v___x_3244_; 
v___x_3240_ = lean_array_uget_borrowed(v_as_3222_, v_i_3223_);
v_fixedParamPerm_3241_ = lean_ctor_get(v___x_3240_, 1);
v_recArgPos_3242_ = lean_ctor_get(v___x_3240_, 2);
v_indGroupInst_3243_ = lean_ctor_get(v___x_3240_, 4);
lean_inc_ref(v_indGroupInst_3243_);
lean_inc_ref(v_group_3218_);
v___x_3244_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3218_, v_indGroupInst_3243_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; uint8_t v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = lean_unbox(v_a_3245_);
lean_dec(v_a_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3247_ = lean_array_get_size(v_a_3219_);
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = lean_nat_dec_eq(v___x_3247_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___f_3250_; lean_object* v___x_3251_; 
lean_inc(v___x_3240_);
lean_inc_ref(v_a_3219_);
lean_inc(v_recArgPos_3242_);
lean_inc_ref(v_xs_3220_);
lean_inc_ref(v_fixedParamPerm_3241_);
lean_inc_ref(v_group_3218_);
v___f_3250_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3250_, 0, v_group_3218_);
lean_closure_set(v___f_3250_, 1, v_fixedParamPerm_3241_);
lean_closure_set(v___f_3250_, 2, v_xs_3220_);
lean_closure_set(v___f_3250_, 3, v_recArgPos_3242_);
lean_closure_set(v___f_3250_, 4, v_a_3219_);
lean_closure_set(v___f_3250_, 5, v___x_3247_);
lean_closure_set(v___f_3250_, 6, v___x_3240_);
lean_inc_ref(v_value_3221_);
v___x_3251_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3221_, v___f_3250_, v___x_3249_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
if (lean_obj_tag(v_a_3252_) == 0)
{
v_a_3232_ = v_b_3225_;
goto v___jp_3231_;
}
else
{
lean_object* v_val_3253_; 
v_val_3253_ = lean_ctor_get(v_a_3252_, 0);
lean_inc(v_val_3253_);
lean_dec_ref_known(v_a_3252_, 1);
v_val_3237_ = v_val_3253_;
goto v___jp_3236_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_b_3225_);
lean_dec_ref(v_value_3221_);
lean_dec_ref(v_xs_3220_);
lean_dec_ref(v_a_3219_);
lean_dec_ref(v_group_3218_);
v_a_3254_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3251_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3251_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
v_a_3232_ = v_b_3225_;
goto v___jp_3231_;
}
}
else
{
lean_inc(v___x_3240_);
v_val_3237_ = v___x_3240_;
goto v___jp_3236_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_b_3225_);
lean_dec_ref(v_value_3221_);
lean_dec_ref(v_xs_3220_);
lean_dec_ref(v_a_3219_);
lean_dec_ref(v_group_3218_);
v_a_3262_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3244_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3244_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v___x_3270_; 
lean_dec_ref(v_value_3221_);
lean_dec_ref(v_xs_3220_);
lean_dec_ref(v_a_3219_);
lean_dec_ref(v_group_3218_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_b_3225_);
return v___x_3270_;
}
v___jp_3231_:
{
size_t v___x_3233_; size_t v___x_3234_; 
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_i_3223_, v___x_3233_);
v_i_3223_ = v___x_3234_;
v_b_3225_ = v_a_3232_;
goto _start;
}
v___jp_3236_:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_array_push(v_b_3225_, v_val_3237_);
v_a_3232_ = v___x_3238_;
goto v___jp_3231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3271_, lean_object* v_a_3272_, lean_object* v_xs_3273_, lean_object* v_value_3274_, lean_object* v_as_3275_, lean_object* v_i_3276_, lean_object* v_stop_3277_, lean_object* v_b_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
size_t v_i_boxed_3284_; size_t v_stop_boxed_3285_; lean_object* v_res_3286_; 
v_i_boxed_3284_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_stop_boxed_3285_ = lean_unbox_usize(v_stop_3277_);
lean_dec(v_stop_3277_);
v_res_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3271_, v_a_3272_, v_xs_3273_, v_value_3274_, v_as_3275_, v_i_boxed_3284_, v_stop_boxed_3285_, v_b_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec_ref(v_as_3275_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3287_, lean_object* v_a_3288_, lean_object* v_xs_3289_, lean_object* v_value_3290_, lean_object* v_as_3291_, lean_object* v_start_3292_, lean_object* v_stop_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3300_ = lean_nat_dec_lt(v_start_3292_, v_stop_3293_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
lean_dec_ref(v_value_3290_);
lean_dec_ref(v_xs_3289_);
lean_dec_ref(v_a_3288_);
lean_dec_ref(v_group_3287_);
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = lean_array_get_size(v_as_3291_);
v___x_3303_ = lean_nat_dec_le(v_stop_3293_, v___x_3302_);
if (v___x_3303_ == 0)
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_nat_dec_lt(v_start_3292_, v___x_3302_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_dec_ref(v_value_3290_);
lean_dec_ref(v_xs_3289_);
lean_dec_ref(v_a_3288_);
lean_dec_ref(v_group_3287_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3299_);
return v___x_3305_;
}
else
{
size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = lean_usize_of_nat(v_start_3292_);
v___x_3307_ = lean_usize_of_nat(v___x_3302_);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3287_, v_a_3288_, v_xs_3289_, v_value_3290_, v_as_3291_, v___x_3306_, v___x_3307_, v___x_3299_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3308_;
}
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_usize_of_nat(v_start_3292_);
v___x_3310_ = lean_usize_of_nat(v_stop_3293_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3287_, v_a_3288_, v_xs_3289_, v_value_3290_, v_as_3291_, v___x_3309_, v___x_3310_, v___x_3299_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3312_, lean_object* v_a_3313_, lean_object* v_xs_3314_, lean_object* v_value_3315_, lean_object* v_as_3316_, lean_object* v_start_3317_, lean_object* v_stop_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3312_, v_a_3313_, v_xs_3314_, v_value_3315_, v_as_3316_, v_start_3317_, v_stop_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v_stop_3318_);
lean_dec(v_start_3317_);
lean_dec_ref(v_as_3316_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3325_, lean_object* v_xs_3326_, lean_object* v_value_3327_, lean_object* v_recArgInfos_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___x_3334_; 
lean_inc_ref(v_group_3325_);
v___x_3334_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3325_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = lean_array_get_size(v_recArgInfos_3328_);
v___x_3338_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3325_, v_a_3335_, v_xs_3326_, v_value_3327_, v_recArgInfos_3328_, v___x_3336_, v___x_3337_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
return v___x_3338_;
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v_value_3327_);
lean_dec_ref(v_xs_3326_);
lean_dec_ref(v_group_3325_);
v_a_3339_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3334_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3334_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3347_, lean_object* v_xs_3348_, lean_object* v_value_3349_, lean_object* v_recArgInfos_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Elab_Structural_argsInGroup(v_group_3347_, v_xs_3348_, v_value_3349_, v_recArgInfos_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec_ref(v_recArgInfos_3350_);
return v_res_3356_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(10u);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3360_, lean_object* v_i_3361_, lean_object* v_acc_3362_){
_start:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = lean_array_get_size(v_xss_3360_);
v___x_3364_ = lean_nat_dec_lt(v_i_3361_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_mk_empty_array_with_capacity(v___x_3365_);
v___x_3367_ = lean_array_push(v___x_3366_, v_acc_3362_);
return v___x_3367_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3368_ = lean_array_fget_borrowed(v_xss_3360_, v_i_3361_);
v___x_3369_ = lean_unsigned_to_nat(0u);
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3371_ = lean_array_get_size(v___x_3368_);
v___x_3372_ = lean_nat_dec_lt(v___x_3369_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_dec_ref(v_acc_3362_);
return v___x_3370_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_le(v___x_3371_, v___x_3371_);
if (v___x_3373_ == 0)
{
if (v___x_3372_ == 0)
{
lean_dec_ref(v_acc_3362_);
return v___x_3370_;
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3371_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3361_, v_acc_3362_, v_xss_3360_, v___x_3368_, v___x_3374_, v___x_3375_, v___x_3370_);
return v___x_3376_;
}
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3371_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3361_, v_acc_3362_, v_xss_3360_, v___x_3368_, v___x_3377_, v___x_3378_, v___x_3370_);
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3380_, lean_object* v_acc_3381_, lean_object* v_xss_3382_, lean_object* v_as_3383_, size_t v_i_3384_, size_t v_stop_3385_, lean_object* v_b_3386_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_usize_dec_eq(v_i_3384_, v_stop_3385_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; size_t v___x_3394_; size_t v___x_3395_; 
v___x_3388_ = lean_array_uget_borrowed(v_as_3383_, v_i_3384_);
v___x_3389_ = lean_unsigned_to_nat(1u);
v___x_3390_ = lean_nat_add(v_i_3380_, v___x_3389_);
lean_inc(v___x_3388_);
lean_inc_ref(v_acc_3381_);
v___x_3391_ = lean_array_push(v_acc_3381_, v___x_3388_);
v___x_3392_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3382_, v___x_3390_, v___x_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = l_Array_append___redArg(v_b_3386_, v___x_3392_);
lean_dec_ref(v___x_3392_);
v___x_3394_ = ((size_t)1ULL);
v___x_3395_ = lean_usize_add(v_i_3384_, v___x_3394_);
v_i_3384_ = v___x_3395_;
v_b_3386_ = v___x_3393_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3381_);
return v_b_3386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3397_, lean_object* v_acc_3398_, lean_object* v_xss_3399_, lean_object* v_as_3400_, lean_object* v_i_3401_, lean_object* v_stop_3402_, lean_object* v_b_3403_){
_start:
{
size_t v_i_boxed_3404_; size_t v_stop_boxed_3405_; lean_object* v_res_3406_; 
v_i_boxed_3404_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_stop_boxed_3405_ = lean_unbox_usize(v_stop_3402_);
lean_dec(v_stop_3402_);
v_res_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3397_, v_acc_3398_, v_xss_3399_, v_as_3400_, v_i_boxed_3404_, v_stop_boxed_3405_, v_b_3403_);
lean_dec_ref(v_as_3400_);
lean_dec_ref(v_xss_3399_);
lean_dec(v_i_3397_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3407_, lean_object* v_i_3408_, lean_object* v_acc_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3407_, v_i_3408_, v_acc_3409_);
lean_dec(v_i_3408_);
lean_dec_ref(v_xss_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3411_, lean_object* v_xss_3412_, lean_object* v_i_3413_, lean_object* v_acc_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3412_, v_i_3413_, v_acc_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_xss_3417_, lean_object* v_i_3418_, lean_object* v_acc_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3416_, v_xss_3417_, v_i_3418_, v_acc_3419_);
lean_dec(v_i_3418_);
lean_dec_ref(v_xss_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3421_, lean_object* v_i_3422_, lean_object* v_acc_3423_, lean_object* v_xss_3424_, lean_object* v_as_3425_, size_t v_i_3426_, size_t v_stop_3427_, lean_object* v_b_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3422_, v_acc_3423_, v_xss_3424_, v_as_3425_, v_i_3426_, v_stop_3427_, v_b_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3430_, lean_object* v_i_3431_, lean_object* v_acc_3432_, lean_object* v_xss_3433_, lean_object* v_as_3434_, lean_object* v_i_3435_, lean_object* v_stop_3436_, lean_object* v_b_3437_){
_start:
{
size_t v_i_boxed_3438_; size_t v_stop_boxed_3439_; lean_object* v_res_3440_; 
v_i_boxed_3438_ = lean_unbox_usize(v_i_3435_);
lean_dec(v_i_3435_);
v_stop_boxed_3439_ = lean_unbox_usize(v_stop_3436_);
lean_dec(v_stop_3436_);
v_res_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3430_, v_i_3431_, v_acc_3432_, v_xss_3433_, v_as_3434_, v_i_boxed_3438_, v_stop_boxed_3439_, v_b_3437_);
lean_dec_ref(v_as_3434_);
lean_dec_ref(v_xss_3433_);
lean_dec(v_i_3431_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3441_, size_t v_i_3442_, size_t v_stop_3443_, lean_object* v_b_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_eq(v_i_3442_, v_stop_3443_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; size_t v___x_3449_; size_t v___x_3450_; 
v___x_3446_ = lean_array_uget_borrowed(v_as_3441_, v_i_3442_);
v___x_3447_ = lean_array_get_size(v___x_3446_);
v___x_3448_ = lean_nat_mul(v_b_3444_, v___x_3447_);
lean_dec(v_b_3444_);
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3442_, v___x_3449_);
v_i_3442_ = v___x_3450_;
v_b_3444_ = v___x_3448_;
goto _start;
}
else
{
return v_b_3444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3452_, lean_object* v_i_3453_, lean_object* v_stop_3454_, lean_object* v_b_3455_){
_start:
{
size_t v_i_boxed_3456_; size_t v_stop_boxed_3457_; lean_object* v_res_3458_; 
v_i_boxed_3456_ = lean_unbox_usize(v_i_3453_);
lean_dec(v_i_3453_);
v_stop_boxed_3457_ = lean_unbox_usize(v_stop_3454_);
lean_dec(v_stop_3454_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3452_, v_i_boxed_3456_, v_stop_boxed_3457_, v_b_3455_);
lean_dec_ref(v_as_3452_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3459_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___y_3464_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3460_ = lean_unsigned_to_nat(10u);
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_array_get_size(v_xss_3459_);
v___x_3471_ = lean_nat_dec_lt(v___x_3462_, v___x_3470_);
if (v___x_3471_ == 0)
{
v___y_3464_ = v___x_3461_;
goto v___jp_3463_;
}
else
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_nat_dec_le(v___x_3470_, v___x_3470_);
if (v___x_3472_ == 0)
{
if (v___x_3471_ == 0)
{
v___y_3464_ = v___x_3461_;
goto v___jp_3463_;
}
else
{
size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = lean_usize_of_nat(v___x_3470_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3459_, v___x_3473_, v___x_3474_, v___x_3461_);
v___y_3464_ = v___x_3475_;
goto v___jp_3463_;
}
}
else
{
size_t v___x_3476_; size_t v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = lean_usize_of_nat(v___x_3470_);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3459_, v___x_3476_, v___x_3477_, v___x_3461_);
v___y_3464_ = v___x_3478_;
goto v___jp_3463_;
}
}
v___jp_3463_:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_nat_dec_lt(v___x_3460_, v___y_3464_);
lean_dec(v___y_3464_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3467_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3459_, v___x_3462_, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
else
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_box(0);
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3479_);
lean_dec_ref(v_xss_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3481_, lean_object* v_xss_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3484_, lean_object* v_xss_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3484_, v_xss_3485_);
lean_dec_ref(v_xss_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3487_, lean_object* v_as_3488_, size_t v_i_3489_, size_t v_stop_3490_, lean_object* v_b_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3488_, v_i_3489_, v_stop_3490_, v_b_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3493_, lean_object* v_as_3494_, lean_object* v_i_3495_, lean_object* v_stop_3496_, lean_object* v_b_3497_){
_start:
{
size_t v_i_boxed_3498_; size_t v_stop_boxed_3499_; lean_object* v_res_3500_; 
v_i_boxed_3498_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_stop_boxed_3499_ = lean_unbox_usize(v_stop_3496_);
lean_dec(v_stop_3496_);
v_res_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3493_, v_as_3494_, v_i_boxed_3498_, v_stop_boxed_3499_, v_b_3497_);
lean_dec_ref(v_as_3494_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3501_, size_t v_i_3502_, size_t v_stop_3503_, lean_object* v_b_3504_){
_start:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_usize_dec_eq(v_i_3502_, v_stop_3503_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; size_t v___x_3508_; size_t v___x_3509_; 
v___x_3506_ = lean_array_uget_borrowed(v_as_3501_, v_i_3502_);
v___x_3507_ = l_Array_append___redArg(v_b_3504_, v___x_3506_);
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3502_, v___x_3508_);
v_i_3502_ = v___x_3509_;
v_b_3504_ = v___x_3507_;
goto _start;
}
else
{
return v_b_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3511_, lean_object* v_i_3512_, lean_object* v_stop_3513_, lean_object* v_b_3514_){
_start:
{
size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_i_boxed_3515_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3513_);
lean_dec(v_stop_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3511_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3514_);
lean_dec_ref(v_as_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
if (lean_obj_tag(v_a_3518_) == 0)
{
lean_object* v___x_3520_; 
v___x_3520_ = l_List_reverse___redArg(v_a_3519_);
return v___x_3520_;
}
else
{
lean_object* v_head_3521_; lean_object* v_tail_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3532_; 
v_head_3521_ = lean_ctor_get(v_a_3518_, 0);
v_tail_3522_ = lean_ctor_get(v_a_3518_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3518_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3524_ = v_a_3518_;
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_tail_3522_);
lean_inc(v_head_3521_);
lean_dec(v_a_3518_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3532_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3526_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3521_);
v___x_3527_ = l_Lean_MessageData_ofFormat(v___x_3526_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_a_3519_);
lean_ctor_set(v___x_3524_, 0, v___x_3527_);
v___x_3529_ = v___x_3524_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_a_3519_);
v___x_3529_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
v_a_3518_ = v_tail_3522_;
v_a_3519_ = v___x_3529_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3533_, size_t v_i_3534_, lean_object* v_bs_3535_){
_start:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_usize_dec_lt(v_i_3534_, v_sz_3533_);
if (v___x_3536_ == 0)
{
return v_bs_3535_;
}
else
{
lean_object* v_v_3537_; lean_object* v___x_3538_; lean_object* v_bs_x27_3539_; lean_object* v___x_3540_; size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
v_v_3537_ = lean_array_uget(v_bs_3535_, v_i_3534_);
v___x_3538_ = lean_unsigned_to_nat(0u);
v_bs_x27_3539_ = lean_array_uset(v_bs_3535_, v_i_3534_, v___x_3538_);
v___x_3540_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3537_);
lean_dec(v_v_3537_);
v___x_3541_ = ((size_t)1ULL);
v___x_3542_ = lean_usize_add(v_i_3534_, v___x_3541_);
v___x_3543_ = lean_array_uset(v_bs_x27_3539_, v_i_3534_, v___x_3540_);
v_i_3534_ = v___x_3542_;
v_bs_3535_ = v___x_3543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3545_, lean_object* v_i_3546_, lean_object* v_bs_3547_){
_start:
{
size_t v_sz_boxed_3548_; size_t v_i_boxed_3549_; lean_object* v_res_3550_; 
v_sz_boxed_3548_ = lean_unbox_usize(v_sz_3545_);
lean_dec(v_sz_3545_);
v_i_boxed_3549_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_res_3550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3548_, v_i_boxed_3549_, v_bs_3547_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3551_, lean_object* v_as_3552_, size_t v_sz_3553_, size_t v_i_3554_, lean_object* v_b_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_usize_dec_lt(v_i_3554_, v_sz_3553_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref(v_xs_3551_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_b_3555_);
return v___x_3562_;
}
else
{
lean_object* v_snd_3563_; lean_object* v_snd_3564_; lean_object* v_snd_3565_; lean_object* v_snd_3566_; lean_object* v_fst_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3711_; 
v_snd_3563_ = lean_ctor_get(v_b_3555_, 1);
lean_inc(v_snd_3563_);
v_snd_3564_ = lean_ctor_get(v_snd_3563_, 1);
lean_inc(v_snd_3564_);
v_snd_3565_ = lean_ctor_get(v_snd_3564_, 1);
lean_inc(v_snd_3565_);
v_snd_3566_ = lean_ctor_get(v_snd_3565_, 1);
lean_inc(v_snd_3566_);
v_fst_3567_ = lean_ctor_get(v_b_3555_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_b_3555_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_b_3555_, 1);
lean_dec(v_unused_3712_);
v___x_3569_ = v_b_3555_;
v_isShared_3570_ = v_isSharedCheck_3711_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_fst_3567_);
lean_dec(v_b_3555_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3711_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v_fst_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3709_; 
v_fst_3571_ = lean_ctor_get(v_snd_3563_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_snd_3563_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_snd_3563_, 1);
lean_dec(v_unused_3710_);
v___x_3573_ = v_snd_3563_;
v_isShared_3574_ = v_isSharedCheck_3709_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_fst_3571_);
lean_dec(v_snd_3563_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3709_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_fst_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3707_; 
v_fst_3575_ = lean_ctor_get(v_snd_3564_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_snd_3564_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v_snd_3564_, 1);
lean_dec(v_unused_3708_);
v___x_3577_ = v_snd_3564_;
v_isShared_3578_ = v_isSharedCheck_3707_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_fst_3575_);
lean_dec(v_snd_3564_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3707_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_fst_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3705_; 
v_fst_3579_ = lean_ctor_get(v_snd_3565_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_snd_3565_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_snd_3565_, 1);
lean_dec(v_unused_3706_);
v___x_3581_ = v_snd_3565_;
v_isShared_3582_ = v_isSharedCheck_3705_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_fst_3579_);
lean_dec(v_snd_3565_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3705_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_array_3583_; lean_object* v_start_3584_; lean_object* v_stop_3585_; uint8_t v___x_3586_; 
v_array_3583_ = lean_ctor_get(v_snd_3566_, 0);
v_start_3584_ = lean_ctor_get(v_snd_3566_, 1);
v_stop_3585_ = lean_ctor_get(v_snd_3566_, 2);
v___x_3586_ = lean_nat_dec_lt(v_start_3584_, v_stop_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v_xs_3551_);
if (v_isShared_3582_ == 0)
{
v___x_3588_ = v___x_3581_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_fst_3579_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_snd_3566_);
v___x_3588_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___x_3588_);
v___x_3590_ = v___x_3577_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3592_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3590_);
v___x_3592_ = v___x_3573_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_fst_3571_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3592_);
v___x_3594_ = v___x_3569_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_fst_3567_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
}
}
}
}
else
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3701_; 
lean_inc(v_stop_3585_);
lean_inc(v_start_3584_);
lean_inc_ref(v_array_3583_);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_snd_3566_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; lean_object* v_unused_3703_; lean_object* v_unused_3704_; 
v_unused_3702_ = lean_ctor_get(v_snd_3566_, 2);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v_snd_3566_, 1);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v_snd_3566_, 0);
lean_dec(v_unused_3704_);
v___x_3601_ = v_snd_3566_;
v_isShared_3602_ = v_isSharedCheck_3701_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v_snd_3566_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3701_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v_array_3603_; lean_object* v_start_3604_; lean_object* v_stop_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v_array_3603_ = lean_ctor_get(v_fst_3579_, 0);
v_start_3604_ = lean_ctor_get(v_fst_3579_, 1);
v_stop_3605_ = lean_ctor_get(v_fst_3579_, 2);
v___x_3606_ = lean_array_fget(v_array_3583_, v_start_3584_);
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = lean_nat_add(v_start_3584_, v___x_3607_);
lean_dec(v_start_3584_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 1, v___x_3608_);
v___x_3610_ = v___x_3601_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_array_3583_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_stop_3585_);
v___x_3610_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_lt(v_start_3604_, v_stop_3605_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3613_; 
lean_dec(v___x_3606_);
lean_dec_ref(v_xs_3551_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3610_);
v___x_3613_ = v___x_3581_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_fst_3579_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3610_);
v___x_3613_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___x_3613_);
v___x_3615_ = v___x_3577_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3615_);
v___x_3617_ = v___x_3573_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_fst_3571_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3617_);
v___x_3619_ = v___x_3569_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_fst_3567_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
}
}
}
}
else
{
lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3696_; 
lean_inc(v_stop_3605_);
lean_inc(v_start_3604_);
lean_inc_ref(v_array_3603_);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_fst_3579_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; lean_object* v_unused_3698_; lean_object* v_unused_3699_; 
v_unused_3697_ = lean_ctor_get(v_fst_3579_, 2);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_fst_3579_, 1);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_fst_3579_, 0);
lean_dec(v_unused_3699_);
v___x_3626_ = v_fst_3579_;
v_isShared_3627_ = v_isSharedCheck_3696_;
goto v_resetjp_3625_;
}
else
{
lean_dec(v_fst_3579_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3696_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v_array_3628_; lean_object* v_start_3629_; lean_object* v_stop_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
v_array_3628_ = lean_ctor_get(v_fst_3575_, 0);
v_start_3629_ = lean_ctor_get(v_fst_3575_, 1);
v_stop_3630_ = lean_ctor_get(v_fst_3575_, 2);
v___x_3631_ = lean_array_fget(v_array_3603_, v_start_3604_);
v___x_3632_ = lean_nat_add(v_start_3604_, v___x_3607_);
lean_dec(v_start_3604_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3632_);
v___x_3634_ = v___x_3626_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_array_3603_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_stop_3605_);
v___x_3634_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_nat_dec_lt(v_start_3629_, v_stop_3630_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3637_; 
lean_dec(v___x_3631_);
lean_dec(v___x_3606_);
lean_dec_ref(v_xs_3551_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3610_);
lean_ctor_set(v___x_3581_, 0, v___x_3634_);
v___x_3637_ = v___x_3581_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3610_);
v___x_3637_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___x_3637_);
v___x_3639_ = v___x_3577_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3639_);
v___x_3641_ = v___x_3573_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_fst_3571_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3643_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3641_);
v___x_3643_ = v___x_3569_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_fst_3567_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
}
}
}
else
{
lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3691_; 
lean_inc(v_stop_3630_);
lean_inc(v_start_3629_);
lean_inc_ref(v_array_3628_);
lean_del_object(v___x_3569_);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_fst_3575_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3692_ = lean_ctor_get(v_fst_3575_, 2);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_fst_3575_, 1);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_fst_3575_, 0);
lean_dec(v_unused_3694_);
v___x_3650_ = v_fst_3575_;
v_isShared_3651_ = v_isSharedCheck_3691_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v_fst_3575_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3691_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_a_3652_ = lean_array_uget_borrowed(v_as_3552_, v_i_3554_);
v___x_3653_ = lean_array_fget_borrowed(v_array_3628_, v_start_3629_);
lean_inc(v___x_3653_);
lean_inc_ref(v_xs_3551_);
lean_inc(v_a_3652_);
v___x_3654_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3652_, v___x_3606_, v_xs_3551_, v___x_3653_, v___x_3631_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v_fst_3656_; lean_object* v_snd_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3682_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v_fst_3656_ = lean_ctor_get(v_a_3655_, 0);
v_snd_3657_ = lean_ctor_get(v_a_3655_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3659_ = v_a_3655_;
v_isShared_3660_ = v_isSharedCheck_3682_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_snd_3657_);
lean_inc(v_fst_3656_);
lean_dec(v_a_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3682_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_nat_add(v_start_3629_, v___x_3607_);
lean_dec(v_start_3629_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v___x_3661_);
v___x_3663_ = v___x_3650_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_array_3628_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_stop_3630_);
v___x_3663_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_fst_3567_);
lean_ctor_set(v___x_3664_, 1, v_snd_3657_);
v___x_3665_ = lean_array_push(v_fst_3571_, v_fst_3656_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 1, v___x_3610_);
lean_ctor_set(v___x_3659_, 0, v___x_3634_);
v___x_3667_ = v___x_3659_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3610_);
v___x_3667_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3667_);
lean_ctor_set(v___x_3581_, 0, v___x_3663_);
v___x_3669_ = v___x_3581_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___x_3669_);
lean_ctor_set(v___x_3577_, 0, v___x_3665_);
v___x_3671_ = v___x_3577_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3671_);
lean_ctor_set(v___x_3573_, 0, v___x_3664_);
v___x_3673_ = v___x_3573_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
size_t v___x_3674_; size_t v___x_3675_; 
v___x_3674_ = ((size_t)1ULL);
v___x_3675_ = lean_usize_add(v_i_3554_, v___x_3674_);
v_i_3554_ = v___x_3675_;
v_b_3555_ = v___x_3673_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3650_);
lean_dec_ref(v___x_3634_);
lean_dec(v_stop_3630_);
lean_dec(v_start_3629_);
lean_dec_ref(v_array_3628_);
lean_dec_ref(v___x_3610_);
lean_del_object(v___x_3581_);
lean_del_object(v___x_3577_);
lean_del_object(v___x_3573_);
lean_dec(v_fst_3571_);
lean_dec(v_fst_3567_);
lean_dec_ref(v_xs_3551_);
v_a_3683_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3654_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3654_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3713_, lean_object* v_as_3714_, lean_object* v_sz_3715_, lean_object* v_i_3716_, lean_object* v_b_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
size_t v_sz_boxed_3723_; size_t v_i_boxed_3724_; lean_object* v_res_3725_; 
v_sz_boxed_3723_ = lean_unbox_usize(v_sz_3715_);
lean_dec(v_sz_3715_);
v_i_boxed_3724_ = lean_unbox_usize(v_i_3716_);
lean_dec(v_i_3716_);
v_res_3725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3713_, v_as_3714_, v_sz_boxed_3723_, v_i_boxed_3724_, v_b_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_as_3714_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3726_, lean_object* v_j_3727_){
_start:
{
lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3728_ = lean_array_get_size(v_as_3726_);
v___x_3729_ = lean_nat_dec_lt(v_j_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; 
lean_dec(v_j_3727_);
v___x_3730_ = lean_box(0);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3731_ = lean_array_fget_borrowed(v_as_3726_, v_j_3727_);
v___x_3732_ = lean_array_get_size(v___x_3731_);
v___x_3733_ = lean_unsigned_to_nat(0u);
v___x_3734_ = lean_nat_dec_eq(v___x_3732_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_nat_add(v_j_3727_, v___x_3735_);
lean_dec(v_j_3727_);
v_j_3727_ = v___x_3736_;
goto _start;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v_j_3727_);
return v___x_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3739_, lean_object* v_j_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3739_, v_j_3740_);
lean_dec_ref(v_as_3739_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3742_, lean_object* v_as_3743_, size_t v_sz_3744_, size_t v_i_3745_, lean_object* v_b_3746_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3745_, v_sz_3744_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
lean_dec_ref(v_a_3742_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_b_3746_);
return v___x_3749_;
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; size_t v___x_3753_; size_t v___x_3754_; 
v_a_3750_ = lean_array_uget_borrowed(v_as_3743_, v_i_3745_);
lean_inc(v_a_3750_);
lean_inc_ref(v_a_3742_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_a_3742_);
lean_ctor_set(v___x_3751_, 1, v_a_3750_);
v___x_3752_ = lean_array_push(v_b_3746_, v___x_3751_);
v___x_3753_ = ((size_t)1ULL);
v___x_3754_ = lean_usize_add(v_i_3745_, v___x_3753_);
v_i_3745_ = v___x_3754_;
v_b_3746_ = v___x_3752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3756_, lean_object* v_as_3757_, lean_object* v_sz_3758_, lean_object* v_i_3759_, lean_object* v_b_3760_, lean_object* v___y_3761_){
_start:
{
size_t v_sz_boxed_3762_; size_t v_i_boxed_3763_; lean_object* v_res_3764_; 
v_sz_boxed_3762_ = lean_unbox_usize(v_sz_3758_);
lean_dec(v_sz_3758_);
v_i_boxed_3763_ = lean_unbox_usize(v_i_3759_);
lean_dec(v_i_3759_);
v_res_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3756_, v_as_3757_, v_sz_boxed_3762_, v_i_boxed_3763_, v_b_3760_);
lean_dec_ref(v_as_3757_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3765_, lean_object* v_xs_3766_, lean_object* v_as_3767_, size_t v_sz_3768_, size_t v_i_3769_, lean_object* v_b_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_usize_dec_lt(v_i_3769_, v_sz_3768_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; 
lean_dec_ref(v_xs_3766_);
lean_dec_ref(v_a_3765_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v_b_3770_);
return v___x_3777_;
}
else
{
lean_object* v_snd_3778_; lean_object* v_fst_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3822_; 
v_snd_3778_ = lean_ctor_get(v_b_3770_, 1);
v_fst_3779_ = lean_ctor_get(v_b_3770_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_b_3770_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3781_ = v_b_3770_;
v_isShared_3782_ = v_isSharedCheck_3822_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_snd_3778_);
lean_inc(v_fst_3779_);
lean_dec(v_b_3770_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3822_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v_array_3783_; lean_object* v_start_3784_; lean_object* v_stop_3785_; uint8_t v___x_3786_; 
v_array_3783_ = lean_ctor_get(v_snd_3778_, 0);
v_start_3784_ = lean_ctor_get(v_snd_3778_, 1);
v_stop_3785_ = lean_ctor_get(v_snd_3778_, 2);
v___x_3786_ = lean_nat_dec_lt(v_start_3784_, v_stop_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref(v_xs_3766_);
lean_dec_ref(v_a_3765_);
if (v_isShared_3782_ == 0)
{
v___x_3788_ = v___x_3781_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_fst_3779_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_snd_3778_);
v___x_3788_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
else
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3818_; 
lean_inc(v_stop_3785_);
lean_inc(v_start_3784_);
lean_inc_ref(v_array_3783_);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_snd_3778_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3819_ = lean_ctor_get(v_snd_3778_, 2);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_snd_3778_, 1);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_snd_3778_, 0);
lean_dec(v_unused_3821_);
v___x_3792_ = v_snd_3778_;
v_isShared_3793_ = v_isSharedCheck_3818_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v_snd_3778_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3818_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3794_ = lean_array_uget_borrowed(v_as_3767_, v_i_3769_);
v___x_3795_ = lean_array_fget_borrowed(v_array_3783_, v_start_3784_);
lean_inc(v_a_3794_);
lean_inc_ref(v_xs_3766_);
lean_inc_ref(v_a_3765_);
v___x_3796_ = l_Lean_Elab_Structural_argsInGroup(v_a_3765_, v_xs_3766_, v_a_3794_, v___x_3795_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = lean_nat_add(v_start_3784_, v___x_3798_);
lean_dec(v_start_3784_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 1, v___x_3799_);
v___x_3801_ = v___x_3792_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_array_3783_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_stop_3785_);
v___x_3801_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3802_ = lean_array_push(v_fst_3779_, v_a_3797_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 1, v___x_3801_);
lean_ctor_set(v___x_3781_, 0, v___x_3802_);
v___x_3804_ = v___x_3781_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v___x_3801_);
v___x_3804_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
size_t v___x_3805_; size_t v___x_3806_; 
v___x_3805_ = ((size_t)1ULL);
v___x_3806_ = lean_usize_add(v_i_3769_, v___x_3805_);
v_i_3769_ = v___x_3806_;
v_b_3770_ = v___x_3804_;
goto _start;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_del_object(v___x_3792_);
lean_dec(v_stop_3785_);
lean_dec(v_start_3784_);
lean_dec_ref(v_array_3783_);
lean_del_object(v___x_3781_);
lean_dec(v_fst_3779_);
lean_dec_ref(v_xs_3766_);
lean_dec_ref(v_a_3765_);
v_a_3810_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3796_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3796_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3823_, lean_object* v_xs_3824_, lean_object* v_as_3825_, lean_object* v_sz_3826_, lean_object* v_i_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
size_t v_sz_boxed_3834_; size_t v_i_boxed_3835_; lean_object* v_res_3836_; 
v_sz_boxed_3834_ = lean_unbox_usize(v_sz_3826_);
lean_dec(v_sz_3826_);
v_i_boxed_3835_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_res_3836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3823_, v_xs_3824_, v_as_3825_, v_sz_boxed_3834_, v_i_boxed_3835_, v_b_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_as_3825_);
return v_res_3836_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3841_ = l_Lean_stringToMessageData(v___x_3840_);
return v___x_3841_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3844_ = l_Lean_stringToMessageData(v___x_3843_);
return v___x_3844_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3847_ = l_Lean_stringToMessageData(v___x_3846_);
return v___x_3847_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3850_ = l_Lean_stringToMessageData(v___x_3849_);
return v___x_3850_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3853_ = l_Lean_stringToMessageData(v___x_3852_);
return v___x_3853_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3856_ = l_Lean_stringToMessageData(v___x_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3857_, lean_object* v_values_3858_, lean_object* v_xs_3859_, lean_object* v_fnNames_3860_, lean_object* v_as_3861_, size_t v_sz_3862_, size_t v_i_3863_, lean_object* v_b_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_a_3871_; uint8_t v___x_3875_; 
v___x_3875_ = lean_usize_dec_lt(v_i_3863_, v_sz_3862_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_dec_ref(v_xs_3859_);
lean_dec_ref(v___x_3857_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_b_3864_);
return v___x_3876_;
}
else
{
lean_object* v___x_3877_; lean_object* v_recArgInfoss_3878_; lean_object* v_a_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; size_t v_sz_3883_; size_t v___x_3884_; lean_object* v___x_3885_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3879_ = lean_array_uget_borrowed(v_as_3861_, v_i_3863_);
v___x_3880_ = lean_array_get_size(v___x_3857_);
lean_inc_ref(v___x_3857_);
v___x_3881_ = l_Array_toSubarray___redArg(v___x_3857_, v___x_3877_, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v_recArgInfoss_3878_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v_sz_3883_ = lean_array_size(v_values_3858_);
v___x_3884_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3859_);
lean_inc(v_a_3879_);
v___x_3885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3879_, v_xs_3859_, v_values_3858_, v_sz_3883_, v___x_3884_, v___x_3882_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3946_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v_fst_3887_ = lean_ctor_get(v_b_3864_, 0);
v_snd_3888_ = lean_ctor_get(v_b_3864_, 1);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_b_3864_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3890_ = v_b_3864_;
v_isShared_3891_ = v_isSharedCheck_3946_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_snd_3888_);
lean_inc(v_fst_3887_);
lean_dec(v_b_3864_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3946_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_fst_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3944_; 
v_fst_3892_ = lean_ctor_get(v_a_3886_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_a_3886_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; 
v_unused_3945_ = lean_ctor_get(v_a_3886_, 1);
lean_dec(v_unused_3945_);
v___x_3894_ = v_a_3886_;
v_isShared_3895_ = v_isSharedCheck_3944_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_fst_3892_);
lean_dec(v_a_3886_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3944_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3892_, v___x_3877_);
if (lean_obj_tag(v___x_3896_) == 1)
{
lean_object* v_val_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
lean_dec(v_fst_3892_);
v_val_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_val_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3879_);
v___x_3900_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3879_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 7);
lean_ctor_set(v___x_3890_, 1, v___x_3900_);
lean_ctor_set(v___x_3890_, 0, v___x_3899_);
v___x_3902_ = v___x_3890_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3902_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = lean_array_get_borrowed(v___x_3898_, v_fnNames_3860_, v_val_3897_);
lean_dec(v_val_3897_);
lean_inc(v___x_3905_);
v___x_3906_ = l_Lean_MessageData_ofName(v___x_3905_);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3904_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v_fst_3887_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v_snd_3888_);
lean_ctor_set(v___x_3894_, 0, v___x_3910_);
v___x_3912_ = v___x_3894_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_snd_3888_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
v_a_3871_ = v___x_3912_;
goto v___jp_3870_;
}
}
}
else
{
lean_object* v___x_3915_; 
lean_dec(v___x_3896_);
v___x_3915_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3892_);
lean_dec(v_fst_3892_);
if (lean_obj_tag(v___x_3915_) == 1)
{
lean_object* v_val_3916_; size_t v_sz_3917_; lean_object* v___x_3918_; 
lean_del_object(v___x_3890_);
v_val_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_val_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v_sz_3917_ = lean_array_size(v_val_3916_);
lean_inc(v_a_3879_);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3879_, v_val_3916_, v_sz_3917_, v___x_3884_, v_snd_3888_);
lean_dec(v_val_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v_a_3919_);
lean_ctor_set(v___x_3894_, 0, v_fst_3887_);
v___x_3921_ = v___x_3894_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_fst_3887_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_a_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
v_a_3871_ = v___x_3921_;
goto v___jp_3870_;
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3894_);
lean_dec(v_fst_3887_);
lean_dec_ref(v_xs_3859_);
lean_dec_ref(v___x_3857_);
v_a_3923_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3918_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3918_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v___x_3915_);
v___x_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3879_);
v___x_3932_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3879_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 7);
lean_ctor_set(v___x_3890_, 1, v___x_3932_);
lean_ctor_set(v___x_3890_, 0, v___x_3931_);
v___x_3934_ = v___x_3890_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_fst_3887_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v_snd_3888_);
lean_ctor_set(v___x_3894_, 0, v___x_3939_);
v___x_3941_ = v___x_3894_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_snd_3888_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
v_a_3871_ = v___x_3941_;
goto v___jp_3870_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_b_3864_);
lean_dec_ref(v_xs_3859_);
lean_dec_ref(v___x_3857_);
v_a_3947_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3885_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3885_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
v___jp_3870_:
{
size_t v___x_3872_; size_t v___x_3873_; 
v___x_3872_ = ((size_t)1ULL);
v___x_3873_ = lean_usize_add(v_i_3863_, v___x_3872_);
v_i_3863_ = v___x_3873_;
v_b_3864_ = v_a_3871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3955_, lean_object* v_values_3956_, lean_object* v_xs_3957_, lean_object* v_fnNames_3958_, lean_object* v_as_3959_, lean_object* v_sz_3960_, lean_object* v_i_3961_, lean_object* v_b_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
size_t v_sz_boxed_3968_; size_t v_i_boxed_3969_; lean_object* v_res_3970_; 
v_sz_boxed_3968_ = lean_unbox_usize(v_sz_3960_);
lean_dec(v_sz_3960_);
v_i_boxed_3969_ = lean_unbox_usize(v_i_3961_);
lean_dec(v_i_3961_);
v_res_3970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3955_, v_values_3956_, v_xs_3957_, v_fnNames_3958_, v_as_3959_, v_sz_boxed_3968_, v_i_boxed_3969_, v_b_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec_ref(v_as_3959_);
lean_dec_ref(v_fnNames_3958_);
lean_dec_ref(v_values_3956_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3971_, lean_object* v___x_3972_, lean_object* v_values_3973_, lean_object* v_fnNames_3974_, lean_object* v_as_3975_, size_t v_sz_3976_, size_t v_i_3977_, lean_object* v_b_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_a_3985_; uint8_t v___x_3989_; 
v___x_3989_ = lean_usize_dec_lt(v_i_3977_, v_sz_3976_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_xs_3971_);
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_b_3978_);
return v___x_3990_;
}
else
{
lean_object* v___x_3991_; lean_object* v_recArgInfoss_3992_; lean_object* v_a_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; size_t v_sz_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3991_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3993_ = lean_array_uget_borrowed(v_as_3975_, v_i_3977_);
v___x_3994_ = lean_array_get_size(v___x_3972_);
lean_inc_ref(v___x_3972_);
v___x_3995_ = l_Array_toSubarray___redArg(v___x_3972_, v___x_3991_, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v_recArgInfoss_3992_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v_sz_3997_ = lean_array_size(v_values_3973_);
v___x_3998_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3971_);
lean_inc(v_a_3993_);
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3993_, v_xs_3971_, v_values_3973_, v_sz_3997_, v___x_3998_, v___x_3996_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4060_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_fst_4001_ = lean_ctor_get(v_b_3978_, 0);
v_snd_4002_ = lean_ctor_get(v_b_3978_, 1);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_b_3978_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4004_ = v_b_3978_;
v_isShared_4005_ = v_isSharedCheck_4060_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_snd_4002_);
lean_inc(v_fst_4001_);
lean_dec(v_b_3978_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4060_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_fst_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4058_; 
v_fst_4006_ = lean_ctor_get(v_a_4000_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; 
v_unused_4059_ = lean_ctor_get(v_a_4000_, 1);
lean_dec(v_unused_4059_);
v___x_4008_ = v_a_4000_;
v_isShared_4009_ = v_isSharedCheck_4058_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_fst_4006_);
lean_dec(v_a_4000_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4058_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_4006_, v___x_3991_);
if (lean_obj_tag(v___x_4010_) == 1)
{
lean_object* v_val_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4016_; 
lean_dec(v_fst_4006_);
v_val_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_val_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3993_);
v___x_4014_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3993_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 7);
lean_ctor_set(v___x_4004_, 1, v___x_4014_);
lean_ctor_set(v___x_4004_, 0, v___x_4013_);
v___x_4016_ = v___x_4004_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4016_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = lean_array_get_borrowed(v___x_4012_, v_fnNames_3974_, v_val_4011_);
lean_dec(v_val_4011_);
lean_inc(v___x_4019_);
v___x_4020_ = l_Lean_MessageData_ofName(v___x_4019_);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4018_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_4023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4021_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v_fst_4001_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v_snd_4002_);
lean_ctor_set(v___x_4008_, 0, v___x_4024_);
v___x_4026_ = v___x_4008_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_snd_4002_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
v_a_3985_ = v___x_4026_;
goto v___jp_3984_;
}
}
}
else
{
lean_object* v___x_4029_; 
lean_dec(v___x_4010_);
v___x_4029_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_4006_);
lean_dec(v_fst_4006_);
if (lean_obj_tag(v___x_4029_) == 1)
{
lean_object* v_val_4030_; size_t v_sz_4031_; lean_object* v___x_4032_; 
lean_del_object(v___x_4004_);
v_val_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v_sz_4031_ = lean_array_size(v_val_4030_);
lean_inc(v_a_3993_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3993_, v_val_4030_, v_sz_4031_, v___x_3998_, v_snd_4002_);
lean_dec(v_val_4030_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v_a_4033_);
lean_ctor_set(v___x_4008_, 0, v_fst_4001_);
v___x_4035_ = v___x_4008_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4001_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_a_4033_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
v_a_3985_ = v___x_4035_;
goto v___jp_3984_;
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_del_object(v___x_4008_);
lean_dec(v_fst_4001_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4037_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4032_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4032_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
lean_dec(v___x_4029_);
v___x_4045_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3993_);
v___x_4046_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3993_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 7);
lean_ctor_set(v___x_4004_, 1, v___x_4046_);
lean_ctor_set(v___x_4004_, 0, v___x_4045_);
v___x_4048_ = v___x_4004_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v_fst_4001_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v_snd_4002_);
lean_ctor_set(v___x_4008_, 0, v___x_4053_);
v___x_4055_ = v___x_4008_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_snd_4002_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
v_a_3985_ = v___x_4055_;
goto v___jp_3984_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_b_3978_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4061_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_3999_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_3999_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
v___jp_3984_:
{
size_t v___x_3986_; size_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = ((size_t)1ULL);
v___x_3987_ = lean_usize_add(v_i_3977_, v___x_3986_);
v___x_3988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3972_, v_values_3973_, v_xs_3971_, v_fnNames_3974_, v_as_3975_, v_sz_3976_, v___x_3987_, v_a_3985_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_4069_, lean_object* v___x_4070_, lean_object* v_values_4071_, lean_object* v_fnNames_4072_, lean_object* v_as_4073_, lean_object* v_sz_4074_, lean_object* v_i_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_sz_boxed_4082_; size_t v_i_boxed_4083_; lean_object* v_res_4084_; 
v_sz_boxed_4082_ = lean_unbox_usize(v_sz_4074_);
lean_dec(v_sz_4074_);
v_i_boxed_4083_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_4069_, v___x_4070_, v_values_4071_, v_fnNames_4072_, v_as_4073_, v_sz_boxed_4082_, v_i_boxed_4083_, v_b_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v_as_4073_);
lean_dec_ref(v_fnNames_4072_);
lean_dec_ref(v_values_4071_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
if (lean_obj_tag(v_a_4085_) == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = l_List_reverse___redArg(v_a_4086_);
return v___x_4087_;
}
else
{
lean_object* v_head_4088_; lean_object* v_tail_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4098_; 
v_head_4088_ = lean_ctor_get(v_a_4085_, 0);
v_tail_4089_ = lean_ctor_get(v_a_4085_, 1);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_a_4085_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4091_ = v_a_4085_;
v_isShared_4092_ = v_isSharedCheck_4098_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_tail_4089_);
lean_inc(v_head_4088_);
lean_dec(v_a_4085_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4098_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4093_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_4088_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 1, v_a_4086_);
lean_ctor_set(v___x_4091_, 0, v___x_4093_);
v___x_4095_ = v___x_4091_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4093_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_a_4086_);
v___x_4095_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
v_a_4085_ = v_tail_4089_;
v_a_4086_ = v___x_4095_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_4103_ = l_Lean_MessageData_ofFormat(v___x_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_4106_ = l_Lean_stringToMessageData(v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
return v___x_4111_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_box(1);
v___x_4113_ = l_Lean_MessageData_ofFormat(v___x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_4114_, lean_object* v_fixedParamPerms_4115_, lean_object* v_xs_4116_, lean_object* v_values_4117_, lean_object* v_termMeasure_x3fs_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v_recArgInfoss_4125_; lean_object* v___x_4126_; lean_object* v_perms_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v_report_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; size_t v_sz_4138_; size_t v___x_4139_; lean_object* v___x_4140_; 
v___x_4124_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_4125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_4126_ = lean_array_get_size(v_values_4117_);
v_perms_4127_ = lean_ctor_get(v_fixedParamPerms_4115_, 1);
lean_inc_ref(v_perms_4127_);
lean_dec_ref(v_fixedParamPerms_4115_);
lean_inc_ref(v_values_4117_);
v___x_4128_ = l_Array_toSubarray___redArg(v_values_4117_, v___x_4124_, v___x_4126_);
v___x_4129_ = lean_array_get_size(v_termMeasure_x3fs_4118_);
v_report_4130_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_4131_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_4118_, v___x_4124_, v___x_4129_);
v___x_4132_ = lean_array_get_size(v_perms_4127_);
v___x_4133_ = l_Array_toSubarray___redArg(v_perms_4127_, v___x_4124_, v___x_4132_);
v___x_4134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4131_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4128_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v_recArgInfoss_4125_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v_report_4130_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v_sz_4138_ = lean_array_size(v_fnNames_4114_);
v___x_4139_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4116_);
v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_4116_, v_fnNames_4114_, v_sz_4138_, v___x_4139_, v___x_4137_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v_snd_4142_; lean_object* v_options_4143_; lean_object* v_fst_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4287_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v_snd_4142_ = lean_ctor_get(v_a_4141_, 1);
lean_inc(v_snd_4142_);
v_options_4143_ = lean_ctor_get(v_a_4121_, 2);
v_fst_4144_ = lean_ctor_get(v_a_4141_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_a_4141_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; 
v_unused_4288_ = lean_ctor_get(v_a_4141_, 1);
lean_dec(v_unused_4288_);
v___x_4146_ = v_a_4141_;
v_isShared_4147_ = v_isSharedCheck_4287_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_fst_4144_);
lean_dec(v_a_4141_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4287_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_fst_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4285_; 
v_fst_4148_ = lean_ctor_get(v_snd_4142_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_snd_4142_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v_snd_4142_, 1);
lean_dec(v_unused_4286_);
v___x_4150_ = v_snd_4142_;
v_isShared_4151_ = v_isSharedCheck_4285_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_fst_4148_);
lean_dec(v_snd_4142_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4285_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v_inheritedTraceOptions_4152_; uint8_t v_hasTrace_4153_; size_t v_sz_4154_; lean_object* v___x_4155_; lean_object* v___y_4157_; lean_object* v_report_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___x_4205_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; 
v_inheritedTraceOptions_4152_ = lean_ctor_get(v_a_4121_, 13);
v_hasTrace_4153_ = lean_ctor_get_uint8(v_options_4143_, sizeof(void*)*1);
v_sz_4154_ = lean_array_size(v_fst_4148_);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4154_, v___x_4139_, v_fst_4148_);
v___x_4205_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4153_ == 0)
{
v___y_4244_ = v_a_4119_;
v___y_4245_ = v_a_4120_;
v___y_4246_ = v_a_4121_;
v___y_4247_ = v_a_4122_;
goto v___jp_4243_;
}
else
{
lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4256_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4152_, v_options_4143_, v___x_4256_);
if (v___x_4257_ == 0)
{
v___y_4244_ = v_a_4119_;
v___y_4245_ = v_a_4120_;
v___y_4246_ = v_a_4121_;
v___y_4247_ = v_a_4122_;
goto v___jp_4243_;
}
else
{
lean_object* v___x_4258_; lean_object* v___y_4260_; lean_object* v___x_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v___x_4258_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4277_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4278_ = lean_array_get_size(v___x_4155_);
v___x_4279_ = lean_nat_dec_lt(v___x_4124_, v___x_4278_);
if (v___x_4279_ == 0)
{
v___y_4260_ = v___x_4277_;
goto v___jp_4259_;
}
else
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_nat_dec_le(v___x_4278_, v___x_4278_);
if (v___x_4280_ == 0)
{
if (v___x_4279_ == 0)
{
v___y_4260_ = v___x_4277_;
goto v___jp_4259_;
}
else
{
size_t v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_usize_of_nat(v___x_4278_);
v___x_4282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4155_, v___x_4139_, v___x_4281_, v___x_4277_);
v___y_4260_ = v___x_4282_;
goto v___jp_4259_;
}
}
else
{
size_t v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_usize_of_nat(v___x_4278_);
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4155_, v___x_4139_, v___x_4283_, v___x_4277_);
v___y_4260_ = v___x_4284_;
goto v___jp_4259_;
}
}
v___jp_4259_:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4261_ = lean_array_to_list(v___y_4260_);
v___x_4262_ = lean_box(0);
v___x_4263_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4261_, v___x_4262_);
v___x_4264_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4265_ = l_Lean_MessageData_joinSep(v___x_4263_, v___x_4264_);
v___x_4266_ = l_Lean_indentD(v___x_4265_);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4258_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4205_, v___x_4267_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_dec_ref_known(v___x_4268_, 1);
v___y_4244_ = v_a_4119_;
v___y_4245_ = v_a_4120_;
v___y_4246_ = v_a_4121_;
v___y_4247_ = v_a_4122_;
goto v___jp_4243_;
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v___x_4155_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4146_);
lean_dec(v_fst_4144_);
lean_dec_ref(v_values_4117_);
lean_dec_ref(v_xs_4116_);
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
v___jp_4156_:
{
lean_object* v___x_4164_; 
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v_recArgInfoss_4125_);
lean_ctor_set(v___x_4150_, 0, v_report_4158_);
v___x_4164_ = v___x_4150_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_report_4158_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_recArgInfoss_4125_);
v___x_4164_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
size_t v_sz_4165_; lean_object* v___x_4166_; 
v_sz_4165_ = lean_array_size(v___y_4157_);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_4116_, v___x_4155_, v_values_4117_, v_fnNames_4114_, v___y_4157_, v_sz_4165_, v___x_4139_, v___x_4164_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v_values_4117_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4183_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4183_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4183_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_fst_4171_; lean_object* v_snd_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4182_; 
v_fst_4171_ = lean_ctor_get(v_a_4167_, 0);
v_snd_4172_ = lean_ctor_get(v_a_4167_, 1);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_a_4167_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4174_ = v_a_4167_;
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_snd_4172_);
lean_inc(v_fst_4171_);
lean_dec(v_a_4167_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v_fst_4171_);
lean_ctor_set(v___x_4174_, 0, v_snd_4172_);
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_snd_4172_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_fst_4171_);
v___x_4177_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4179_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4177_);
v___x_4179_ = v___x_4169_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
v_a_4184_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4166_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4166_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
v___jp_4193_:
{
lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4199_ = lean_array_get_size(v___y_4194_);
v___x_4200_ = lean_nat_dec_eq(v___x_4199_, v___x_4124_);
if (v___x_4200_ == 0)
{
lean_del_object(v___x_4146_);
v___y_4157_ = v___y_4194_;
v_report_4158_ = v_fst_4144_;
v___y_4159_ = v___y_4195_;
v___y_4160_ = v___y_4196_;
v___y_4161_ = v___y_4197_;
v___y_4162_ = v___y_4198_;
goto v___jp_4156_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4201_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 7);
lean_ctor_set(v___x_4146_, 1, v___x_4201_);
v___x_4203_ = v___x_4146_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_fst_4144_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
v___y_4157_ = v___y_4194_;
v_report_4158_ = v___x_4203_;
v___y_4159_ = v___y_4195_;
v___y_4160_ = v___y_4196_;
v___y_4161_ = v___y_4197_;
v___y_4162_ = v___y_4198_;
goto v___jp_4156_;
}
}
}
v___jp_4206_:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4211_, v___y_4209_, v___y_4210_, v___y_4207_, v___y_4208_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_options_4213_; uint8_t v_hasTrace_4214_; 
v_options_4213_ = lean_ctor_get(v___y_4207_, 2);
v_hasTrace_4214_ = lean_ctor_get_uint8(v_options_4213_, sizeof(void*)*1);
if (v_hasTrace_4214_ == 0)
{
lean_object* v_a_4215_; 
v_a_4215_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4212_, 1);
v___y_4194_ = v_a_4215_;
v___y_4195_ = v___y_4209_;
v___y_4196_ = v___y_4210_;
v___y_4197_ = v___y_4207_;
v___y_4198_ = v___y_4208_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4216_; lean_object* v_inheritedTraceOptions_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v_a_4216_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4212_, 1);
v_inheritedTraceOptions_4217_ = lean_ctor_get(v___y_4207_, 13);
v___x_4218_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4217_, v_options_4213_, v___x_4218_);
if (v___x_4219_ == 0)
{
v___y_4194_ = v_a_4216_;
v___y_4195_ = v___y_4209_;
v___y_4196_ = v___y_4210_;
v___y_4197_ = v___y_4207_;
v___y_4198_ = v___y_4208_;
goto v___jp_4193_;
}
else
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4220_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4216_);
v___x_4221_ = lean_array_to_list(v_a_4216_);
v___x_4222_ = lean_box(0);
v___x_4223_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4221_, v___x_4222_);
v___x_4224_ = l_Lean_MessageData_ofList(v___x_4223_);
v___x_4225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4220_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4205_, v___x_4225_, v___y_4209_, v___y_4210_, v___y_4207_, v___y_4208_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_dec_ref_known(v___x_4226_, 1);
v___y_4194_ = v_a_4216_;
v___y_4195_ = v___y_4209_;
v___y_4196_ = v___y_4210_;
v___y_4197_ = v___y_4207_;
v___y_4198_ = v___y_4208_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_a_4216_);
lean_dec_ref(v___x_4155_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4146_);
lean_dec(v_fst_4144_);
lean_dec_ref(v_values_4117_);
lean_dec_ref(v_xs_4116_);
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___x_4155_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4146_);
lean_dec(v_fst_4144_);
lean_dec_ref(v_values_4117_);
lean_dec_ref(v_xs_4116_);
v_a_4235_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4212_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4212_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
v___jp_4243_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4248_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4249_ = lean_array_get_size(v___x_4155_);
v___x_4250_ = lean_nat_dec_lt(v___x_4124_, v___x_4249_);
if (v___x_4250_ == 0)
{
v___y_4207_ = v___y_4246_;
v___y_4208_ = v___y_4247_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4245_;
v___y_4211_ = v___x_4248_;
goto v___jp_4206_;
}
else
{
uint8_t v___x_4251_; 
v___x_4251_ = lean_nat_dec_le(v___x_4249_, v___x_4249_);
if (v___x_4251_ == 0)
{
if (v___x_4250_ == 0)
{
v___y_4207_ = v___y_4246_;
v___y_4208_ = v___y_4247_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4245_;
v___y_4211_ = v___x_4248_;
goto v___jp_4206_;
}
else
{
size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_usize_of_nat(v___x_4249_);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4155_, v___x_4139_, v___x_4252_, v___x_4248_);
v___y_4207_ = v___y_4246_;
v___y_4208_ = v___y_4247_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4245_;
v___y_4211_ = v___x_4253_;
goto v___jp_4206_;
}
}
else
{
size_t v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = lean_usize_of_nat(v___x_4249_);
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4155_, v___x_4139_, v___x_4254_, v___x_4248_);
v___y_4207_ = v___y_4246_;
v___y_4208_ = v___y_4247_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4245_;
v___y_4211_ = v___x_4255_;
goto v___jp_4206_;
}
}
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v_values_4117_);
lean_dec_ref(v_xs_4116_);
v_a_4289_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4140_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4140_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4297_, lean_object* v_fixedParamPerms_4298_, lean_object* v_xs_4299_, lean_object* v_values_4300_, lean_object* v_termMeasure_x3fs_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4297_, v_fixedParamPerms_4298_, v_xs_4299_, v_values_4300_, v_termMeasure_x3fs_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec_ref(v_fnNames_4297_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4308_, lean_object* v_as_4309_, size_t v_sz_4310_, size_t v_i_4311_, lean_object* v_b_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4308_, v_as_4309_, v_sz_4310_, v_i_4311_, v_b_4312_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4319_, lean_object* v_as_4320_, lean_object* v_sz_4321_, lean_object* v_i_4322_, lean_object* v_b_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
size_t v_sz_boxed_4329_; size_t v_i_boxed_4330_; lean_object* v_res_4331_; 
v_sz_boxed_4329_ = lean_unbox_usize(v_sz_4321_);
lean_dec(v_sz_4321_);
v_i_boxed_4330_ = lean_unbox_usize(v_i_4322_);
lean_dec(v_i_4322_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4319_, v_as_4320_, v_sz_boxed_4329_, v_i_boxed_4330_, v_b_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v_as_4320_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4332_, uint8_t v_skipRealize_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; lean_object* v_env_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4336_ = lean_st_ref_get(v___y_4334_);
v_env_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc_ref(v_env_4337_);
lean_dec(v___x_4336_);
v___x_4338_ = l_Lean_Environment_contains(v_env_4337_, v_constName_4332_, v_skipRealize_4333_);
v___x_4339_ = lean_box(v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4341_, lean_object* v_skipRealize_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
uint8_t v_skipRealize_boxed_4345_; lean_object* v_res_4346_; 
v_skipRealize_boxed_4345_ = lean_unbox(v_skipRealize_4342_);
v_res_4346_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4341_, v_skipRealize_boxed_4345_, v___y_4343_);
lean_dec(v___y_4343_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4347_, uint8_t v_skipRealize_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4347_, v_skipRealize_4348_, v___y_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4355_, lean_object* v_skipRealize_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v_skipRealize_boxed_4362_; lean_object* v_res_4363_; 
v_skipRealize_boxed_4362_ = lean_unbox(v_skipRealize_4356_);
v_res_4363_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4355_, v_skipRealize_boxed_4362_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_Meta_saveState___redArg(v___y_4366_, v___y_4368_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4372_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4370_, 1);
lean_inc(v___y_4368_);
lean_inc_ref(v___y_4367_);
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
v___x_4372_ = lean_apply_5(v_x_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, lean_box(0));
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_dec(v_a_4371_);
return v___x_4372_;
}
else
{
lean_object* v_a_4373_; uint8_t v___y_4375_; uint8_t v___x_4393_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
v___x_4393_ = l_Lean_Exception_isInterrupt(v_a_4373_);
if (v___x_4393_ == 0)
{
uint8_t v___x_4394_; 
lean_inc(v_a_4373_);
v___x_4394_ = l_Lean_Exception_isRuntime(v_a_4373_);
v___y_4375_ = v___x_4394_;
goto v___jp_4374_;
}
else
{
v___y_4375_ = v___x_4393_;
goto v___jp_4374_;
}
v___jp_4374_:
{
if (v___y_4375_ == 0)
{
lean_object* v___x_4376_; 
lean_dec_ref_known(v___x_4372_, 1);
v___x_4376_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4371_, v___y_4366_, v___y_4368_);
lean_dec(v_a_4371_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4376_, 0);
lean_dec(v_unused_4384_);
v___x_4378_ = v___x_4376_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v___x_4376_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 1);
lean_ctor_set(v___x_4378_, 0, v_a_4373_);
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4373_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_a_4373_);
v_a_4385_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4376_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4376_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_dec(v_a_4373_);
lean_dec(v_a_4371_);
return v___x_4372_;
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec_ref(v_x_4364_);
v_a_4395_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4370_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4370_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4410_, lean_object* v_x_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4418_, lean_object* v_x_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4418_, v_x_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
return v_res_4425_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4428_ = l_Lean_stringToMessageData(v___x_4427_);
return v___x_4428_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4431_ = l_Lean_stringToMessageData(v___x_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4432_, uint8_t v___x_4433_, lean_object* v_group_4434_, lean_object* v_k_4435_, lean_object* v_comb_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4432_, v___x_4433_, v___y_4440_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; uint8_t v___x_4444_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = lean_unbox(v_a_4443_);
lean_dec(v_a_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4446_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4434_);
v___x_4447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4445_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
v___x_4448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4447_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4449_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v___x_4451_; 
lean_dec_ref_known(v___x_4450_, 1);
v___x_4451_ = lean_apply_6(v_k_4435_, v_comb_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, lean_box(0));
return v___x_4451_;
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_comb_4436_);
lean_dec_ref(v_k_4435_);
v_a_4452_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4450_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4450_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v___x_4460_; 
lean_dec_ref(v_group_4434_);
v___x_4460_ = lean_apply_6(v_k_4435_, v_comb_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, lean_box(0));
return v___x_4460_;
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_comb_4436_);
lean_dec_ref(v_k_4435_);
lean_dec_ref(v_group_4434_);
v_a_4461_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4442_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4442_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4469_, lean_object* v___x_4470_, lean_object* v_group_4471_, lean_object* v_k_4472_, lean_object* v_comb_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
uint8_t v___x_4418__boxed_4479_; lean_object* v_res_4480_; 
v___x_4418__boxed_4479_ = lean_unbox(v___x_4470_);
v_res_4480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4469_, v___x_4418__boxed_4479_, v_group_4471_, v_k_4472_, v_comb_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v_res_4480_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4483_ = l_Lean_stringToMessageData(v___x_4482_);
return v___x_4483_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4485_ = l_Lean_stringToMessageData(v___x_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4486_, lean_object* v_fnNames_4487_, lean_object* v_xs_4488_, lean_object* v_values_4489_, lean_object* v_as_4490_, size_t v_sz_4491_, size_t v_i_4492_, lean_object* v_b_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
uint8_t v___x_4499_; 
v___x_4499_ = lean_usize_dec_lt(v_i_4492_, v_sz_4491_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; 
lean_dec_ref(v_values_4489_);
lean_dec_ref(v_xs_4488_);
lean_dec_ref(v_k_4486_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v_b_4493_);
return v___x_4500_;
}
else
{
lean_object* v_snd_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4571_; 
v_snd_4501_ = lean_ctor_get(v_b_4493_, 1);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_b_4493_);
if (v_isSharedCheck_4571_ == 0)
{
lean_object* v_unused_4572_; 
v_unused_4572_ = lean_ctor_get(v_b_4493_, 0);
lean_dec(v_unused_4572_);
v___x_4503_ = v_b_4493_;
v_isShared_4504_ = v_isSharedCheck_4571_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_snd_4501_);
lean_dec(v_b_4493_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4571_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v_a_4505_; lean_object* v_group_4506_; lean_object* v_comb_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4570_; 
v_a_4505_ = lean_array_uget(v_as_4490_, v_i_4492_);
v_group_4506_ = lean_ctor_get(v_a_4505_, 0);
v_comb_4507_ = lean_ctor_get(v_a_4505_, 1);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_a_4505_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4509_ = v_a_4505_;
v_isShared_4510_ = v_isSharedCheck_4570_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_comb_4507_);
lean_inc(v_group_4506_);
lean_dec(v_a_4505_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4570_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v_toIndGroupInfo_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___f_4515_; lean_object* v___x_4516_; 
v_toIndGroupInfo_4511_ = lean_ctor_get(v_group_4506_, 0);
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4511_, v___x_4512_);
v___x_4514_ = lean_box(v___x_4499_);
lean_inc_ref(v_comb_4507_);
lean_inc_ref(v_k_4486_);
v___f_4515_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4515_, 0, v___x_4513_);
lean_closure_set(v___f_4515_, 1, v___x_4514_);
lean_closure_set(v___f_4515_, 2, v_group_4506_);
lean_closure_set(v___f_4515_, 3, v_k_4486_);
lean_closure_set(v___f_4515_, 4, v_comb_4507_);
v___x_4516_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4515_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4528_; 
lean_del_object(v___x_4509_);
lean_dec_ref(v_comb_4507_);
lean_dec_ref(v_values_4489_);
lean_dec_ref(v_xs_4488_);
lean_dec_ref(v_k_4486_);
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4519_ = v___x_4516_;
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4516_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4521_, 0, v_a_4517_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4521_);
v___x_4523_ = v___x_4503_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_snd_4501_);
v___x_4523_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v___x_4523_);
v___x_4525_ = v___x_4519_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4569_; 
v_a_4529_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4531_ = v___x_4516_;
v_isShared_4532_ = v_isSharedCheck_4569_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4516_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4569_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; uint8_t v___y_4535_; uint8_t v___x_4567_; 
v___x_4533_ = lean_box(0);
v___x_4567_ = l_Lean_Exception_isInterrupt(v_a_4529_);
if (v___x_4567_ == 0)
{
uint8_t v___x_4568_; 
lean_inc(v_a_4529_);
v___x_4568_ = l_Lean_Exception_isRuntime(v_a_4529_);
v___y_4535_ = v___x_4568_;
goto v___jp_4534_;
}
else
{
v___y_4535_ = v___x_4567_;
goto v___jp_4534_;
}
v___jp_4534_:
{
if (v___y_4535_ == 0)
{
lean_object* v___x_4536_; 
lean_del_object(v___x_4531_);
lean_inc_ref(v_values_4489_);
lean_inc_ref(v_xs_4488_);
v___x_4536_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4487_, v_xs_4488_, v_values_4489_, v_comb_4507_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v___x_4540_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4510_ == 0)
{
lean_ctor_set_tag(v___x_4509_, 7);
lean_ctor_set(v___x_4509_, 1, v_a_4537_);
lean_ctor_set(v___x_4509_, 0, v___x_4538_);
v___x_4540_ = v___x_4509_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_a_4537_);
v___x_4540_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4541_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_Exception_toMessageData(v_a_4529_);
v___x_4544_ = l_Lean_indentD(v___x_4543_);
v___x_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4542_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4545_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v_snd_4501_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 1, v___x_4548_);
lean_ctor_set(v___x_4503_, 0, v___x_4533_);
v___x_4550_ = v___x_4503_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
size_t v___x_4551_; size_t v___x_4552_; 
v___x_4551_ = ((size_t)1ULL);
v___x_4552_ = lean_usize_add(v_i_4492_, v___x_4551_);
v_i_4492_ = v___x_4552_;
v_b_4493_ = v___x_4550_;
goto _start;
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v_a_4529_);
lean_del_object(v___x_4509_);
lean_del_object(v___x_4503_);
lean_dec(v_snd_4501_);
lean_dec_ref(v_values_4489_);
lean_dec_ref(v_xs_4488_);
lean_dec_ref(v_k_4486_);
v_a_4556_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4536_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4536_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v___x_4565_; 
lean_del_object(v___x_4509_);
lean_dec_ref(v_comb_4507_);
lean_del_object(v___x_4503_);
lean_dec(v_snd_4501_);
lean_dec_ref(v_values_4489_);
lean_dec_ref(v_xs_4488_);
lean_dec_ref(v_k_4486_);
if (v_isShared_4532_ == 0)
{
v___x_4565_ = v___x_4531_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4529_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4573_, lean_object* v_fnNames_4574_, lean_object* v_xs_4575_, lean_object* v_values_4576_, lean_object* v_as_4577_, lean_object* v_sz_4578_, lean_object* v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4578_);
lean_dec(v_sz_4578_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4579_);
lean_dec(v_i_4579_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4573_, v_fnNames_4574_, v_xs_4575_, v_values_4576_, v_as_4577_, v_sz_boxed_4586_, v_i_boxed_4587_, v_b_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec_ref(v_as_4577_);
lean_dec_ref(v_fnNames_4574_);
return v_res_4588_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4590_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4591_ = l_Lean_stringToMessageData(v___x_4590_);
return v___x_4591_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4594_ = l_Lean_stringToMessageData(v___x_4593_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4595_, lean_object* v_xs_4596_, lean_object* v_values_4597_, lean_object* v_candidates_4598_, lean_object* v_k_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v_candidates_4605_; lean_object* v_report_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4665_; 
v_candidates_4605_ = lean_ctor_get(v_candidates_4598_, 0);
v_report_4606_ = lean_ctor_get(v_candidates_4598_, 1);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_candidates_4598_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4608_ = v_candidates_4598_;
v_isShared_4609_ = v_isSharedCheck_4665_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_report_4606_);
lean_inc(v_candidates_4605_);
lean_dec(v_candidates_4598_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4665_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = lean_box(0);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4610_);
v___x_4612_ = v___x_4608_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v_report_4606_);
v___x_4612_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
size_t v_sz_4613_; size_t v___x_4614_; lean_object* v___x_4615_; 
v_sz_4613_ = lean_array_size(v_candidates_4605_);
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4599_, v_fnNames_4595_, v_xs_4596_, v_values_4597_, v_candidates_4605_, v_sz_4613_, v___x_4614_, v___x_4612_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec_ref(v_candidates_4605_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4655_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4655_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4655_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v_fst_4620_; 
v_fst_4620_ = lean_ctor_get(v_a_4616_, 0);
if (lean_obj_tag(v_fst_4620_) == 0)
{
lean_object* v_options_4621_; lean_object* v_snd_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4649_; 
lean_del_object(v___x_4618_);
v_options_4621_ = lean_ctor_get(v_a_4602_, 2);
v_snd_4622_ = lean_ctor_get(v_a_4616_, 1);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_a_4616_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v_a_4616_, 0);
lean_dec(v_unused_4650_);
v___x_4624_ = v_a_4616_;
v_isShared_4625_ = v_isSharedCheck_4649_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_snd_4622_);
lean_dec(v_a_4616_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4649_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v_inheritedTraceOptions_4626_; uint8_t v_hasTrace_4627_; lean_object* v___x_4628_; lean_object* v___x_4630_; 
v_inheritedTraceOptions_4626_ = lean_ctor_get(v_a_4602_, 13);
v_hasTrace_4627_ = lean_ctor_get_uint8(v_options_4621_, sizeof(void*)*1);
v___x_4628_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4625_ == 0)
{
lean_ctor_set_tag(v___x_4624_, 7);
lean_ctor_set(v___x_4624_, 0, v___x_4628_);
v___x_4630_ = v___x_4624_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_snd_4622_);
v___x_4630_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
if (v_hasTrace_4627_ == 0)
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4630_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4632_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4633_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4626_, v_options_4621_, v___x_4633_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4630_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4635_;
}
else
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4630_);
v___x_4637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
lean_ctor_set(v___x_4637_, 1, v___x_4630_);
v___x_4638_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4632_, v___x_4637_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v___x_4639_; 
lean_dec_ref_known(v___x_4638_, 1);
v___x_4639_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4630_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4639_;
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___x_4630_);
v_a_4640_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4638_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4638_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_val_4651_; lean_object* v___x_4653_; 
lean_inc_ref(v_fst_4620_);
lean_dec(v_a_4616_);
v_val_4651_ = lean_ctor_get(v_fst_4620_, 0);
lean_inc(v_val_4651_);
lean_dec_ref_known(v_fst_4620_, 1);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v_val_4651_);
v___x_4653_ = v___x_4618_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_val_4651_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
v_a_4656_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4615_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4615_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4666_, lean_object* v_xs_4667_, lean_object* v_values_4668_, lean_object* v_candidates_4669_, lean_object* v_k_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4666_, v_xs_4667_, v_values_4668_, v_candidates_4669_, v_k_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec_ref(v_fnNames_4666_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4677_, lean_object* v_fnNames_4678_, lean_object* v_xs_4679_, lean_object* v_values_4680_, lean_object* v_candidates_4681_, lean_object* v_k_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4678_, v_xs_4679_, v_values_4680_, v_candidates_4681_, v_k_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4689_, lean_object* v_fnNames_4690_, lean_object* v_xs_4691_, lean_object* v_values_4692_, lean_object* v_candidates_4693_, lean_object* v_k_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4689_, v_fnNames_4690_, v_xs_4691_, v_values_4692_, v_candidates_4693_, v_k_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec_ref(v_fnNames_4690_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4701_, lean_object* v_k_4702_, lean_object* v_fnNames_4703_, lean_object* v_xs_4704_, lean_object* v_values_4705_, lean_object* v_as_4706_, size_t v_sz_4707_, size_t v_i_4708_, lean_object* v_b_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4702_, v_fnNames_4703_, v_xs_4704_, v_values_4705_, v_as_4706_, v_sz_4707_, v_i_4708_, v_b_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4716_, lean_object* v_k_4717_, lean_object* v_fnNames_4718_, lean_object* v_xs_4719_, lean_object* v_values_4720_, lean_object* v_as_4721_, lean_object* v_sz_4722_, lean_object* v_i_4723_, lean_object* v_b_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
size_t v_sz_boxed_4730_; size_t v_i_boxed_4731_; lean_object* v_res_4732_; 
v_sz_boxed_4730_ = lean_unbox_usize(v_sz_4722_);
lean_dec(v_sz_4722_);
v_i_boxed_4731_ = lean_unbox_usize(v_i_4723_);
lean_dec(v_i_4723_);
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4716_, v_k_4717_, v_fnNames_4718_, v_xs_4719_, v_values_4720_, v_as_4721_, v_sz_boxed_4730_, v_i_boxed_4731_, v_b_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec_ref(v_as_4721_);
lean_dec_ref(v_fnNames_4718_);
return v_res_4732_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_maxCombinationSize = _init_l_Lean_Elab_Structural_maxCombinationSize();
lean_mark_persistent(l_Lean_Elab_Structural_maxCombinationSize);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
}
#ifdef __cplusplus
}
#endif
