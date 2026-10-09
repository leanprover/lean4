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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Elab.PreDefinition.Structural.FindRecArg"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Elab.Structural.getRecArgInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__1;
static const lean_ctor_object l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value),((lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value)}};
static const lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "no parameters suitable for structural recursion"};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Structural_findRecArgCandidates___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value)}};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__3;
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inductive groups: "};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__5;
static const lean_array_object l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value;
static const lean_string_object l_Lean_Elab_Structural_findRecArgCandidates___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "recArgInfos:"};
static const lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_findRecArgCandidates___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__8;
static lean_once_cell_t l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_findRecArgCandidates___closed__9;
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParam___closed__1(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParam___closed__0));
v___x_28_ = l_Lean_stringToMessageData(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam(lean_object* v_xs_29_, lean_object* v_i_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_36_; lean_object* v_x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = l_Lean_instInhabitedExpr;
v_x_37_ = lean_array_get_borrowed(v___x_36_, v_xs_29_, v_i_30_);
v___x_38_ = l_Lean_Expr_fvarId_x21(v_x_37_);
v___x_39_ = l_Lean_FVarId_getUserName___redArg(v___x_38_, v_a_31_, v_a_33_, v_a_34_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; uint8_t v___x_41_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v___x_39_, 1);
v___x_41_ = l_Lean_Name_hasMacroScopes(v_a_40_);
lean_dec(v_a_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_inc(v_x_37_);
v___x_42_ = l_Lean_MessageData_ofExpr(v_x_37_);
v___x_43_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_42_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_44_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParam___closed__1, &l_Lean_Elab_Structural_prettyParam___closed__1_once, _init_l_Lean_Elab_Structural_prettyParam___closed__1);
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_add(v_i_30_, v___x_45_);
v___x_47_ = l_Nat_reprFast(v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
v___x_50_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_44_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_50_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
return v___x_51_;
}
}
else
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_52_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_39_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_39_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam___boxed(lean_object* v_xs_60_, lean_object* v_i_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_Structural_prettyParam(v_xs_60_, v_i_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_i_61_);
lean_dec_ref(v_xs_60_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object* v_k_68_, lean_object* v_b_69_, lean_object* v_c_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
v___x_76_ = lean_apply_7(v_k_68_, v_b_69_, v_c_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object* v_k_77_, lean_object* v_b_78_, lean_object* v_c_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_77_, v_b_78_, v_c_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(lean_object* v_e_86_, lean_object* v_k_87_, uint8_t v_cleanupAnnotations_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___f_94_; uint8_t v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___f_94_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_94_, 0, v_k_87_);
v___x_95_ = 1;
v___x_96_ = 0;
v___x_97_ = lean_box(0);
v___x_98_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_86_, v___x_95_, v___x_96_, v___x_95_, v___x_96_, v___x_97_, v___f_94_, v_cleanupAnnotations_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_98_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_98_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(lean_object* v_e_115_, lean_object* v_k_116_, lean_object* v_cleanupAnnotations_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_123_; lean_object* v_res_124_; 
v_cleanupAnnotations_boxed_123_ = lean_unbox(v_cleanupAnnotations_117_);
v_res_124_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_115_, v_k_116_, v_cleanupAnnotations_boxed_123_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_object* v_00_u03b1_125_, lean_object* v_e_126_, lean_object* v_k_127_, uint8_t v_cleanupAnnotations_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_126_, v_k_127_, v_cleanupAnnotations_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(lean_object* v_00_u03b1_135_, lean_object* v_e_136_, lean_object* v_k_137_, lean_object* v_cleanupAnnotations_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_144_; lean_object* v_res_145_; 
v_cleanupAnnotations_boxed_144_ = lean_unbox(v_cleanupAnnotations_138_);
v_res_145_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(v_00_u03b1_135_, v_e_136_, v_k_137_, v_cleanupAnnotations_boxed_144_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0(lean_object* v_recArgInfo_146_, lean_object* v_xs_147_, lean_object* v_ys_148_, lean_object* v_x_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_fixedParamPerm_155_; lean_object* v_recArgPos_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_fixedParamPerm_155_ = lean_ctor_get(v_recArgInfo_146_, 1);
lean_inc_ref(v_fixedParamPerm_155_);
v_recArgPos_156_ = lean_ctor_get(v_recArgInfo_146_, 2);
lean_inc(v_recArgPos_156_);
lean_dec_ref(v_recArgInfo_146_);
v___x_157_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_155_, v_xs_147_, v_ys_148_);
v___x_158_ = l_Lean_Elab_Structural_prettyParam(v___x_157_, v_recArgPos_156_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v_recArgPos_156_);
lean_dec_ref(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object* v_recArgInfo_159_, lean_object* v_xs_160_, lean_object* v_ys_161_, lean_object* v_x_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_159_, v_xs_160_, v_ys_161_, v_x_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec_ref(v_x_162_);
lean_dec_ref(v_xs_160_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object* v_xs_169_, lean_object* v_value_170_, lean_object* v_recArgInfo_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___f_177_; uint8_t v___x_178_; lean_object* v___x_179_; 
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_177_, 0, v_recArgInfo_171_);
lean_closure_set(v___f_177_, 1, v_xs_169_);
v___x_178_ = 0;
v___x_179_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_170_, v___f_177_, v___x_178_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object* v_xs_180_, lean_object* v_value_181_, lean_object* v_recArgInfo_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_180_, v_value_181_, v_recArgInfo_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_188_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0));
v___x_191_ = l_Lean_stringToMessageData(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object* v_xs_192_, lean_object* v_as_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_b_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_lt(v_i_195_, v_sz_194_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v_xs_192_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_b_196_);
return v___x_203_;
}
else
{
lean_object* v_snd_204_; lean_object* v_snd_205_; lean_object* v_fst_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_288_; 
v_snd_204_ = lean_ctor_get(v_b_196_, 1);
lean_inc(v_snd_204_);
v_snd_205_ = lean_ctor_get(v_snd_204_, 1);
lean_inc(v_snd_205_);
v_fst_206_ = lean_ctor_get(v_b_196_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_b_196_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v_b_196_, 1);
lean_dec(v_unused_289_);
v___x_208_ = v_b_196_;
v_isShared_209_ = v_isSharedCheck_288_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_fst_206_);
lean_dec(v_b_196_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_288_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_fst_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_286_; 
v_fst_210_ = lean_ctor_get(v_snd_204_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_snd_204_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_snd_204_, 1);
lean_dec(v_unused_287_);
v___x_212_ = v_snd_204_;
v_isShared_213_ = v_isSharedCheck_286_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_fst_210_);
lean_dec(v_snd_204_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_286_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_array_214_; lean_object* v_start_215_; lean_object* v_stop_216_; uint8_t v___x_217_; 
v_array_214_ = lean_ctor_get(v_snd_205_, 0);
v_start_215_ = lean_ctor_get(v_snd_205_, 1);
v_stop_216_ = lean_ctor_get(v_snd_205_, 2);
v___x_217_ = lean_nat_dec_lt(v_start_215_, v_stop_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_219_; 
lean_dec_ref(v_xs_192_);
if (v_isShared_213_ == 0)
{
v___x_219_ = v___x_212_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_fst_210_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_snd_205_);
v___x_219_ = v_reuseFailAlloc_224_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_219_);
v___x_221_ = v___x_208_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_223_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
else
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_282_; 
lean_inc(v_stop_216_);
lean_inc(v_start_215_);
lean_inc_ref(v_array_214_);
v_isSharedCheck_282_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_283_ = lean_ctor_get(v_snd_205_, 2);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_snd_205_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_snd_205_, 0);
lean_dec(v_unused_285_);
v___x_226_ = v_snd_205_;
v_isShared_227_ = v_isSharedCheck_282_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_snd_205_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_282_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_array_228_; lean_object* v_start_229_; lean_object* v_stop_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v_array_228_ = lean_ctor_get(v_fst_210_, 0);
v_start_229_ = lean_ctor_get(v_fst_210_, 1);
v_stop_230_ = lean_ctor_get(v_fst_210_, 2);
v___x_231_ = lean_array_fget(v_array_214_, v_start_215_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_start_215_, v___x_232_);
lean_dec(v_start_215_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_233_);
v___x_235_ = v___x_226_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_array_214_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_stop_216_);
v___x_235_ = v_reuseFailAlloc_281_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_lt(v_start_229_, v_stop_230_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v___x_231_);
lean_dec_ref(v_xs_192_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_235_);
v___x_238_ = v___x_212_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_fst_210_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_235_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_238_);
v___x_240_ = v___x_208_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
else
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_277_; 
lean_inc(v_stop_230_);
lean_inc(v_start_229_);
lean_inc_ref(v_array_228_);
v_isSharedCheck_277_ = !lean_is_exclusive(v_fst_210_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_278_ = lean_ctor_get(v_fst_210_, 2);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_fst_210_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_fst_210_, 0);
lean_dec(v_unused_280_);
v___x_245_ = v_fst_210_;
v_isShared_246_ = v_isSharedCheck_277_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_fst_210_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_277_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_247_ = lean_array_uget_borrowed(v_as_193_, v_i_195_);
v___x_248_ = lean_array_fget(v_array_228_, v_start_229_);
v___x_249_ = lean_nat_add(v_start_229_, v___x_232_);
lean_dec(v_start_229_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_array_228_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_stop_230_);
v___x_251_ = v_reuseFailAlloc_276_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
lean_inc_ref(v_xs_192_);
v___x_252_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_192_, v___x_248_, v___x_231_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v___x_254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v_a_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_inc(v_a_247_);
v___x_256_ = l_Lean_MessageData_ofName(v_a_247_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_array_push(v_fst_206_, v___x_257_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_235_);
lean_ctor_set(v___x_212_, 0, v___x_251_);
v___x_260_ = v___x_212_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_235_);
v___x_260_ = v_reuseFailAlloc_267_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_260_);
lean_ctor_set(v___x_208_, 0, v___x_258_);
v___x_262_ = v___x_208_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_195_, v___x_263_);
v_i_195_ = v___x_264_;
v_b_196_ = v___x_262_;
goto _start;
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v___x_251_);
lean_dec_ref(v___x_235_);
lean_del_object(v___x_212_);
lean_del_object(v___x_208_);
lean_dec(v_fst_206_);
lean_dec_ref(v_xs_192_);
v_a_268_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_252_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_252_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object* v_xs_290_, lean_object* v_as_291_, lean_object* v_sz_292_, lean_object* v_i_293_, lean_object* v_b_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
size_t v_sz_boxed_300_; size_t v_i_boxed_301_; lean_object* v_res_302_; 
v_sz_boxed_300_ = lean_unbox_usize(v_sz_292_);
lean_dec(v_sz_292_);
v_i_boxed_301_ = lean_unbox_usize(v_i_293_);
lean_dec(v_i_293_);
v_res_302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_290_, v_as_291_, v_sz_boxed_300_, v_i_boxed_301_, v_b_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec_ref(v_as_291_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__1));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__3));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object* v_fnNames_311_, lean_object* v_xs_312_, lean_object* v_values_313_, lean_object* v_recArgInfos_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_array_get_size(v_fnNames_311_);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_dec_eq(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v_l_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; size_t v_sz_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v_l_324_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_325_ = lean_array_get_size(v_values_313_);
v___x_326_ = l_Array_toSubarray___redArg(v_values_313_, v___x_323_, v___x_325_);
v___x_327_ = lean_array_get_size(v_recArgInfos_314_);
v___x_328_ = l_Array_toSubarray___redArg(v_recArgInfos_314_, v___x_323_, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_326_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_l_324_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v_sz_331_ = lean_array_size(v_fnNames_311_);
v___x_332_ = ((size_t)0ULL);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_312_, v_fnNames_311_, v_sz_331_, v___x_332_, v___x_330_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_353_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_353_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_fst_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_351_; 
v_fst_338_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_a_334_, 1);
lean_dec(v_unused_352_);
v___x_340_ = v_a_334_;
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_fst_338_);
lean_dec(v_a_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_342_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__2, &l_Lean_Elab_Structural_prettyParameterSet___closed__2_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2);
v___x_343_ = lean_array_to_list(v_fst_338_);
v___x_344_ = l_Lean_MessageData_andList(v___x_343_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 7);
lean_ctor_set(v___x_340_, 1, v___x_344_);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_346_);
v___x_348_ = v___x_336_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_333_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_333_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_362_ = l_Lean_instInhabitedExpr;
v___x_363_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_array_get(v___x_362_, v_values_313_, v___x_364_);
lean_dec_ref(v_values_313_);
v___x_366_ = lean_array_get(v___x_363_, v_recArgInfos_314_, v___x_364_);
lean_dec_ref(v_recArgInfos_314_);
v___x_367_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_312_, v___x_365_, v___x_366_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__4, &l_Lean_Elab_Structural_prettyParameterSet___closed__4_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_373_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object* v_fnNames_378_, lean_object* v_xs_379_, lean_object* v_values_380_, lean_object* v_recArgInfos_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_378_, v_xs_379_, v_values_380_, v_recArgInfos_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_fnNames_378_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object* v_xs_388_, lean_object* v_v_389_, lean_object* v_i_390_){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_array_get_size(v_xs_388_);
v___x_392_ = lean_nat_dec_lt(v_i_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v_i_390_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_fget_borrowed(v_xs_388_, v_i_390_);
v___x_395_ = lean_expr_eqv(v___x_394_, v_v_389_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_i_390_, v___x_396_);
lean_dec(v_i_390_);
v_i_390_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_i_390_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_400_, lean_object* v_v_401_, lean_object* v_i_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_400_, v_v_401_, v_i_402_);
lean_dec_ref(v_v_401_);
lean_dec_ref(v_xs_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object* v_xs_404_, lean_object* v_v_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_404_, v_v_405_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object* v_xs_408_, lean_object* v_v_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_408_, v_v_409_);
lean_dec_ref(v_v_409_);
lean_dec_ref(v_xs_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object* v_xs_411_, lean_object* v_v_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_411_, v_v_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_val_415_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_413_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v___x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object* v_xs_423_, lean_object* v_v_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_423_, v_v_424_);
lean_dec_ref(v_v_424_);
lean_dec_ref(v_xs_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object* v_xs_426_, lean_object* v_as_427_, size_t v_sz_428_, size_t v_i_429_, lean_object* v_b_430_){
_start:
{
lean_object* v_a_432_; uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_436_ == 0)
{
return v_b_430_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_438_; 
v_a_437_ = lean_array_uget_borrowed(v_as_427_, v_i_429_);
v___x_438_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_426_, v_a_437_);
if (lean_obj_tag(v___x_438_) == 1)
{
lean_object* v_val_439_; uint8_t v___x_440_; 
v_val_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = lean_nat_dec_lt(v_val_439_, v_b_430_);
if (v___x_440_ == 0)
{
lean_dec(v_val_439_);
v_a_432_ = v_b_430_;
goto v___jp_431_;
}
else
{
lean_dec(v_b_430_);
v_a_432_ = v_val_439_;
goto v___jp_431_;
}
}
else
{
lean_dec(v___x_438_);
v_a_432_ = v_b_430_;
goto v___jp_431_;
}
}
v___jp_431_:
{
size_t v___x_433_; size_t v___x_434_; 
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_429_, v___x_433_);
v_i_429_ = v___x_434_;
v_b_430_ = v_a_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object* v_xs_441_, lean_object* v_as_442_, lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_b_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_441_, v_as_442_, v_sz_boxed_446_, v_i_boxed_447_, v_b_445_);
lean_dec_ref(v_as_442_);
lean_dec_ref(v_xs_441_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object* v_xs_449_, lean_object* v_indices_450_){
_start:
{
lean_object* v_minPos_451_; size_t v_sz_452_; size_t v___x_453_; lean_object* v___x_454_; 
v_minPos_451_ = lean_array_get_size(v_xs_449_);
v_sz_452_ = lean_array_size(v_indices_450_);
v___x_453_ = ((size_t)0ULL);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_449_, v_indices_450_, v_sz_452_, v___x_453_, v_minPos_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* v_xs_455_, lean_object* v_indices_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_455_, v_indices_456_);
lean_dec_ref(v_indices_456_);
lean_dec_ref(v_xs_455_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object* v_x_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_460_);
lean_dec(v_x_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object* v_fvarId_463_, lean_object* v_x_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_instBEqFVarId_beq(v_fvarId_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_fvarId_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = lean_unsigned_to_nat(16u);
v___x_473_ = lean_mk_array(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_477_, lean_object* v_fvarId_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___x_483_; uint8_t v_fst_485_; lean_object* v_mctx_486_; lean_object* v___y_504_; lean_object* v_mctx_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___f_481_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_482_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_482_, 0, v_fvarId_478_);
v___x_483_ = lean_st_ref_get(v___y_479_);
v_mctx_509_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref_n(v_mctx_509_, 2);
lean_dec(v___x_483_);
v___x_510_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_mctx_509_);
v___x_512_ = l_Lean_Expr_hasFVar(v_e_477_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Expr_hasMVar(v_e_477_);
if (v___x_513_ == 0)
{
lean_dec_ref_known(v___x_511_, 2);
lean_dec_ref(v___f_482_);
lean_dec_ref(v_e_477_);
v_fst_485_ = v___x_513_;
v_mctx_486_ = v_mctx_509_;
goto v___jp_484_;
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_mctx_509_);
v___x_514_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_482_, v___f_481_, v_e_477_, v___x_511_);
v___y_504_ = v___x_514_;
goto v___jp_503_;
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v_mctx_509_);
v___x_515_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_482_, v___f_481_, v_e_477_, v___x_511_);
v___y_504_ = v___x_515_;
goto v___jp_503_;
}
v___jp_484_:
{
lean_object* v___x_487_; lean_object* v_cache_488_; lean_object* v_zetaDeltaFVarIds_489_; lean_object* v_postponed_490_; lean_object* v_diag_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_501_; 
v___x_487_ = lean_st_ref_take(v___y_479_);
v_cache_488_ = lean_ctor_get(v___x_487_, 1);
v_zetaDeltaFVarIds_489_ = lean_ctor_get(v___x_487_, 2);
v_postponed_490_ = lean_ctor_get(v___x_487_, 3);
v_diag_491_ = lean_ctor_get(v___x_487_, 4);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_502_);
v___x_493_ = v___x_487_;
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_diag_491_);
lean_inc(v_postponed_490_);
lean_inc(v_zetaDeltaFVarIds_489_);
lean_inc(v_cache_488_);
lean_dec(v___x_487_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_mctx_486_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_mctx_486_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_cache_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_zetaDeltaFVarIds_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_postponed_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_diag_491_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_st_ref_put(v___y_479_, v___x_496_);
v___x_498_ = lean_box(v_fst_485_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
v___jp_503_:
{
lean_object* v_snd_505_; lean_object* v_fst_506_; lean_object* v_mctx_507_; uint8_t v___x_508_; 
v_snd_505_ = lean_ctor_get(v___y_504_, 1);
lean_inc(v_snd_505_);
v_fst_506_ = lean_ctor_get(v___y_504_, 0);
lean_inc(v_fst_506_);
lean_dec_ref(v___y_504_);
v_mctx_507_ = lean_ctor_get(v_snd_505_, 1);
lean_inc_ref(v_mctx_507_);
lean_dec(v_snd_505_);
v___x_508_ = lean_unbox(v_fst_506_);
lean_dec(v_fst_506_);
v_fst_485_ = v___x_508_;
v_mctx_486_ = v_mctx_507_;
goto v___jp_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_516_, lean_object* v_fvarId_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_516_, v_fvarId_517_, v___y_518_);
lean_dec(v___y_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_521_, lean_object* v_fvarId_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_521_, v_fvarId_522_, v___y_524_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_529_, lean_object* v_fvarId_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_529_, v_fvarId_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
v___x_543_ = lean_expr_eqv(v_a_537_, v___x_542_);
if (v___x_543_ == 0)
{
size_t v___x_544_; size_t v___x_545_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_539_, v___x_544_);
v_i_539_ = v___x_545_;
goto _start;
}
else
{
return v___x_543_;
}
}
else
{
uint8_t v___x_547_; 
v___x_547_ = 0;
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_548_, lean_object* v_as_549_, lean_object* v_i_550_, lean_object* v_stop_551_){
_start:
{
size_t v_i_boxed_552_; size_t v_stop_boxed_553_; uint8_t v_res_554_; lean_object* v_r_555_; 
v_i_boxed_552_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_stop_boxed_553_ = lean_unbox_usize(v_stop_551_);
lean_dec(v_stop_551_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_548_, v_as_549_, v_i_boxed_552_, v_stop_boxed_553_);
lean_dec_ref(v_as_549_);
lean_dec_ref(v_a_548_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_array_get_size(v_as_556_);
v___x_560_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
return v___x_560_;
}
else
{
if (v___x_560_ == 0)
{
return v___x_560_;
}
else
{
size_t v___x_561_; size_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_559_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_557_, v_as_556_, v___x_561_, v___x_562_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_564_, lean_object* v_a_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_564_, v_a_565_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_as_564_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_571_, lean_object* v_indices_572_, lean_object* v_a_573_, lean_object* v_as_574_, size_t v_sz_575_, size_t v_i_576_, lean_object* v_b_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_a_584_; uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_lt(v_i_576_, v_sz_575_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v_a_573_);
lean_dec_ref(v_a_571_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_b_577_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v_b_577_);
v___x_590_ = lean_box(0);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_592_ = lean_array_uget_borrowed(v_as_574_, v_i_576_);
v___x_593_ = l_Lean_Expr_fvarId_x21(v_a_592_);
lean_inc_ref(v_a_571_);
v___x_594_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_571_, v___x_593_, v___y_579_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_608_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_608_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_608_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_608_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_572_, v_a_592_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_595_);
lean_dec(v_a_595_);
if (v___x_600_ == 0)
{
lean_del_object(v___x_597_);
v_a_584_ = v___x_591_;
goto v___jp_583_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec_ref(v_a_571_);
lean_inc(v_a_592_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_a_573_);
lean_ctor_set(v___x_601_, 1, v_a_592_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_590_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_604_);
v___x_606_ = v___x_597_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
lean_del_object(v___x_597_);
lean_dec(v_a_595_);
v_a_584_ = v___x_591_;
goto v___jp_583_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_a_573_);
lean_dec_ref(v_a_571_);
v_a_609_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_594_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_594_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
v___jp_583_:
{
size_t v___x_585_; size_t v___x_586_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_576_, v___x_585_);
lean_inc_ref(v_a_584_);
v_i_576_ = v___x_586_;
v_b_577_ = v_a_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_617_, lean_object* v_indices_618_, lean_object* v_a_619_, lean_object* v_as_620_, lean_object* v_sz_621_, lean_object* v_i_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
size_t v_sz_boxed_629_; size_t v_i_boxed_630_; lean_object* v_res_631_; 
v_sz_boxed_629_ = lean_unbox_usize(v_sz_621_);
lean_dec(v_sz_621_);
v_i_boxed_630_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_617_, v_indices_618_, v_a_619_, v_as_620_, v_sz_boxed_629_, v_i_boxed_630_, v_b_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v_as_620_);
lean_dec_ref(v_indices_618_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_632_, lean_object* v_indices_633_, lean_object* v_as_634_, size_t v_sz_635_, size_t v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_lt(v_i_636_, v_sz_635_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v_b_637_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_a_647_; lean_object* v___x_648_; 
lean_dec_ref(v_b_637_);
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_647_ = lean_array_uget_borrowed(v_as_634_, v_i_636_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v_a_647_);
v___x_648_ = lean_infer_type(v_a_647_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v_sz_650_ = lean_array_size(v_ys_632_);
v___x_651_ = ((size_t)0ULL);
lean_inc(v_a_647_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_649_, v_indices_633_, v_a_647_, v_ys_632_, v_sz_650_, v___x_651_, v___x_646_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_672_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_672_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_672_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_fst_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_670_; 
v_fst_657_ = lean_ctor_get(v_a_653_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_a_653_, 1);
lean_dec(v_unused_671_);
v___x_659_ = v_a_653_;
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_fst_657_);
lean_dec(v_a_653_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
if (lean_obj_tag(v_fst_657_) == 0)
{
size_t v___x_661_; size_t v___x_662_; 
lean_del_object(v___x_659_);
lean_del_object(v___x_655_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_add(v_i_636_, v___x_661_);
v_i_636_ = v___x_662_;
v_b_637_ = v___x_646_;
goto _start;
}
else
{
lean_object* v___x_665_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_645_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_645_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_665_);
v___x_667_ = v___x_655_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
else
{
return v___x_652_;
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_648_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_648_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_681_, lean_object* v_indices_682_, lean_object* v_as_683_, lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
size_t v_sz_boxed_692_; size_t v_i_boxed_693_; lean_object* v_res_694_; 
v_sz_boxed_692_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_693_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_681_, v_indices_682_, v_as_683_, v_sz_boxed_692_, v_i_boxed_693_, v_b_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v_as_683_);
lean_dec_ref(v_indices_682_);
lean_dec_ref(v_ys_681_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_695_, lean_object* v_ys_696_, lean_object* v_as_697_, size_t v_sz_698_, size_t v_i_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_b_700_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_a_710_; lean_object* v___x_711_; 
lean_dec_ref(v_b_700_);
v___x_708_ = lean_box(0);
v___x_709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_710_ = lean_array_uget_borrowed(v_as_697_, v_i_699_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v_a_710_);
v___x_711_ = lean_infer_type(v_a_710_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_sz_713_ = lean_array_size(v_ys_696_);
v___x_714_ = ((size_t)0ULL);
lean_inc(v_a_710_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_712_, v_indices_695_, v_a_710_, v_ys_696_, v_sz_713_, v___x_714_, v___x_709_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_735_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_735_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fst_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v_fst_720_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_a_716_, 1);
lean_dec(v_unused_734_);
v___x_722_ = v_a_716_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_fst_720_);
lean_dec(v_a_716_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_fst_720_) == 0)
{
size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
lean_del_object(v___x_722_);
lean_del_object(v___x_718_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_699_, v___x_724_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_696_, v_indices_695_, v_as_697_, v_sz_698_, v___x_725_, v___x_709_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_726_;
}
else
{
lean_object* v___x_728_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_708_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_708_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_728_);
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
else
{
return v___x_715_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_711_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_711_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_744_, lean_object* v_ys_745_, lean_object* v_as_746_, lean_object* v_sz_747_, lean_object* v_i_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_sz_boxed_755_ = lean_unbox_usize(v_sz_747_);
lean_dec(v_sz_747_);
v_i_boxed_756_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_744_, v_ys_745_, v_as_746_, v_sz_boxed_755_, v_i_boxed_756_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec_ref(v_as_746_);
lean_dec_ref(v_ys_745_);
lean_dec_ref(v_indices_744_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_758_, lean_object* v_indices_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_767_ = lean_array_size(v_indices_759_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_759_, v_ys_758_, v_indices_759_, v_sz_767_, v___x_768_, v___x_766_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_fst_774_);
lean_dec(v_a_770_);
if (lean_obj_tag(v_fst_774_) == 0)
{
lean_object* v___x_776_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_765_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_765_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v_val_778_; lean_object* v___x_780_; 
v_val_778_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_fst_774_, 1);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_val_778_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_val_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_769_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_769_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_791_, lean_object* v_indices_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_791_, v_indices_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec_ref(v_indices_792_);
lean_dec_ref(v_ys_791_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_799_, lean_object* v_as_800_, size_t v_sz_801_, size_t v_i_802_, lean_object* v_b_803_, lean_object* v___y_804_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_a_799_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v_b_803_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_b_803_);
v___x_808_ = lean_box(0);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_810_ = lean_array_uget_borrowed(v_as_800_, v_i_802_);
v___x_811_ = l_Lean_Expr_fvarId_x21(v_a_810_);
lean_inc_ref(v_a_799_);
v___x_812_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_799_, v___x_811_, v___y_804_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_828_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_828_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; 
v___x_817_ = lean_unbox(v_a_813_);
lean_dec(v_a_813_);
if (v___x_817_ == 0)
{
size_t v___x_818_; size_t v___x_819_; 
lean_del_object(v___x_815_);
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_i_802_, v___x_818_);
v_i_802_ = v___x_819_;
v_b_803_ = v___x_809_;
goto _start;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_a_810_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_799_);
lean_ctor_set(v___x_821_, 1, v_a_810_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_808_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_824_);
v___x_826_ = v___x_815_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_a_799_);
v_a_829_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_812_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_812_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_837_, lean_object* v_as_838_, lean_object* v_sz_839_, lean_object* v_i_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
size_t v_sz_boxed_844_; size_t v_i_boxed_845_; lean_object* v_res_846_; 
v_sz_boxed_844_ = lean_unbox_usize(v_sz_839_);
lean_dec(v_sz_839_);
v_i_boxed_845_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_837_, v_as_838_, v_sz_boxed_844_, v_i_boxed_845_, v_b_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v_as_838_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_847_, lean_object* v_as_848_, size_t v_sz_849_, size_t v_i_850_, lean_object* v_b_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v_b_851_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_a_861_; size_t v_sz_862_; size_t v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v_b_851_);
v___x_859_ = lean_box(0);
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_861_ = lean_array_uget_borrowed(v_as_848_, v_i_850_);
v_sz_862_ = lean_array_size(v_ys_847_);
v___x_863_ = ((size_t)0ULL);
lean_inc(v_a_861_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_861_, v_ys_847_, v_sz_862_, v___x_863_, v___x_860_, v___y_853_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_884_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_884_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_884_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_884_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_fst_869_ = lean_ctor_get(v_a_865_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_a_865_, 1);
lean_dec(v_unused_883_);
v___x_871_ = v_a_865_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_fst_869_);
lean_dec(v_a_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
if (lean_obj_tag(v_fst_869_) == 0)
{
size_t v___x_873_; size_t v___x_874_; 
lean_del_object(v___x_871_);
lean_del_object(v___x_867_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_850_, v___x_873_);
v_i_850_ = v___x_874_;
v_b_851_ = v___x_860_;
goto _start;
}
else
{
lean_object* v___x_877_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_859_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_fst_869_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_859_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_877_);
v___x_879_ = v___x_867_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
else
{
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_885_, lean_object* v_as_886_, lean_object* v_sz_887_, lean_object* v_i_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_887_);
lean_dec(v_sz_887_);
v_i_boxed_896_ = lean_unbox_usize(v_i_888_);
lean_dec(v_i_888_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_885_, v_as_886_, v_sz_boxed_895_, v_i_boxed_896_, v_b_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v_as_886_);
lean_dec_ref(v_ys_885_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_898_, lean_object* v_indParams_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; size_t v_sz_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_905_ = lean_box(0);
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_907_ = lean_array_size(v_indParams_899_);
v___x_908_ = ((size_t)0ULL);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_898_, v_indParams_899_, v_sz_907_, v___x_908_, v___x_906_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; 
v_fst_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_fst_914_);
lean_dec(v_a_910_);
if (lean_obj_tag(v_fst_914_) == 0)
{
lean_object* v___x_916_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_905_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_905_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; 
v_val_918_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v_fst_914_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_val_918_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_val_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_909_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_909_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_931_, lean_object* v_indParams_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_931_, v_indParams_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec_ref(v_indParams_932_);
lean_dec_ref(v_ys_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_939_, lean_object* v_as_940_, size_t v_sz_941_, size_t v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_939_, v_as_940_, v_sz_941_, v_i_942_, v_b_943_, v___y_945_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_961_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_950_, v_as_951_, v_sz_boxed_960_, v_i_boxed_961_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_panic_fn_borrowed(v___x_964_, v_msg_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___f_973_; lean_object* v___x_4718__overap_974_; lean_object* v___x_975_; 
v___f_973_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4718__overap_974_ = lean_panic_fn_borrowed(v___f_973_, v_msg_967_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
v___x_975_ = lean_apply_5(v___x_4718__overap_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_987_ = lean_unsigned_to_nat(107u);
v___x_988_ = lean_unsigned_to_nat(97u);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_991_ = l_mkPanicMessageWithDecl(v___x_990_, v___x_989_, v___x_988_, v___x_987_, v___x_986_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_xs_992_, size_t v_sz_993_, size_t v_i_994_, lean_object* v_bs_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_lt(v_i_994_, v_sz_993_);
if (v___x_996_ == 0)
{
return v_bs_995_;
}
else
{
lean_object* v_v_997_; lean_object* v___x_998_; lean_object* v_bs_x27_999_; lean_object* v___y_1001_; lean_object* v___x_1006_; 
v_v_997_ = lean_array_uget(v_bs_995_, v_i_994_);
v___x_998_ = lean_unsigned_to_nat(0u);
v_bs_x27_999_ = lean_array_uset(v_bs_995_, v_i_994_, v___x_998_);
v___x_1006_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_992_, v_v_997_);
lean_dec(v_v_997_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3);
v___x_1008_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1007_);
v___y_1001_ = v___x_1008_;
goto v___jp_1000_;
}
else
{
lean_object* v_val_1009_; 
v_val_1009_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___x_1006_, 1);
v___y_1001_ = v_val_1009_;
goto v___jp_1000_;
}
v___jp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_994_, v___x_1002_);
v___x_1004_ = lean_array_uset(v_bs_x27_999_, v_i_994_, v___y_1001_);
v_i_994_ = v___x_1003_;
v_bs_995_ = v___x_1004_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_xs_1010_, lean_object* v_sz_1011_, lean_object* v_i_1012_, lean_object* v_bs_1013_){
_start:
{
size_t v_sz_boxed_1014_; size_t v_i_boxed_1015_; lean_object* v_res_1016_; 
v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1011_);
lean_dec(v_sz_1011_);
v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1010_, v_sz_boxed_1014_, v_i_boxed_1015_, v_bs_1013_);
lean_dec_ref(v_xs_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_ref_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_ref_1023_ = lean_ctor_get(v___y_1020_, 2);
v___x_1024_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_inc(v_ref_1023_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_ref_1023_);
lean_ctor_set(v___x_1029_, 1, v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(lean_object* v_xs_1041_, lean_object* v_v_1042_, lean_object* v_i_1043_){
_start:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_array_get_size(v_xs_1041_);
v___x_1045_ = lean_nat_dec_lt(v_i_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v_i_1043_);
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_array_fget_borrowed(v_xs_1041_, v_i_1043_);
v___x_1048_ = lean_name_eq(v___x_1047_, v_v_1042_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_add(v_i_1043_, v___x_1049_);
lean_dec(v_i_1043_);
v_i_1043_ = v___x_1050_;
goto _start;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_i_1043_);
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7___boxed(lean_object* v_xs_1053_, lean_object* v_v_1054_, lean_object* v_i_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1053_, v_v_1054_, v_i_1055_);
lean_dec(v_v_1054_);
lean_dec_ref(v_xs_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(lean_object* v_xs_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1057_, v_v_1058_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5___boxed(lean_object* v_xs_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1061_, v_v_1062_);
lean_dec(v_v_1062_);
lean_dec_ref(v_xs_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1064_, lean_object* v_v_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1064_, v_v_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(0);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_val_1068_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_val_1068_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_val_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1076_, lean_object* v_v_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1076_, v_v_1077_);
lean_dec(v_v_1077_);
lean_dec_ref(v_xs_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_i_1079_, lean_object* v___x_1080_, lean_object* v_as_1081_, size_t v_i_1082_, size_t v_stop_1083_){
_start:
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_usize_dec_eq(v_i_1082_, v_stop_1083_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = lean_array_uget_borrowed(v_as_1081_, v_i_1082_);
v___x_1090_ = l_Lean_Expr_isFVar(v___x_1089_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_nat_dec_lt(v_i_1079_, v___x_1080_);
if (v___x_1091_ == 0)
{
goto v___jp_1084_;
}
else
{
return v___x_1091_;
}
}
else
{
goto v___jp_1084_;
}
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
return v___x_1092_;
}
v___jp_1084_:
{
size_t v___x_1085_; size_t v___x_1086_; 
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_add(v_i_1082_, v___x_1085_);
v_i_1082_ = v___x_1086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_i_1093_, lean_object* v___x_1094_, lean_object* v_as_1095_, lean_object* v_i_1096_, lean_object* v_stop_1097_){
_start:
{
size_t v_i_boxed_1098_; size_t v_stop_boxed_1099_; uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_i_boxed_1098_ = lean_unbox_usize(v_i_1096_);
lean_dec(v_i_1096_);
v_stop_boxed_1099_ = lean_unbox_usize(v_stop_1097_);
lean_dec(v_stop_1097_);
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1093_, v___x_1094_, v_as_1095_, v_i_boxed_1098_, v_stop_boxed_1099_);
lean_dec_ref(v_as_1095_);
lean_dec(v___x_1094_);
lean_dec(v_i_1093_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(lean_object* v_as_1102_, lean_object* v_a_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_zero_1105_; uint8_t v_isZero_1106_; 
v_zero_1105_ = lean_unsigned_to_nat(0u);
v_isZero_1106_ = lean_nat_dec_eq(v_x_1104_, v_zero_1105_);
if (v_isZero_1106_ == 1)
{
lean_dec(v_x_1104_);
return v_isZero_1106_;
}
else
{
lean_object* v_one_1107_; lean_object* v_n_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_one_1107_ = lean_unsigned_to_nat(1u);
v_n_1108_ = lean_nat_sub(v_x_1104_, v_one_1107_);
lean_dec(v_x_1104_);
v___x_1109_ = lean_array_fget_borrowed(v_as_1102_, v_n_1108_);
v___x_1110_ = lean_expr_eqv(v_a_1103_, v___x_1109_);
if (v___x_1110_ == 0)
{
v_x_1104_ = v_n_1108_;
goto _start;
}
else
{
lean_dec(v_n_1108_);
return v_isZero_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_as_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1112_, v_a_1113_, v_x_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_as_1112_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(lean_object* v_as_1117_, lean_object* v_i_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_array_get_size(v_as_1117_);
v___x_1120_ = lean_nat_dec_lt(v_i_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
lean_dec(v_i_1118_);
v___x_1121_ = 1;
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_array_fget_borrowed(v_as_1117_, v_i_1118_);
lean_inc(v_i_1118_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1117_, v___x_1122_, v_i_1118_);
if (v___x_1123_ == 0)
{
lean_dec(v_i_1118_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_i_1118_, v___x_1124_);
lean_dec(v_i_1118_);
v_i_1118_ = v___x_1125_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3___boxed(lean_object* v_as_1127_, lean_object* v_i_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1127_, v_i_1128_);
lean_dec_ref(v_as_1127_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_as_1131_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_as_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_as_1134_);
lean_dec_ref(v_as_1134_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1148_ = lean_unsigned_to_nat(59u);
v___x_1149_ = lean_unsigned_to_nat(96u);
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1152_ = l_mkPanicMessageWithDecl(v___x_1151_, v___x_1150_, v___x_1149_, v___x_1148_, v___x_1147_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1177_; lean_object* v_dummy_1178_; 
v___x_1177_ = lean_box(0);
v_dummy_1178_ = l_Lean_Expr_sort___override(v___x_1177_);
return v_dummy_1178_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1181_ = l_Lean_stringToMessageData(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1184_ = lean_unsigned_to_nat(2u);
v___x_1185_ = lean_unsigned_to_nat(68u);
v___x_1186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1188_ = l_mkPanicMessageWithDecl(v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1200_ = l_Lean_stringToMessageData(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1201_, lean_object* v_fixedParamPerm_1202_, lean_object* v_xs_1203_, lean_object* v_i_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v_lower_1351_; lean_object* v_upper_1352_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; uint8_t v___x_1437_; 
v___x_1336_ = lean_array_get_size(v_fixedParamPerm_1202_);
v___x_1337_ = lean_array_get_size(v_xs_1203_);
v___x_1437_ = lean_nat_dec_eq(v___x_1336_, v___x_1337_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1438_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1439_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1438_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1439_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_nat_dec_lt(v_i_1204_, v___x_1337_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1441_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v_i_1204_, v___x_1442_);
lean_dec(v_i_1204_);
v___x_1444_ = l_Nat_reprFast(v___x_1443_);
v___x_1445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
v___x_1446_ = l_Lean_MessageData_ofFormat(v___x_1445_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1441_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Nat_reprFast(v___x_1337_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
v___x_1452_ = l_Lean_MessageData_ofFormat(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1449_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1455_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1202_, v_i_1204_);
if (v___x_1457_ == 0)
{
v___y_1410_ = v_a_1205_;
v___y_1411_ = v_a_1206_;
v___y_1412_ = v_a_1207_;
v___y_1413_ = v_a_1208_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1459_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1458_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
v___jp_1210_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1216_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1215_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
v___jp_1217_:
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1223_);
if (v___x_1229_ == 0)
{
lean_object* v_name_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1230_ = lean_ctor_get(v___y_1228_, 0);
lean_inc(v_name_1230_);
lean_dec_ref(v___y_1228_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1232_ = l_Lean_MessageData_ofName(v_name_1230_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_indentExpr(v___y_1225_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1237_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1202_, v_xs_1203_);
v___x_1240_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1239_, v___y_1223_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
if (lean_obj_tag(v_a_1241_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1239_, v___y_1224_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
lean_dec_ref(v___x_1239_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1293_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1293_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1293_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
if (lean_obj_tag(v_a_1243_) == 0)
{
lean_object* v_name_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v___y_1225_);
v_name_1247_ = lean_ctor_get(v___y_1228_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1228_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; 
v_unused_1268_ = lean_ctor_get(v___y_1228_, 2);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v___y_1228_, 1);
lean_dec(v_unused_1269_);
v___x_1249_ = v___y_1228_;
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_name_1247_);
lean_dec(v___y_1228_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_array_mk(v___y_1226_);
v___x_1252_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1251_, v_name_1247_);
lean_dec(v_name_1247_);
lean_dec_ref(v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; size_t v_sz_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_sz_1254_ = lean_array_size(v___y_1223_);
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1203_, v_sz_1254_, v___x_1255_, v___y_1223_);
v___x_1257_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1222_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 2, v___y_1224_);
lean_ctor_set(v___x_1249_, 1, v___y_1218_);
lean_ctor_set(v___x_1249_, 0, v___x_1257_);
v___x_1259_ = v___x_1249_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___y_1218_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___y_1224_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1260_, 0, v_fnName_1201_);
lean_ctor_set(v___x_1260_, 1, v_fixedParamPerm_1202_);
lean_ctor_set(v___x_1260_, 2, v_i_1204_);
lean_ctor_set(v___x_1260_, 3, v___x_1256_);
lean_ctor_set(v___x_1260_, 4, v___x_1259_);
lean_ctor_set(v___x_1260_, 5, v_val_1253_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1260_);
v___x_1262_ = v___x_1245_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v___x_1252_);
lean_del_object(v___x_1249_);
lean_del_object(v___x_1245_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1266_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1265_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_val_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_val_1270_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_a_1243_, 1);
v_fst_1271_ = lean_ctor_get(v_val_1270_, 0);
v_snd_1272_ = lean_ctor_get(v_val_1270_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_val_1270_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1274_ = v_val_1270_;
v_isShared_1275_ = v_isSharedCheck_1292_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_snd_1272_);
lean_inc(v_fst_1271_);
lean_dec(v_val_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1292_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1276_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1277_ = l_Lean_indentExpr(v___y_1225_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 7);
lean_ctor_set(v___x_1274_, 1, v___x_1277_);
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1280_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_indentExpr(v_fst_1271_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_indentExpr(v_snd_1272_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1289_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_a_1294_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1242_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1242_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_val_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___x_1239_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_val_1302_ = lean_ctor_get(v_a_1241_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_a_1241_, 1);
v_fst_1303_ = lean_ctor_get(v_val_1302_, 0);
v_snd_1304_ = lean_ctor_get(v_val_1302_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_val_1302_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1306_ = v_val_1302_;
v_isShared_1307_ = v_isSharedCheck_1327_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_snd_1304_);
lean_inc(v_fst_1303_);
lean_dec(v_val_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1327_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_name_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v_name_1308_ = lean_ctor_get(v___y_1228_, 0);
lean_inc(v_name_1308_);
lean_dec_ref(v___y_1228_);
v___x_1309_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1310_ = l_Lean_MessageData_ofName(v_name_1308_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 7);
lean_ctor_set(v___x_1306_, 1, v___x_1310_);
lean_ctor_set(v___x_1306_, 0, v___x_1309_);
v___x_1312_ = v___x_1306_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1313_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_indentExpr(v___y_1225_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_indentExpr(v_fst_1303_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_indentExpr(v_snd_1304_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1324_, v___y_1220_, v___y_1221_, v___y_1219_, v___y_1227_);
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___x_1239_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_a_1328_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1240_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1240_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1353_ = l_Array_toSubarray___redArg(v___y_1344_, v_lower_1351_, v_upper_1352_);
v___x_1354_ = l_Subarray_copy___redArg(v___x_1353_);
v___x_1355_ = lean_array_get_size(v___x_1354_);
v___x_1356_ = lean_nat_dec_lt(v___y_1343_, v___x_1355_);
lean_dec(v___y_1343_);
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___y_1340_;
v___y_1220_ = v___y_1341_;
v___y_1221_ = v___y_1348_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___x_1354_;
v___y_1224_ = v___y_1345_;
v___y_1225_ = v___y_1349_;
v___y_1226_ = v___y_1350_;
v___y_1227_ = v___y_1346_;
v___y_1228_ = v___y_1347_;
goto v___jp_1217_;
}
else
{
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___y_1340_;
v___y_1220_ = v___y_1341_;
v___y_1221_ = v___y_1348_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___x_1354_;
v___y_1224_ = v___y_1345_;
v___y_1225_ = v___y_1349_;
v___y_1226_ = v___y_1350_;
v___y_1227_ = v___y_1346_;
v___y_1228_ = v___y_1347_;
goto v___jp_1217_;
}
else
{
size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_of_nat(v___x_1355_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1204_, v___x_1337_, v___x_1354_, v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___y_1340_;
v___y_1220_ = v___y_1341_;
v___y_1221_ = v___y_1348_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___x_1354_;
v___y_1224_ = v___y_1345_;
v___y_1225_ = v___y_1349_;
v___y_1226_ = v___y_1350_;
v___y_1227_ = v___y_1346_;
v___y_1228_ = v___y_1347_;
goto v___jp_1217_;
}
else
{
lean_object* v_name_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1354_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1345_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1339_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1360_ = lean_ctor_get(v___y_1347_, 0);
lean_inc(v_name_1360_);
lean_dec_ref(v___y_1347_);
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1362_ = l_Lean_MessageData_ofName(v_name_1360_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_indentExpr(v___y_1349_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1367_, v___y_1341_, v___y_1348_, v___y_1340_, v___y_1346_);
return v___x_1368_;
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = l_Lean_LocalDecl_type(v___y_1370_);
lean_dec_ref(v___y_1370_);
v___x_1376_ = l_Lean_Meta_whnfD(v___x_1375_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = l_Lean_Expr_getAppFn(v_a_1377_);
if (lean_obj_tag(v___x_1378_) == 4)
{
lean_object* v_declName_1379_; lean_object* v_us_1380_; lean_object* v___x_1381_; lean_object* v_env_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v_declName_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_declName_1379_);
v_us_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_us_1380_);
lean_dec_ref_known(v___x_1378_, 2);
v___x_1381_ = lean_st_ref_get(v___y_1374_);
v_env_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref(v_env_1382_);
lean_dec(v___x_1381_);
v___x_1383_ = 0;
v___x_1384_ = l_Lean_Environment_find_x3f(v_env_1382_, v_declName_1379_, v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec(v_us_1380_);
lean_dec(v_a_1377_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
v___y_1213_ = v___y_1373_;
v___y_1214_ = v___y_1374_;
goto v___jp_1210_;
}
else
{
lean_object* v_val_1385_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
if (lean_obj_tag(v_val_1385_) == 5)
{
lean_object* v_val_1386_; lean_object* v_toConstantVal_1387_; lean_object* v_numParams_1388_; lean_object* v_all_1389_; lean_object* v_nargs_1390_; lean_object* v_dummy_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_val_1386_ = lean_ctor_get(v_val_1385_, 0);
lean_inc_ref(v_val_1386_);
lean_dec_ref_known(v_val_1385_, 1);
v_toConstantVal_1387_ = lean_ctor_get(v_val_1386_, 0);
lean_inc_ref(v_toConstantVal_1387_);
v_numParams_1388_ = lean_ctor_get(v_val_1386_, 1);
v_all_1389_ = lean_ctor_get(v_val_1386_, 3);
lean_inc(v_all_1389_);
v_nargs_1390_ = l_Lean_Expr_getAppNumArgs(v_a_1377_);
v_dummy_1391_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1390_);
v___x_1392_ = lean_mk_array(v_nargs_1390_, v_dummy_1391_);
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_sub(v_nargs_1390_, v___x_1393_);
lean_dec(v_nargs_1390_);
lean_inc(v_a_1377_);
v___x_1395_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1377_, v___x_1392_, v___x_1394_);
v___x_1396_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1388_);
lean_inc_ref(v___x_1395_);
v___x_1397_ = l_Array_toSubarray___redArg(v___x_1395_, v___x_1396_, v_numParams_1388_);
v___x_1398_ = l_Subarray_copy___redArg(v___x_1397_);
v___x_1399_ = lean_array_get_size(v___x_1395_);
v___x_1400_ = lean_nat_dec_le(v_numParams_1388_, v___x_1396_);
if (v___x_1400_ == 0)
{
lean_inc(v_numParams_1388_);
v___y_1339_ = v_us_1380_;
v___y_1340_ = v___y_1373_;
v___y_1341_ = v___y_1371_;
v___y_1342_ = v_val_1386_;
v___y_1343_ = v___x_1396_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v___x_1398_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v_toConstantVal_1387_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v_a_1377_;
v___y_1350_ = v_all_1389_;
v_lower_1351_ = v_numParams_1388_;
v_upper_1352_ = v___x_1399_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v_us_1380_;
v___y_1340_ = v___y_1373_;
v___y_1341_ = v___y_1371_;
v___y_1342_ = v_val_1386_;
v___y_1343_ = v___x_1396_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v___x_1398_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v_toConstantVal_1387_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v_a_1377_;
v___y_1350_ = v_all_1389_;
v_lower_1351_ = v___x_1396_;
v_upper_1352_ = v___x_1399_;
goto v___jp_1338_;
}
}
else
{
lean_dec(v_val_1385_);
lean_dec(v_us_1380_);
lean_dec(v_a_1377_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
v___y_1213_ = v___y_1373_;
v___y_1214_ = v___y_1374_;
goto v___jp_1210_;
}
}
}
else
{
lean_dec_ref(v___x_1378_);
lean_dec(v_a_1377_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
v___y_1213_ = v___y_1373_;
v___y_1214_ = v___y_1374_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_a_1401_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1376_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1376_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
v___jp_1409_:
{
lean_object* v_x_1414_; lean_object* v___x_1415_; 
v_x_1414_ = lean_array_fget_borrowed(v_xs_1203_, v_i_1204_);
v___x_1415_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1414_, v___y_1410_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_LocalDecl_isLet(v_a_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1370_ = v_a_1416_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_a_1416_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1419_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1420_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1419_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
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
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_a_1429_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1415_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1415_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1468_, lean_object* v_fixedParamPerm_1469_, lean_object* v_xs_1470_, lean_object* v_i_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1468_, v_fixedParamPerm_1469_, v_xs_1470_, v_i_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_xs_1470_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1478_, lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1486_, v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(lean_object* v_as_1494_, lean_object* v_a_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1494_, v_a_1495_, v_x_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___boxed(lean_object* v_as_1499_, lean_object* v_a_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(v_as_1499_, v_a_1500_, v_x_1501_, v_x_1502_);
lean_dec_ref(v_a_1500_);
lean_dec_ref(v_as_1499_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1505_, lean_object* v_e_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = l_Lean_indentD(v_e_1506_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1505_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1509_, lean_object* v_fnName_1510_, lean_object* v_fixedParamPerm_1511_, lean_object* v_args_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1509_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1510_, v_fixedParamPerm_1511_, v_args_1512_, v_a_1519_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1520_;
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_fixedParamPerm_1511_);
lean_dec(v_fnName_1510_);
v_a_1521_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1518_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1518_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1529_, lean_object* v_fnName_1530_, lean_object* v_fixedParamPerm_1531_, lean_object* v_args_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1529_, v_fnName_1530_, v_fixedParamPerm_1531_, v_args_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_args_1532_);
return v_res_1538_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1549_ = l_Lean_MessageData_ofFormat(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1550_, lean_object* v_fnName_1551_, lean_object* v_fixedParamPerm_1552_, lean_object* v_args_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_fst_1562_; lean_object* v_snd_1563_; uint8_t v___x_1568_; 
v___x_1568_ = lean_nat_dec_lt(v_a_1554_, v_upperBound_1550_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec(v_a_1554_);
lean_dec_ref(v_fixedParamPerm_1552_);
lean_dec(v_fnName_1551_);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_b_1555_);
return v___x_1569_;
}
else
{
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1616_; 
v_fst_1570_ = lean_ctor_get(v_b_1555_, 0);
v_snd_1571_ = lean_ctor_get(v_b_1555_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_b_1555_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1573_ = v_b_1555_;
v_isShared_1574_ = v_isSharedCheck_1616_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_b_1555_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1616_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; 
lean_inc(v_a_1554_);
lean_inc_ref(v_fixedParamPerm_1552_);
lean_inc(v_fnName_1551_);
v___x_1575_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1551_, v_fixedParamPerm_1552_, v_args_1553_, v_a_1554_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1573_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = lean_array_push(v_fst_1570_, v_a_1576_);
v_fst_1562_ = v___x_1577_;
v_snd_1563_ = v_snd_1571_;
goto v___jp_1561_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1615_; 
v_a_1578_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1580_ = v___x_1575_;
v_isShared_1581_ = v_isSharedCheck_1615_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1615_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___y_1583_; uint8_t v___x_1613_; 
v___x_1613_ = l_Lean_Exception_isInterrupt(v_a_1578_);
if (v___x_1613_ == 0)
{
uint8_t v___x_1614_; 
lean_inc(v_a_1578_);
v___x_1614_ = l_Lean_Exception_isRuntime(v_a_1578_);
v___y_1583_ = v___x_1614_;
goto v___jp_1582_;
}
else
{
v___y_1583_ = v___x_1613_;
goto v___jp_1582_;
}
v___jp_1582_:
{
if (v___y_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_del_object(v___x_1580_);
v___x_1584_ = l_Lean_Elab_Structural_prettyParam(v_args_1553_, v_a_1554_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 7);
lean_ctor_set(v___x_1573_, 1, v_a_1585_);
lean_ctor_set(v___x_1573_, 0, v___x_1586_);
v___x_1588_ = v___x_1573_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_a_1585_);
v___x_1588_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
lean_inc(v_fnName_1551_);
v___x_1591_ = l_Lean_MessageData_ofName(v_fnName_1551_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Exception_toMessageData(v_a_1578_);
v___x_1596_ = l_Lean_indentD(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1594_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_snd_1571_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v_fst_1562_ = v_fst_1570_;
v_snd_1563_ = v___x_1600_;
goto v___jp_1561_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1578_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec(v_a_1554_);
lean_dec_ref(v_fixedParamPerm_1552_);
lean_dec(v_fnName_1551_);
v_a_1602_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1584_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1584_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v___x_1611_; 
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec(v_a_1554_);
lean_dec_ref(v_fixedParamPerm_1552_);
lean_dec(v_fnName_1551_);
if (v_isShared_1581_ == 0)
{
v___x_1611_ = v___x_1580_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1578_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
}
v___jp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_fst_1562_);
lean_ctor_set(v___x_1564_, 1, v_snd_1563_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_a_1554_, v___x_1565_);
lean_dec(v_a_1554_);
v_a_1554_ = v___x_1566_;
v_b_1555_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1617_, lean_object* v_fnName_1618_, lean_object* v_fixedParamPerm_1619_, lean_object* v_args_1620_, lean_object* v_a_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1617_, v_fnName_1618_, v_fixedParamPerm_1619_, v_args_1620_, v_a_1621_, v_b_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v_args_1620_);
lean_dec(v_upperBound_1617_);
return v_res_1628_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1629_; double v___x_1630_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_float_of_nat(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1632_, lean_object* v_msg_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_ref_1639_; lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1686_; 
v_ref_1639_ = lean_ctor_get(v___y_1636_, 2);
v___x_1640_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1686_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1686_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v_traceState_1646_; lean_object* v_env_1647_; lean_object* v_nextMacroScope_1648_; lean_object* v_ngen_1649_; lean_object* v_auxDeclNGen_1650_; lean_object* v_cache_1651_; lean_object* v_recordedDeps_1652_; lean_object* v_messages_1653_; lean_object* v_infoState_1654_; lean_object* v_snapshotTasks_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1685_; 
v___x_1645_ = lean_st_ref_take(v___y_1637_);
v_traceState_1646_ = lean_ctor_get(v___x_1645_, 4);
v_env_1647_ = lean_ctor_get(v___x_1645_, 0);
v_nextMacroScope_1648_ = lean_ctor_get(v___x_1645_, 1);
v_ngen_1649_ = lean_ctor_get(v___x_1645_, 2);
v_auxDeclNGen_1650_ = lean_ctor_get(v___x_1645_, 3);
v_cache_1651_ = lean_ctor_get(v___x_1645_, 5);
v_recordedDeps_1652_ = lean_ctor_get(v___x_1645_, 6);
v_messages_1653_ = lean_ctor_get(v___x_1645_, 7);
v_infoState_1654_ = lean_ctor_get(v___x_1645_, 8);
v_snapshotTasks_1655_ = lean_ctor_get(v___x_1645_, 9);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1657_ = v___x_1645_;
v_isShared_1658_ = v_isSharedCheck_1685_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_snapshotTasks_1655_);
lean_inc(v_infoState_1654_);
lean_inc(v_messages_1653_);
lean_inc(v_recordedDeps_1652_);
lean_inc(v_cache_1651_);
lean_inc(v_traceState_1646_);
lean_inc(v_auxDeclNGen_1650_);
lean_inc(v_ngen_1649_);
lean_inc(v_nextMacroScope_1648_);
lean_inc(v_env_1647_);
lean_dec(v___x_1645_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1685_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint64_t v_tid_1659_; lean_object* v_traces_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1684_; 
v_tid_1659_ = lean_ctor_get_uint64(v_traceState_1646_, sizeof(void*)*1);
v_traces_1660_ = lean_ctor_get(v_traceState_1646_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_traceState_1646_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1662_ = v_traceState_1646_;
v_isShared_1663_ = v_isSharedCheck_1684_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_traces_1660_);
lean_dec(v_traceState_1646_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1684_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; double v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1667_ = 0;
v___x_1668_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1669_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1669_, 0, v_cls_1632_);
lean_ctor_set(v___x_1669_, 1, v___x_1665_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_ctor_set_float(v___x_1669_, sizeof(void*)*3, v___x_1666_);
lean_ctor_set_float(v___x_1669_, sizeof(void*)*3 + 8, v___x_1666_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 16, v___x_1667_);
v___x_1670_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1671_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v_a_1641_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
lean_inc(v_ref_1639_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_ref_1639_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_PersistentArray_push___redArg(v_traces_1660_, v___x_1672_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1673_);
v___x_1675_ = v___x_1662_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1673_);
lean_ctor_set_uint64(v_reuseFailAlloc_1683_, sizeof(void*)*1, v_tid_1659_);
v___x_1675_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 4, v___x_1675_);
v___x_1677_ = v___x_1657_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_env_1647_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_nextMacroScope_1648_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_ngen_1649_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_auxDeclNGen_1650_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1682_, 5, v_cache_1651_);
lean_ctor_set(v_reuseFailAlloc_1682_, 6, v_recordedDeps_1652_);
lean_ctor_set(v_reuseFailAlloc_1682_, 7, v_messages_1653_);
lean_ctor_set(v_reuseFailAlloc_1682_, 8, v_infoState_1654_);
lean_ctor_set(v_reuseFailAlloc_1682_, 9, v_snapshotTasks_1655_);
v___x_1677_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_st_ref_put(v___y_1637_, v___x_1677_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1664_);
v___x_1680_ = v___x_1643_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1664_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1687_, lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1687_, v_msg_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1694_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___f_1699_; 
v___x_1698_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1699_, 0, v___x_1698_);
return v___f_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1704_; lean_object* v_recArgInfos_1705_; lean_object* v___x_1706_; 
v_report_1704_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1705_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_recArgInfos_1705_);
lean_ctor_set(v___x_1706_, 1, v_report_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1719_ = l_Lean_Name_append(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1723_, lean_object* v_fixedParamPerm_1724_, lean_object* v_xs_1725_, lean_object* v_fnName_1726_, lean_object* v_ys_1727_, lean_object* v_x_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1723_) == 1)
{
lean_object* v_val_1734_; lean_object* v_ref_1735_; lean_object* v_toCold_1736_; lean_object* v_currRecDepth_1737_; lean_object* v_ref_1738_; uint16_t v_optionFlags_1739_; uint8_t v_suppressElabErrors_1740_; uint8_t v_isRecordingDeps_1741_; lean_object* v___f_1742_; lean_object* v_args_1743_; lean_object* v___f_1744_; lean_object* v_ref_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_val_1734_ = lean_ctor_get(v_termMeasure_x3f_1723_, 0);
lean_inc(v_val_1734_);
lean_dec_ref_known(v_termMeasure_x3f_1723_, 1);
v_ref_1735_ = lean_ctor_get(v_val_1734_, 0);
lean_inc(v_ref_1735_);
v_toCold_1736_ = lean_ctor_get(v___y_1731_, 0);
v_currRecDepth_1737_ = lean_ctor_get(v___y_1731_, 1);
v_ref_1738_ = lean_ctor_get(v___y_1731_, 2);
v_optionFlags_1739_ = lean_ctor_get_uint16(v___y_1731_, sizeof(void*)*3);
v_suppressElabErrors_1740_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1741_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*3 + 3);
v___f_1742_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1724_);
v_args_1743_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1724_, v_xs_1725_, v_ys_1727_);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1744_, 0, v_val_1734_);
lean_closure_set(v___f_1744_, 1, v_fnName_1726_);
lean_closure_set(v___f_1744_, 2, v_fixedParamPerm_1724_);
lean_closure_set(v___f_1744_, 3, v_args_1743_);
v_ref_1745_ = l_Lean_replaceRef(v_ref_1735_, v_ref_1738_);
lean_dec(v_ref_1735_);
lean_inc(v_currRecDepth_1737_);
lean_inc_ref(v_toCold_1736_);
v___x_1746_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1746_, 0, v_toCold_1736_);
lean_ctor_set(v___x_1746_, 1, v_currRecDepth_1737_);
lean_ctor_set(v___x_1746_, 2, v_ref_1745_);
lean_ctor_set_uint16(v___x_1746_, sizeof(void*)*3, v_optionFlags_1739_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 2, v_suppressElabErrors_1740_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 3, v_isRecordingDeps_1741_);
v___x_1747_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1744_, v___f_1742_, v___y_1729_, v___y_1730_, v___x_1746_, v___y_1732_);
lean_dec_ref_known(v___x_1746_, 3);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1760_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1752_);
v___x_1754_ = lean_array_push(v___x_1753_, v_a_1748_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1756_);
v___x_1758_ = v___x_1750_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1747_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1747_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_args_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_termMeasure_x3f_1723_);
lean_inc_ref(v_fixedParamPerm_1724_);
v_args_1769_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1724_, v_xs_1725_, v_ys_1727_);
v___x_1770_ = lean_array_get_size(v_args_1769_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1770_, v_fnName_1726_, v_fixedParamPerm_1724_, v_args_1769_, v___x_1771_, v___x_1772_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec_ref(v_args_1769_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1809_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1809_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1809_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1808_; 
v_fst_1778_ = lean_ctor_get(v_a_1774_, 0);
v_snd_1779_ = lean_ctor_get(v_a_1774_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1781_ = v_a_1774_;
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v_a_1774_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_toCold_1790_; lean_object* v_options_1791_; uint8_t v_hasTrace_1792_; 
v_toCold_1790_ = lean_ctor_get(v___y_1731_, 0);
v_options_1791_ = lean_ctor_get(v_toCold_1790_, 2);
v_hasTrace_1792_ = lean_ctor_get_uint8(v_options_1791_, sizeof(void*)*1);
if (v_hasTrace_1792_ == 0)
{
goto v___jp_1783_;
}
else
{
lean_object* v_inheritedTraceOptions_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_inheritedTraceOptions_1793_ = lean_ctor_get(v_toCold_1790_, 11);
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1793_, v_options_1791_, v___x_1795_);
if (v___x_1796_ == 0)
{
goto v___jp_1783_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1779_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_snd_1779_);
v___x_1799_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1794_, v___x_1798_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref_known(v___x_1799_, 1);
goto v___jp_1783_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_del_object(v___x_1781_);
lean_dec(v_snd_1779_);
lean_dec(v_fst_1778_);
lean_del_object(v___x_1776_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; 
if (v_isShared_1782_ == 0)
{
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_fst_1778_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_snd_1779_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1785_);
v___x_1787_ = v___x_1776_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
else
{
return v___x_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1810_, lean_object* v_fixedParamPerm_1811_, lean_object* v_xs_1812_, lean_object* v_fnName_1813_, lean_object* v_ys_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1810_, v_fixedParamPerm_1811_, v_xs_1812_, v_fnName_1813_, v_ys_1814_, v_x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_x_1815_);
lean_dec_ref(v_xs_1812_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1822_, lean_object* v_fixedParamPerm_1823_, lean_object* v_xs_1824_, lean_object* v_value_1825_, lean_object* v_termMeasure_x3f_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___f_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; 
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1832_, 0, v_termMeasure_x3f_1826_);
lean_closure_set(v___f_1832_, 1, v_fixedParamPerm_1823_);
lean_closure_set(v___f_1832_, 2, v_xs_1824_);
lean_closure_set(v___f_1832_, 3, v_fnName_1822_);
v___x_1833_ = 0;
v___x_1834_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1825_, v___f_1832_, v___x_1833_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1835_, lean_object* v_fixedParamPerm_1836_, lean_object* v_xs_1837_, lean_object* v_value_1838_, lean_object* v_termMeasure_x3f_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1835_, v_fixedParamPerm_1836_, v_xs_1837_, v_value_1838_, v_termMeasure_x3f_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1846_, lean_object* v_fnName_1847_, lean_object* v_fixedParamPerm_1848_, lean_object* v_args_1849_, lean_object* v_inst_1850_, lean_object* v_R_1851_, lean_object* v_a_1852_, lean_object* v_b_1853_, lean_object* v_c_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1846_, v_fnName_1847_, v_fixedParamPerm_1848_, v_args_1849_, v_a_1852_, v_b_1853_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1861_, lean_object* v_fnName_1862_, lean_object* v_fixedParamPerm_1863_, lean_object* v_args_1864_, lean_object* v_inst_1865_, lean_object* v_R_1866_, lean_object* v_a_1867_, lean_object* v_b_1868_, lean_object* v_c_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1861_, v_fnName_1862_, v_fixedParamPerm_1863_, v_args_1864_, v_inst_1865_, v_R_1866_, v_a_1867_, v_b_1868_, v_c_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec_ref(v_args_1864_);
lean_dec(v_upperBound_1861_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
return v_x_1876_;
}
else
{
lean_object* v_key_1878_; lean_object* v_value_1879_; lean_object* v_tail_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1903_; 
v_key_1878_ = lean_ctor_get(v_x_1877_, 0);
v_value_1879_ = lean_ctor_get(v_x_1877_, 1);
v_tail_1880_ = lean_ctor_get(v_x_1877_, 2);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1882_ = v_x_1877_;
v_isShared_1883_ = v_isSharedCheck_1903_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_tail_1880_);
lean_inc(v_value_1879_);
lean_inc(v_key_1878_);
lean_dec(v_x_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1903_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; uint64_t v_fold_1888_; uint64_t v___x_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; size_t v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1884_ = lean_array_get_size(v_x_1876_);
v___x_1885_ = lean_uint64_of_nat(v_key_1878_);
v___x_1886_ = 32ULL;
v___x_1887_ = lean_uint64_shift_right(v___x_1885_, v___x_1886_);
v_fold_1888_ = lean_uint64_xor(v___x_1885_, v___x_1887_);
v___x_1889_ = 16ULL;
v___x_1890_ = lean_uint64_shift_right(v_fold_1888_, v___x_1889_);
v___x_1891_ = lean_uint64_xor(v_fold_1888_, v___x_1890_);
v___x_1892_ = lean_uint64_to_usize(v___x_1891_);
v___x_1893_ = lean_usize_of_nat(v___x_1884_);
v___x_1894_ = ((size_t)1ULL);
v___x_1895_ = lean_usize_sub(v___x_1893_, v___x_1894_);
v___x_1896_ = lean_usize_land(v___x_1892_, v___x_1895_);
v___x_1897_ = lean_array_uget_borrowed(v_x_1876_, v___x_1896_);
lean_inc(v___x_1897_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 2, v___x_1897_);
v___x_1899_ = v___x_1882_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_key_1878_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_value_1879_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_array_uset(v_x_1876_, v___x_1896_, v___x_1899_);
v_x_1876_ = v___x_1900_;
v_x_1877_ = v_tail_1880_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1904_, lean_object* v_source_1905_, lean_object* v_target_1906_){
_start:
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = lean_array_get_size(v_source_1905_);
v___x_1908_ = lean_nat_dec_lt(v_i_1904_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_dec_ref(v_source_1905_);
lean_dec(v_i_1904_);
return v_target_1906_;
}
else
{
lean_object* v_es_1909_; lean_object* v___x_1910_; lean_object* v_source_1911_; lean_object* v_target_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_es_1909_ = lean_array_fget(v_source_1905_, v_i_1904_);
v___x_1910_ = lean_box(0);
v_source_1911_ = lean_array_fset(v_source_1905_, v_i_1904_, v___x_1910_);
v_target_1912_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1906_, v_es_1909_);
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_add(v_i_1904_, v___x_1913_);
lean_dec(v_i_1904_);
v_i_1904_ = v___x_1914_;
v_source_1905_ = v_source_1911_;
v_target_1906_ = v_target_1912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_nbuckets_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1917_ = lean_array_get_size(v_data_1916_);
v___x_1918_ = lean_unsigned_to_nat(2u);
v_nbuckets_1919_ = lean_nat_mul(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_mk_array(v_nbuckets_1919_, v___x_1921_);
v___x_1923_ = lean_array_propagate_mark(v_data_1916_, v___x_1922_);
v___x_1924_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1920_, v_data_1916_, v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1925_, lean_object* v_x_1926_){
_start:
{
if (lean_obj_tag(v_x_1926_) == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = 0;
return v___x_1927_;
}
else
{
lean_object* v_key_1928_; lean_object* v_tail_1929_; uint8_t v___x_1930_; 
v_key_1928_ = lean_ctor_get(v_x_1926_, 0);
v_tail_1929_ = lean_ctor_get(v_x_1926_, 2);
v___x_1930_ = lean_nat_dec_eq(v_key_1928_, v_a_1925_);
if (v___x_1930_ == 0)
{
v_x_1926_ = v_tail_1929_;
goto _start;
}
else
{
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1932_, lean_object* v_x_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1932_, v_x_1933_);
lean_dec(v_x_1933_);
lean_dec(v_a_1932_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1936_, lean_object* v_a_1937_, lean_object* v_b_1938_){
_start:
{
lean_object* v_size_1939_; lean_object* v_buckets_1940_; lean_object* v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v_fold_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; lean_object* v_bkt_1954_; uint8_t v___x_1955_; 
v_size_1939_ = lean_ctor_get(v_m_1936_, 0);
v_buckets_1940_ = lean_ctor_get(v_m_1936_, 1);
v___x_1941_ = lean_array_get_size(v_buckets_1940_);
v___x_1942_ = lean_uint64_of_nat(v_a_1937_);
v___x_1943_ = 32ULL;
v___x_1944_ = lean_uint64_shift_right(v___x_1942_, v___x_1943_);
v_fold_1945_ = lean_uint64_xor(v___x_1942_, v___x_1944_);
v___x_1946_ = 16ULL;
v___x_1947_ = lean_uint64_shift_right(v_fold_1945_, v___x_1946_);
v___x_1948_ = lean_uint64_xor(v_fold_1945_, v___x_1947_);
v___x_1949_ = lean_uint64_to_usize(v___x_1948_);
v___x_1950_ = lean_usize_of_nat(v___x_1941_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_sub(v___x_1950_, v___x_1951_);
v___x_1953_ = lean_usize_land(v___x_1949_, v___x_1952_);
v_bkt_1954_ = lean_array_uget_borrowed(v_buckets_1940_, v___x_1953_);
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1937_, v_bkt_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1976_; 
lean_inc_ref(v_buckets_1940_);
lean_inc(v_size_1939_);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_m_1936_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; lean_object* v_unused_1978_; 
v_unused_1977_ = lean_ctor_get(v_m_1936_, 1);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_m_1936_, 0);
lean_dec(v_unused_1978_);
v___x_1957_ = v_m_1936_;
v_isShared_1958_ = v_isSharedCheck_1976_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v_m_1936_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1976_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v_size_x27_1960_; lean_object* v___x_1961_; lean_object* v_buckets_x27_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v_size_x27_1960_ = lean_nat_add(v_size_1939_, v___x_1959_);
lean_dec(v_size_1939_);
lean_inc(v_bkt_1954_);
v___x_1961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1961_, 0, v_a_1937_);
lean_ctor_set(v___x_1961_, 1, v_b_1938_);
lean_ctor_set(v___x_1961_, 2, v_bkt_1954_);
v_buckets_x27_1962_ = lean_array_uset(v_buckets_1940_, v___x_1953_, v___x_1961_);
v___x_1963_ = lean_unsigned_to_nat(4u);
v___x_1964_ = lean_nat_mul(v_size_x27_1960_, v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(3u);
v___x_1966_ = lean_nat_div(v___x_1964_, v___x_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_array_get_size(v_buckets_x27_1962_);
v___x_1968_ = lean_nat_dec_le(v___x_1966_, v___x_1967_);
lean_dec(v___x_1966_);
if (v___x_1968_ == 0)
{
lean_object* v_val_1969_; lean_object* v___x_1971_; 
v_val_1969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1962_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_val_1969_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1960_);
v___x_1971_ = v___x_1957_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_size_x27_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_val_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
else
{
lean_object* v___x_1974_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_buckets_x27_1962_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1960_);
v___x_1974_ = v___x_1957_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_size_x27_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_buckets_x27_1962_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_dec(v_b_1938_);
lean_dec(v_a_1937_);
return v_m_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_b_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1981_, v_sz_1980_);
if (v___x_1983_ == 0)
{
return v_b_1982_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; size_t v___x_1987_; size_t v___x_1988_; 
v_a_1984_ = lean_array_uget_borrowed(v_as_1979_, v_i_1981_);
v___x_1985_ = lean_box(0);
lean_inc(v_a_1984_);
v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1982_, v_a_1984_, v___x_1985_);
v___x_1987_ = ((size_t)1ULL);
v___x_1988_ = lean_usize_add(v_i_1981_, v___x_1987_);
v_i_1981_ = v___x_1988_;
v_b_1982_ = v___x_1986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_){
_start:
{
size_t v_sz_boxed_1994_; size_t v_i_boxed_1995_; lean_object* v_res_1996_; 
v_sz_boxed_1994_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_1995_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1990_, v_sz_boxed_1994_, v_i_boxed_1995_, v_b_1993_);
lean_dec_ref(v_as_1990_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1997_, size_t v_sz_1998_, size_t v_i_1999_, lean_object* v_b_2000_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_usize_dec_lt(v_i_1999_, v_sz_1998_);
if (v___x_2001_ == 0)
{
return v_b_2000_;
}
else
{
lean_object* v_a_2002_; lean_object* v_indicesPos_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; 
v_a_2002_ = lean_array_uget_borrowed(v_as_1997_, v_i_1999_);
v_indicesPos_2003_ = lean_ctor_get(v_a_2002_, 3);
v_sz_2004_ = lean_array_size(v_indicesPos_2003_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2003_, v_sz_2004_, v___x_2005_, v_b_2000_);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_add(v_i_1999_, v___x_2007_);
v_i_1999_ = v___x_2008_;
v_b_2000_ = v___x_2006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2010_, lean_object* v_sz_2011_, lean_object* v_i_2012_, lean_object* v_b_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2011_);
lean_dec(v_sz_2011_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2010_, v_sz_boxed_2014_, v_i_boxed_2015_, v_b_2013_);
lean_dec_ref(v_as_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_buckets_2019_; lean_object* v___x_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; uint64_t v_fold_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_buckets_2019_ = lean_ctor_get(v_m_2017_, 1);
v___x_2020_ = lean_array_get_size(v_buckets_2019_);
v___x_2021_ = lean_uint64_of_nat(v_a_2018_);
v___x_2022_ = 32ULL;
v___x_2023_ = lean_uint64_shift_right(v___x_2021_, v___x_2022_);
v_fold_2024_ = lean_uint64_xor(v___x_2021_, v___x_2023_);
v___x_2025_ = 16ULL;
v___x_2026_ = lean_uint64_shift_right(v_fold_2024_, v___x_2025_);
v___x_2027_ = lean_uint64_xor(v_fold_2024_, v___x_2026_);
v___x_2028_ = lean_uint64_to_usize(v___x_2027_);
v___x_2029_ = lean_usize_of_nat(v___x_2020_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_sub(v___x_2029_, v___x_2030_);
v___x_2032_ = lean_usize_land(v___x_2028_, v___x_2031_);
v___x_2033_ = lean_array_uget_borrowed(v_buckets_2019_, v___x_2032_);
v___x_2034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2018_, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_res_2037_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2035_, v_a_2036_);
lean_dec(v_a_2036_);
lean_dec_ref(v_m_2035_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2039_, lean_object* v_as_2040_, size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_b_2043_){
_start:
{
lean_object* v_a_2045_; uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2049_ == 0)
{
return v_b_2043_;
}
else
{
lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2066_; 
v_fst_2050_ = lean_ctor_get(v_b_2043_, 0);
v_snd_2051_ = lean_ctor_get(v_b_2043_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_b_2043_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2053_ = v_b_2043_;
v_isShared_2054_ = v_isSharedCheck_2066_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snd_2051_);
lean_inc(v_fst_2050_);
lean_dec(v_b_2043_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2066_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_a_2055_; lean_object* v_recArgPos_2056_; uint8_t v___x_2057_; 
v_a_2055_ = lean_array_uget_borrowed(v_as_2040_, v_i_2042_);
v_recArgPos_2056_ = lean_ctor_get(v_a_2055_, 2);
v___x_2057_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2039_, v_recArgPos_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_inc(v_a_2055_);
v___x_2058_ = lean_array_push(v_snd_2051_, v_a_2055_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2058_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_fst_2050_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v_a_2045_ = v___x_2060_;
goto v___jp_2044_;
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_inc(v_a_2055_);
v___x_2062_ = lean_array_push(v_fst_2050_, v_a_2055_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2062_);
v___x_2064_ = v___x_2053_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_snd_2051_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_a_2045_ = v___x_2064_;
goto v___jp_2044_;
}
}
}
}
v___jp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2042_, v___x_2046_);
v_i_2042_ = v___x_2047_;
v_b_2043_ = v_a_2045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2067_, lean_object* v_as_2068_, lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_b_2071_){
_start:
{
size_t v_sz_boxed_2072_; size_t v_i_boxed_2073_; lean_object* v_res_2074_; 
v_sz_boxed_2072_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2073_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2067_, v_as_2068_, v_sz_boxed_2072_, v_i_boxed_2073_, v_b_2071_);
lean_dec_ref(v_as_2068_);
lean_dec_ref(v___x_2067_);
return v_res_2074_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_unsigned_to_nat(16u);
v___x_2077_ = lean_mk_array(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_indicesPos_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2079_ = lean_unsigned_to_nat(0u);
v_indicesPos_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2080_, 0, v___x_2079_);
lean_ctor_set(v_indicesPos_2080_, 1, v___x_2078_);
return v_indicesPos_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2083_){
_start:
{
lean_object* v_indicesPos_2084_; size_t v_sz_2085_; size_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_fst_2090_; lean_object* v_snd_2091_; lean_object* v___x_2092_; 
v_indicesPos_2084_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2085_ = lean_array_size(v_recArgInfos_2083_);
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2083_, v_sz_2085_, v___x_2086_, v_indicesPos_2084_);
v___x_2088_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2087_, v_recArgInfos_2083_, v_sz_2085_, v___x_2086_, v___x_2088_);
lean_dec_ref(v___x_2087_);
v_fst_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_fst_2090_);
v_snd_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2091_);
lean_dec_ref(v___x_2089_);
v___x_2092_ = l_Array_append___redArg(v_snd_2091_, v_fst_2090_);
lean_dec(v_fst_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2093_);
lean_dec_ref(v_recArgInfos_2093_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2095_, lean_object* v_m_2096_, lean_object* v_a_2097_, lean_object* v_b_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2096_, v_a_2097_, v_b_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2100_, lean_object* v_m_2101_, lean_object* v_a_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2101_, v_a_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2104_, lean_object* v_m_2105_, lean_object* v_a_2106_){
_start:
{
uint8_t v_res_2107_; lean_object* v_r_2108_; 
v_res_2107_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2104_, v_m_2105_, v_a_2106_);
lean_dec(v_a_2106_);
lean_dec_ref(v_m_2105_);
v_r_2108_ = lean_box(v_res_2107_);
return v_r_2108_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2109_, lean_object* v_a_2110_, lean_object* v_x_2111_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2110_, v_x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2113_, lean_object* v_a_2114_, lean_object* v_x_2115_){
_start:
{
uint8_t v_res_2116_; lean_object* v_r_2117_; 
v_res_2116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2113_, v_a_2114_, v_x_2115_);
lean_dec(v_x_2115_);
lean_dec(v_a_2114_);
v_r_2117_ = lean_box(v_res_2116_);
return v_r_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2118_, lean_object* v_data_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2121_, lean_object* v_i_2122_, lean_object* v_source_2123_, lean_object* v_target_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2122_, v_source_2123_, v_target_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2130_, lean_object* v_a_2131_, lean_object* v_toPure_2132_, uint8_t v_____do__lift_2133_){
_start:
{
if (v_____do__lift_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_array_push(v___y_2130_, v_a_2131_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_apply_2(v_toPure_2132_, lean_box(0), v___x_2135_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_a_2131_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___y_2130_);
v___x_2138_ = lean_apply_2(v_toPure_2132_, lean_box(0), v___x_2137_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2139_, lean_object* v_a_2140_, lean_object* v_toPure_2141_, lean_object* v_____do__lift_2142_){
_start:
{
uint8_t v_____do__lift_159__boxed_2143_; lean_object* v_res_2144_; 
v_____do__lift_159__boxed_2143_ = lean_unbox(v_____do__lift_2142_);
v_res_2144_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2139_, v_a_2140_, v_toPure_2141_, v_____do__lift_159__boxed_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2145_, lean_object* v_a_2146_, lean_object* v_x_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_apply_2(v_eq_2145_, v_x_2147_, v_a_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2149_, lean_object* v___x_2150_, lean_object* v_toBind_2151_, lean_object* v_eq_2152_, lean_object* v_inst_2153_, lean_object* v_a_2154_, lean_object* v_x_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
lean_inc(v_toPure_2149_);
lean_inc(v_a_2154_);
lean_inc_ref(v___y_2156_);
v___f_2157_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2157_, 0, v___y_2156_);
lean_closure_set(v___f_2157_, 1, v_a_2154_);
lean_closure_set(v___f_2157_, 2, v_toPure_2149_);
v___x_2158_ = lean_array_get_size(v___y_2156_);
v___x_2159_ = lean_nat_dec_lt(v___x_2150_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v___y_2156_);
lean_dec(v_a_2154_);
lean_dec_ref(v_inst_2153_);
lean_dec(v_eq_2152_);
v___x_2160_ = lean_box(v___x_2159_);
v___x_2161_ = lean_apply_2(v_toPure_2149_, lean_box(0), v___x_2160_);
v___x_2162_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v___x_2161_, v___f_2157_);
return v___x_2162_;
}
else
{
if (v___x_2159_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v___y_2156_);
lean_dec(v_a_2154_);
lean_dec_ref(v_inst_2153_);
lean_dec(v_eq_2152_);
v___x_2163_ = lean_box(v___x_2159_);
v___x_2164_ = lean_apply_2(v_toPure_2149_, lean_box(0), v___x_2163_);
v___x_2165_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v___x_2164_, v___f_2157_);
return v___x_2165_;
}
else
{
lean_object* v___f_2166_; size_t v___x_2167_; size_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v_toPure_2149_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2166_, 0, v_eq_2152_);
lean_closure_set(v___f_2166_, 1, v_a_2154_);
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = lean_usize_of_nat(v___x_2158_);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2153_, v___f_2166_, v___y_2156_, v___x_2167_, v___x_2168_);
v___x_2170_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v___x_2169_, v___f_2157_);
return v___x_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2171_, lean_object* v___x_2172_, lean_object* v_toBind_2173_, lean_object* v_eq_2174_, lean_object* v_inst_2175_, lean_object* v_a_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2171_, v___x_2172_, v_toBind_2173_, v_eq_2174_, v_inst_2175_, v_a_2176_, v_x_2177_, v___y_2178_);
lean_dec(v___x_2172_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2180_, lean_object* v_____s_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_apply_2(v_toPure_2180_, lean_box(0), v_____s_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2185_, lean_object* v_eq_2186_, lean_object* v_xs_2187_){
_start:
{
lean_object* v_toApplicative_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v___x_2191_; lean_object* v_ret_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; size_t v_sz_2195_; size_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2185_, 0);
v_toBind_2189_ = lean_ctor_get(v_inst_2185_, 1);
lean_inc_n(v_toBind_2189_, 2);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2188_, 1);
v___x_2191_ = lean_unsigned_to_nat(0u);
v_ret_2192_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2185_);
lean_inc_n(v_toPure_2190_, 2);
v___f_2193_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2193_, 0, v_toPure_2190_);
lean_closure_set(v___f_2193_, 1, v___x_2191_);
lean_closure_set(v___f_2193_, 2, v_toBind_2189_);
lean_closure_set(v___f_2193_, 3, v_eq_2186_);
lean_closure_set(v___f_2193_, 4, v_inst_2185_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2194_, 0, v_toPure_2190_);
v_sz_2195_ = lean_array_size(v_xs_2187_);
v___x_2196_ = ((size_t)0ULL);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2185_, v_xs_2187_, v___f_2193_, v_sz_2195_, v___x_2196_, v_ret_2192_);
v___x_2198_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2197_, v___f_2194_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2199_, lean_object* v_00_u03b1_2200_, lean_object* v_inst_2201_, lean_object* v_eq_2202_, lean_object* v_xs_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2201_, v_eq_2202_, v_xs_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2205_, size_t v_i_2206_, lean_object* v_bs_2207_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_lt(v_i_2206_, v_sz_2205_);
if (v___x_2208_ == 0)
{
return v_bs_2207_;
}
else
{
lean_object* v_v_2209_; lean_object* v_indGroupInst_2210_; lean_object* v___x_2211_; lean_object* v_bs_x27_2212_; size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v_v_2209_ = lean_array_uget_borrowed(v_bs_2207_, v_i_2206_);
v_indGroupInst_2210_ = lean_ctor_get(v_v_2209_, 4);
lean_inc_ref(v_indGroupInst_2210_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v_bs_x27_2212_ = lean_array_uset(v_bs_2207_, v_i_2206_, v___x_2211_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2206_, v___x_2213_);
v___x_2215_ = lean_array_uset(v_bs_x27_2212_, v_i_2206_, v_indGroupInst_2210_);
v_i_2206_ = v___x_2214_;
v_bs_2207_ = v___x_2215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2217_, lean_object* v_i_2218_, lean_object* v_bs_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2217_);
lean_dec(v_sz_2217_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2218_);
lean_dec(v_i_2218_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2220_, v_i_boxed_2221_, v_bs_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2223_, lean_object* v_a_2224_, lean_object* v_as_2225_, size_t v_i_2226_, size_t v_stop_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_eq(v_i_2226_, v_stop_2227_);
if (v___x_2233_ == 0)
{
uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = 1;
v___x_2235_ = lean_array_uget_borrowed(v_as_2225_, v_i_2226_);
lean_inc_ref(v_eq_2223_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v_a_2224_);
lean_inc(v___x_2235_);
v___x_2236_ = lean_apply_7(v_eq_2223_, v___x_2235_, v_a_2224_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, lean_box(0));
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2249_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2249_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2249_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_unbox(v_a_2237_);
lean_dec(v_a_2237_);
if (v___x_2241_ == 0)
{
size_t v___x_2242_; size_t v___x_2243_; 
lean_del_object(v___x_2239_);
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2226_, v___x_2242_);
v_i_2226_ = v___x_2243_;
goto _start;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
lean_dec(v_a_2224_);
lean_dec_ref(v_eq_2223_);
v___x_2245_ = lean_box(v___x_2234_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2245_);
v___x_2247_ = v___x_2239_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_dec(v_a_2224_);
lean_dec_ref(v_eq_2223_);
return v___x_2236_;
}
}
else
{
uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v_a_2224_);
lean_dec_ref(v_eq_2223_);
v___x_2250_ = 0;
v___x_2251_ = lean_box(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2253_, lean_object* v_a_2254_, lean_object* v_as_2255_, lean_object* v_i_2256_, lean_object* v_stop_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
size_t v_i_boxed_2263_; size_t v_stop_boxed_2264_; lean_object* v_res_2265_; 
v_i_boxed_2263_ = lean_unbox_usize(v_i_2256_);
lean_dec(v_i_2256_);
v_stop_boxed_2264_ = lean_unbox_usize(v_stop_2257_);
lean_dec(v_stop_2257_);
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2253_, v_a_2254_, v_as_2255_, v_i_boxed_2263_, v_stop_boxed_2264_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_as_2255_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2266_, lean_object* v_a_2267_, uint8_t v_____do__lift_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
if (v_____do__lift_2268_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_array_push(v_b_2266_, v_a_2267_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec(v_a_2267_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_b_2266_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2279_, lean_object* v_a_2280_, lean_object* v_____do__lift_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v_____do__lift_1273__boxed_2287_; lean_object* v_res_2288_; 
v_____do__lift_1273__boxed_2287_ = lean_unbox(v_____do__lift_2281_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2279_, v_a_2280_, v_____do__lift_1273__boxed_2287_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2289_, lean_object* v_as_2290_, size_t v_sz_2291_, size_t v_i_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_a_2300_; lean_object* v___y_2305_; uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_lt(v_i_2292_, v_sz_2291_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
lean_dec_ref(v_eq_2289_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_b_2293_);
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; lean_object* v_a_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v_a_2327_ = lean_array_uget_borrowed(v_as_2290_, v_i_2292_);
v___x_2328_ = lean_array_get_size(v_b_2293_);
v___x_2329_ = lean_nat_dec_lt(v___x_2326_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_a_2327_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2293_, v_a_2327_, v___x_2329_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
v___y_2305_ = v___x_2330_;
goto v___jp_2304_;
}
else
{
if (v___x_2329_ == 0)
{
lean_object* v___x_2331_; 
lean_inc(v_a_2327_);
v___x_2331_ = lean_array_push(v_b_2293_, v_a_2327_);
v_a_2300_ = v___x_2331_;
goto v___jp_2299_;
}
else
{
size_t v___x_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = ((size_t)0ULL);
v___x_2333_ = lean_usize_of_nat(v___x_2328_);
lean_inc(v_a_2327_);
lean_inc_ref(v_eq_2289_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2289_, v_a_2327_, v_b_2293_, v___x_2332_, v___x_2333_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
lean_inc(v_a_2327_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2293_, v_a_2327_, v___x_2336_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
v___y_2305_ = v___x_2337_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_b_2293_);
lean_dec_ref(v_eq_2289_);
v_a_2338_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2334_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2334_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
v___jp_2299_:
{
size_t v___x_2301_; size_t v___x_2302_; 
v___x_2301_ = ((size_t)1ULL);
v___x_2302_ = lean_usize_add(v_i_2292_, v___x_2301_);
v_i_2292_ = v___x_2302_;
v_b_2293_ = v_a_2300_;
goto _start;
}
v___jp_2304_:
{
if (lean_obj_tag(v___y_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2315_; 
v_a_2306_ = lean_ctor_get(v___y_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___y_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2308_ = v___y_2305_;
v_isShared_2309_ = v_isSharedCheck_2315_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___y_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2315_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
if (lean_obj_tag(v_a_2306_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; 
lean_dec_ref(v_eq_2289_);
v_a_2310_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v_a_2306_, 1);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v_a_2310_);
v___x_2312_ = v___x_2308_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
lean_object* v_a_2314_; 
lean_del_object(v___x_2308_);
v_a_2314_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v_a_2306_, 1);
v_a_2300_ = v_a_2314_;
goto v___jp_2299_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_eq_2289_);
v_a_2316_ = lean_ctor_get(v___y_2305_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___y_2305_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___y_2305_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___y_2305_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2346_, lean_object* v_as_2347_, lean_object* v_sz_2348_, lean_object* v_i_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2348_);
lean_dec(v_sz_2348_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2346_, v_as_2347_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec_ref(v_as_2347_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2359_, lean_object* v_xs_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_ret_2366_; size_t v_sz_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v_ret_2366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2367_ = lean_array_size(v_xs_2360_);
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2359_, v_xs_2360_, v_sz_2367_, v___x_2368_, v_ret_2366_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2370_, lean_object* v_xs_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2370_, v_xs_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v_xs_2371_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; size_t v_sz_2386_; size_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2385_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2386_ = lean_array_size(v_recArgInfos_2379_);
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2386_, v___x_2387_, v_recArgInfos_2379_);
v___x_2389_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2385_, v___x_2388_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec_ref(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2397_, lean_object* v_eq_2398_, lean_object* v_xs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2398_, v_xs_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_eq_2407_, lean_object* v_xs_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2406_, v_eq_2407_, v_xs_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v_xs_2408_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2415_, lean_object* v_eq_2416_, lean_object* v_a_2417_, lean_object* v_as_2418_, size_t v_i_2419_, size_t v_stop_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2416_, v_a_2417_, v_as_2418_, v_i_2419_, v_stop_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_eq_2428_, lean_object* v_a_2429_, lean_object* v_as_2430_, lean_object* v_i_2431_, lean_object* v_stop_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
size_t v_i_boxed_2438_; size_t v_stop_boxed_2439_; lean_object* v_res_2440_; 
v_i_boxed_2438_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_stop_boxed_2439_ = lean_unbox_usize(v_stop_2432_);
lean_dec(v_stop_2432_);
v_res_2440_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2427_, v_eq_2428_, v_a_2429_, v_as_2430_, v_i_boxed_2438_, v_stop_boxed_2439_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec_ref(v_as_2430_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2441_, lean_object* v_eq_2442_, lean_object* v_as_2443_, size_t v_sz_2444_, size_t v_i_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2442_, v_as_2443_, v_sz_2444_, v_i_2445_, v_b_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_eq_2454_, lean_object* v_as_2455_, lean_object* v_sz_2456_, lean_object* v_i_2457_, lean_object* v_b_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
size_t v_sz_boxed_2464_; size_t v_i_boxed_2465_; lean_object* v_res_2466_; 
v_sz_boxed_2464_ = lean_unbox_usize(v_sz_2456_);
lean_dec(v_sz_2456_);
v_i_boxed_2465_ = lean_unbox_usize(v_i_2457_);
lean_dec(v_i_2457_);
v_res_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2453_, v_eq_2454_, v_as_2455_, v_sz_boxed_2464_, v_i_boxed_2465_, v_b_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_as_2455_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = l_Lean_Expr_hasMVar(v_e_2467_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_e_2467_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; lean_object* v_mctx_2473_; lean_object* v___x_2474_; lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v___x_2477_; lean_object* v_cache_2478_; lean_object* v_zetaDeltaFVarIds_2479_; lean_object* v_postponed_2480_; lean_object* v_diag_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2490_; 
v___x_2472_ = lean_st_ref_get(v___y_2468_);
v_mctx_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_mctx_2473_);
lean_dec(v___x_2472_);
v___x_2474_ = l_Lean_instantiateMVarsCore(v_mctx_2473_, v_e_2467_);
v_fst_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_fst_2475_);
v_snd_2476_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_snd_2476_);
lean_dec_ref(v___x_2474_);
v___x_2477_ = lean_st_ref_take(v___y_2468_);
v_cache_2478_ = lean_ctor_get(v___x_2477_, 1);
v_zetaDeltaFVarIds_2479_ = lean_ctor_get(v___x_2477_, 2);
v_postponed_2480_ = lean_ctor_get(v___x_2477_, 3);
v_diag_2481_ = lean_ctor_get(v___x_2477_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2477_, 0);
lean_dec(v_unused_2491_);
v___x_2483_ = v___x_2477_;
v_isShared_2484_ = v_isSharedCheck_2490_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_diag_2481_);
lean_inc(v_postponed_2480_);
lean_inc(v_zetaDeltaFVarIds_2479_);
lean_inc(v_cache_2478_);
lean_dec(v___x_2477_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2490_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v_snd_2476_);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_snd_2476_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_cache_2478_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_zetaDeltaFVarIds_2479_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_postponed_2480_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_diag_2481_);
v___x_2486_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_st_ref_put(v___y_2468_, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_fst_2475_);
return v___x_2488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2492_, v___y_2493_);
lean_dec(v___y_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2496_, v___y_2498_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2512_ = lean_unsigned_to_nat(109u);
v___x_2513_ = lean_unsigned_to_nat(216u);
v___x_2514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2516_ = l_mkPanicMessageWithDecl(v___x_2515_, v___x_2514_, v___x_2513_, v___x_2512_, v___x_2511_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2517_, size_t v_sz_2518_, size_t v_i_2519_, lean_object* v_bs_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
if (v___x_2521_ == 0)
{
return v_bs_2520_;
}
else
{
lean_object* v_v_2522_; lean_object* v___x_2523_; lean_object* v_bs_x27_2524_; lean_object* v___y_2526_; lean_object* v___x_2531_; 
v_v_2522_ = lean_array_uget(v_bs_2520_, v_i_2519_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v_bs_x27_2524_ = lean_array_uset(v_bs_2520_, v_i_2519_, v___x_2523_);
v___x_2531_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2517_, v_v_2522_);
lean_dec(v_v_2522_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2533_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2532_);
v___y_2526_ = v___x_2533_;
goto v___jp_2525_;
}
else
{
lean_object* v_val_2534_; 
v_val_2534_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v___x_2531_, 1);
v___y_2526_ = v_val_2534_;
goto v___jp_2525_;
}
v___jp_2525_:
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_add(v_i_2519_, v___x_2527_);
v___x_2529_ = lean_array_uset(v_bs_x27_2524_, v_i_2519_, v___y_2526_);
v_i_2519_ = v___x_2528_;
v_bs_2520_ = v___x_2529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2535_, lean_object* v_sz_2536_, lean_object* v_i_2537_, lean_object* v_bs_2538_){
_start:
{
size_t v_sz_boxed_2539_; size_t v_i_boxed_2540_; lean_object* v_res_2541_; 
v_sz_boxed_2539_ = lean_unbox_usize(v_sz_2536_);
lean_dec(v_sz_2536_);
v_i_boxed_2540_ = lean_unbox_usize(v_i_2537_);
lean_dec(v_i_2537_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2535_, v_sz_boxed_2539_, v_i_boxed_2540_, v_bs_2538_);
lean_dec_ref(v___x_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2542_, size_t v_i_2543_, lean_object* v_bs_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_usize_dec_lt(v_i_2543_, v_sz_2542_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_bs_2544_);
return v___x_2551_;
}
else
{
lean_object* v_v_2552_; lean_object* v___x_2553_; lean_object* v_bs_x27_2554_; lean_object* v___x_2555_; 
v_v_2552_ = lean_array_uget(v_bs_2544_, v_i_2543_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v_bs_x27_2554_ = lean_array_uset(v_bs_2544_, v_i_2543_, v___x_2553_);
v___x_2555_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2552_, v___y_2546_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = ((size_t)1ULL);
v___x_2558_ = lean_usize_add(v_i_2543_, v___x_2557_);
v___x_2559_ = lean_array_uset(v_bs_x27_2554_, v_i_2543_, v_a_2556_);
v_i_2543_ = v___x_2558_;
v_bs_2544_ = v___x_2559_;
goto _start;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec_ref(v_bs_x27_2554_);
v_a_2561_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2555_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2555_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2569_, lean_object* v_i_2570_, lean_object* v_bs_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
size_t v_sz_boxed_2577_; size_t v_i_boxed_2578_; lean_object* v_res_2579_; 
v_sz_boxed_2577_ = lean_unbox_usize(v_sz_2569_);
lean_dec(v_sz_2569_);
v_i_boxed_2578_ = lean_unbox_usize(v_i_2570_);
lean_dec(v_i_2570_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2577_, v_i_boxed_2578_, v_bs_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2579_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2580_, lean_object* v___x_2581_, lean_object* v_as_2582_, size_t v_i_2583_, size_t v_stop_2584_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_eq(v_i_2583_, v_stop_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; uint8_t v___y_2588_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2586_ = 1;
v___x_2592_ = lean_array_uget_borrowed(v_as_2582_, v_i_2583_);
v___x_2593_ = l_Lean_Expr_isFVar(v___x_2592_);
if (v___x_2593_ == 0)
{
v___y_2588_ = v_a_2580_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_nat_dec_eq(v___x_2581_, v___x_2594_);
v___y_2588_ = v___x_2595_;
goto v___jp_2587_;
}
v___jp_2587_:
{
if (v___y_2588_ == 0)
{
size_t v___x_2589_; size_t v___x_2590_; 
v___x_2589_ = ((size_t)1ULL);
v___x_2590_ = lean_usize_add(v_i_2583_, v___x_2589_);
v_i_2583_ = v___x_2590_;
goto _start;
}
else
{
return v___x_2586_;
}
}
}
else
{
uint8_t v___x_2596_; 
v___x_2596_ = 0;
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2597_, lean_object* v___x_2598_, lean_object* v_as_2599_, lean_object* v_i_2600_, lean_object* v_stop_2601_){
_start:
{
uint8_t v_a_7784__boxed_2602_; size_t v_i_boxed_2603_; size_t v_stop_boxed_2604_; uint8_t v_res_2605_; lean_object* v_r_2606_; 
v_a_7784__boxed_2602_ = lean_unbox(v_a_2597_);
v_i_boxed_2603_ = lean_unbox_usize(v_i_2600_);
lean_dec(v_i_2600_);
v_stop_boxed_2604_ = lean_unbox_usize(v_stop_2601_);
lean_dec(v_stop_2601_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7784__boxed_2602_, v___x_2598_, v_as_2599_, v_i_boxed_2603_, v_stop_boxed_2604_);
lean_dec_ref(v_as_2599_);
lean_dec(v___x_2598_);
v_r_2606_ = lean_box(v_res_2605_);
return v_r_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2607_, lean_object* v_ys_2608_, lean_object* v___x_2609_, lean_object* v_recArgInfo_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v_group_2613_, lean_object* v___x_2614_, lean_object* v_as_2615_, size_t v_sz_2616_, size_t v_i_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_a_2625_; uint8_t v___x_2629_; 
v___x_2629_ = lean_usize_dec_lt(v_i_2617_, v_sz_2616_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_b_2618_);
return v___x_2630_;
}
else
{
lean_object* v_snd_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2787_; 
v_snd_2631_ = lean_ctor_get(v_b_2618_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_b_2618_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v_b_2618_, 0);
lean_dec(v_unused_2788_);
v___x_2633_ = v_b_2618_;
v_isShared_2634_ = v_isSharedCheck_2787_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_snd_2631_);
lean_dec(v_b_2618_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2787_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_next_2635_; lean_object* v_upperBound_2636_; lean_object* v___x_2637_; 
v_next_2635_ = lean_ctor_get(v_snd_2631_, 0);
lean_inc(v_next_2635_);
v_upperBound_2636_ = lean_ctor_get(v_snd_2631_, 1);
v___x_2637_ = lean_box(0);
if (lean_obj_tag(v_next_2635_) == 0)
{
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
goto v___jp_2638_;
}
else
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2786_; 
v_val_2643_ = lean_ctor_get(v_next_2635_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_next_2635_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2645_ = v_next_2635_;
v_isShared_2646_ = v_isSharedCheck_2786_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v_next_2635_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2786_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint8_t v___x_2647_; 
v___x_2647_ = lean_nat_dec_lt(v_val_2643_, v_upperBound_2636_);
if (v___x_2647_ == 0)
{
lean_del_object(v___x_2645_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
goto v___jp_2638_;
}
else
{
lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2783_; 
lean_inc(v_upperBound_2636_);
lean_del_object(v___x_2633_);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_snd_2631_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; lean_object* v_unused_2785_; 
v_unused_2784_ = lean_ctor_get(v_snd_2631_, 1);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_snd_2631_, 0);
lean_dec(v_unused_2785_);
v___x_2649_ = v_snd_2631_;
v_isShared_2650_ = v_isSharedCheck_2783_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v_snd_2631_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2783_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v_a_2651_ = lean_array_uget_borrowed(v_as_2615_, v_i_2617_);
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_add(v_val_2643_, v___x_2652_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2653_);
v___x_2655_ = v___x_2645_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2657_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2655_);
v___x_2657_ = v___x_2649_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_upperBound_2636_);
v___x_2657_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; 
lean_inc(v___y_2622_);
lean_inc_ref(v___y_2621_);
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc_ref(v___x_2607_);
v___x_2658_ = lean_infer_type(v___x_2607_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_Meta_whnfD(v_a_2659_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; uint8_t v___x_2662_; lean_object* v___x_2663_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v___x_2662_ = 0;
lean_inc(v_a_2651_);
v___x_2663_ = l_Lean_Meta_forallMetaTelescope(v_a_2651_, v___x_2662_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_snd_2665_; lean_object* v_fst_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2756_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v_snd_2665_ = lean_ctor_get(v_a_2664_, 1);
v_fst_2666_ = lean_ctor_get(v_a_2664_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2668_ = v_a_2664_;
v_isShared_2669_ = v_isSharedCheck_2756_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2665_);
lean_inc(v_fst_2666_);
lean_dec(v_a_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2756_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_snd_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2754_; 
v_snd_2670_ = lean_ctor_get(v_snd_2665_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_snd_2665_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_snd_2665_, 0);
lean_dec(v_unused_2755_);
v___x_2672_ = v_snd_2665_;
v_isShared_2673_ = v_isSharedCheck_2754_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2670_);
lean_dec(v_snd_2665_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2754_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2670_, v_a_2661_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; uint8_t v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_unbox(v_a_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2678_; 
lean_dec(v_a_2675_);
lean_del_object(v___x_2668_);
lean_dec(v_fst_2666_);
lean_dec(v_val_2643_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2657_);
lean_ctor_set(v___x_2672_, 0, v___x_2637_);
v___x_2678_ = v___x_2672_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2657_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
v_a_2625_ = v___x_2678_;
goto v___jp_2624_;
}
}
else
{
size_t v_sz_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v_sz_2680_ = lean_array_size(v_fst_2666_);
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2680_, v___x_2681_, v_fst_2666_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = lean_array_get_size(v_a_2683_);
v___x_2731_ = lean_nat_dec_lt(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec(v_a_2675_);
lean_del_object(v___x_2668_);
goto v___jp_2684_;
}
else
{
if (v___x_2731_ == 0)
{
lean_dec(v_a_2675_);
lean_del_object(v___x_2668_);
goto v___jp_2684_;
}
else
{
size_t v___x_2732_; uint8_t v___x_2733_; uint8_t v___x_2734_; 
v___x_2732_ = lean_usize_of_nat(v___x_2730_);
v___x_2733_ = lean_unbox(v_a_2675_);
lean_dec(v_a_2675_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2733_, v___x_2614_, v_a_2683_, v___x_2681_, v___x_2732_);
if (v___x_2734_ == 0)
{
lean_del_object(v___x_2668_);
goto v___jp_2684_;
}
else
{
lean_object* v___x_2736_; 
lean_dec(v_a_2683_);
lean_del_object(v___x_2672_);
lean_dec(v_val_2643_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2657_);
lean_ctor_set(v___x_2668_, 0, v___x_2637_);
v___x_2736_ = v___x_2668_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2657_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
v_a_2625_ = v___x_2736_;
goto v___jp_2624_;
}
}
}
}
v___jp_2684_:
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2683_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2687_; 
lean_dec(v_a_2683_);
lean_dec(v_val_2643_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2657_);
lean_ctor_set(v___x_2672_, 0, v___x_2637_);
v___x_2687_ = v___x_2672_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2657_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
v_a_2625_ = v___x_2687_;
goto v___jp_2624_;
}
}
else
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2608_, v_a_2683_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2720_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2720_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
if (lean_obj_tag(v_a_2690_) == 1)
{
lean_object* v___x_2695_; 
lean_dec_ref_known(v_a_2690_, 1);
lean_del_object(v___x_2692_);
lean_dec(v_a_2683_);
lean_dec(v_val_2643_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2657_);
lean_ctor_set(v___x_2672_, 0, v___x_2637_);
v___x_2695_ = v___x_2672_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2657_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
v_a_2625_ = v___x_2695_;
goto v___jp_2624_;
}
}
else
{
lean_object* v_fnName_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2690_);
lean_dec_ref(v___x_2607_);
v_fnName_2697_ = lean_ctor_get(v_recArgInfo_2610_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_recArgInfo_2610_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2715_ = lean_ctor_get(v_recArgInfo_2610_, 5);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_recArgInfo_2610_, 4);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_recArgInfo_2610_, 3);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2610_, 2);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_recArgInfo_2610_, 1);
lean_dec(v_unused_2719_);
v___x_2699_ = v_recArgInfo_2610_;
v_isShared_2700_ = v_isSharedCheck_2714_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_fnName_2697_);
lean_dec(v_recArgInfo_2610_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2714_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
size_t v_sz_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v_sz_2701_ = lean_array_size(v_a_2683_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2609_, v_sz_2701_, v___x_2681_, v_a_2683_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 5, v_val_2643_);
lean_ctor_set(v___x_2699_, 4, v_group_2613_);
lean_ctor_set(v___x_2699_, 3, v___x_2702_);
lean_ctor_set(v___x_2699_, 2, v___x_2612_);
lean_ctor_set(v___x_2699_, 1, v___x_2611_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_fnName_2697_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2713_, 3, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_group_2613_);
lean_ctor_set(v_reuseFailAlloc_2713_, 5, v_val_2643_);
v___x_2704_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2657_);
lean_ctor_set(v___x_2672_, 0, v___x_2706_);
v___x_2708_ = v___x_2672_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2657_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2708_);
v___x_2710_ = v___x_2692_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_a_2683_);
lean_del_object(v___x_2672_);
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2721_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2689_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2689_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2675_);
lean_del_object(v___x_2672_);
lean_del_object(v___x_2668_);
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2738_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2682_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2682_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_del_object(v___x_2672_);
lean_del_object(v___x_2668_);
lean_dec(v_fst_2666_);
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2746_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2674_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2674_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2661_);
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2757_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2663_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2663_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2765_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2660_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2660_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v___x_2657_);
lean_dec(v_val_2643_);
lean_dec_ref(v_group_2613_);
lean_dec(v___x_2612_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_recArgInfo_2610_);
lean_dec_ref(v___x_2607_);
v_a_2773_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2658_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2658_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
}
}
}
v___jp_2638_:
{
lean_object* v___x_2640_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2637_);
v___x_2640_ = v___x_2633_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_snd_2631_);
v___x_2640_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
}
}
}
v___jp_2624_:
{
size_t v___x_2626_; size_t v___x_2627_; 
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_add(v_i_2617_, v___x_2626_);
v_i_2617_ = v___x_2627_;
v_b_2618_ = v_a_2625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2789_ = _args[0];
lean_object* v_ys_2790_ = _args[1];
lean_object* v___x_2791_ = _args[2];
lean_object* v_recArgInfo_2792_ = _args[3];
lean_object* v___x_2793_ = _args[4];
lean_object* v___x_2794_ = _args[5];
lean_object* v_group_2795_ = _args[6];
lean_object* v___x_2796_ = _args[7];
lean_object* v_as_2797_ = _args[8];
lean_object* v_sz_2798_ = _args[9];
lean_object* v_i_2799_ = _args[10];
lean_object* v_b_2800_ = _args[11];
lean_object* v___y_2801_ = _args[12];
lean_object* v___y_2802_ = _args[13];
lean_object* v___y_2803_ = _args[14];
lean_object* v___y_2804_ = _args[15];
lean_object* v___y_2805_ = _args[16];
_start:
{
size_t v_sz_boxed_2806_; size_t v_i_boxed_2807_; lean_object* v_res_2808_; 
v_sz_boxed_2806_ = lean_unbox_usize(v_sz_2798_);
lean_dec(v_sz_2798_);
v_i_boxed_2807_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_res_2808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2789_, v_ys_2790_, v___x_2791_, v_recArgInfo_2792_, v___x_2793_, v___x_2794_, v_group_2795_, v___x_2796_, v_as_2797_, v_sz_boxed_2806_, v_i_boxed_2807_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_as_2797_);
lean_dec(v___x_2796_);
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_ys_2790_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v_ys_2811_, lean_object* v___x_2812_, lean_object* v_recArgInfo_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_group_2816_, lean_object* v_as_2817_, size_t v_sz_2818_, size_t v_i_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_a_2827_; uint8_t v___x_2831_; 
v___x_2831_ = lean_usize_dec_lt(v_i_2819_, v_sz_2818_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_b_2820_);
return v___x_2832_;
}
else
{
lean_object* v_snd_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2989_; 
v_snd_2833_ = lean_ctor_get(v_b_2820_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_b_2820_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_b_2820_, 0);
lean_dec(v_unused_2990_);
v___x_2835_ = v_b_2820_;
v_isShared_2836_ = v_isSharedCheck_2989_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_snd_2833_);
lean_dec(v_b_2820_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2989_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_next_2837_; lean_object* v_upperBound_2838_; lean_object* v___x_2839_; 
v_next_2837_ = lean_ctor_get(v_snd_2833_, 0);
lean_inc(v_next_2837_);
v_upperBound_2838_ = lean_ctor_get(v_snd_2833_, 1);
v___x_2839_ = lean_box(0);
if (lean_obj_tag(v_next_2837_) == 0)
{
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
goto v___jp_2840_;
}
else
{
lean_object* v_val_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2988_; 
v_val_2845_ = lean_ctor_get(v_next_2837_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_next_2837_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2847_ = v_next_2837_;
v_isShared_2848_ = v_isSharedCheck_2988_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_val_2845_);
lean_dec(v_next_2837_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2988_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_nat_dec_lt(v_val_2845_, v_upperBound_2838_);
if (v___x_2849_ == 0)
{
lean_del_object(v___x_2847_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
goto v___jp_2840_;
}
else
{
lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2985_; 
lean_inc(v_upperBound_2838_);
lean_del_object(v___x_2835_);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_snd_2833_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; lean_object* v_unused_2987_; 
v_unused_2986_ = lean_ctor_get(v_snd_2833_, 1);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v_snd_2833_, 0);
lean_dec(v_unused_2987_);
v___x_2851_ = v_snd_2833_;
v_isShared_2852_ = v_isSharedCheck_2985_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v_snd_2833_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2985_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v_a_2853_ = lean_array_uget_borrowed(v_as_2817_, v_i_2819_);
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_add(v_val_2845_, v___x_2854_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2855_);
v___x_2857_ = v___x_2847_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2859_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2857_);
v___x_2859_ = v___x_2851_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_upperBound_2838_);
v___x_2859_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc_ref(v___x_2809_);
v___x_2860_ = lean_infer_type(v___x_2809_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = l_Lean_Meta_whnfD(v_a_2861_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = 0;
lean_inc(v_a_2853_);
v___x_2865_ = l_Lean_Meta_forallMetaTelescope(v_a_2853_, v___x_2864_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v_snd_2867_; lean_object* v_fst_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2958_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v_snd_2867_ = lean_ctor_get(v_a_2866_, 1);
v_fst_2868_ = lean_ctor_get(v_a_2866_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2870_ = v_a_2866_;
v_isShared_2871_ = v_isSharedCheck_2958_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_snd_2867_);
lean_inc(v_fst_2868_);
lean_dec(v_a_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2958_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_snd_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2956_; 
v_snd_2872_ = lean_ctor_get(v_snd_2867_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_snd_2867_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v_snd_2867_, 0);
lean_dec(v_unused_2957_);
v___x_2874_ = v_snd_2867_;
v_isShared_2875_ = v_isSharedCheck_2956_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_snd_2872_);
lean_dec(v_snd_2867_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2956_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2872_, v_a_2863_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; uint8_t v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = lean_unbox(v_a_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2880_; 
lean_dec(v_a_2877_);
lean_del_object(v___x_2870_);
lean_dec(v_fst_2868_);
lean_dec(v_val_2845_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2859_);
lean_ctor_set(v___x_2874_, 0, v___x_2839_);
v___x_2880_ = v___x_2874_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2859_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_a_2827_ = v___x_2880_;
goto v___jp_2826_;
}
}
else
{
size_t v_sz_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v_sz_2882_ = lean_array_size(v_fst_2868_);
v___x_2883_ = ((size_t)0ULL);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2882_, v___x_2883_, v_fst_2868_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_array_get_size(v_a_2885_);
v___x_2933_ = lean_nat_dec_lt(v___x_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_dec(v_a_2877_);
lean_del_object(v___x_2870_);
goto v___jp_2886_;
}
else
{
if (v___x_2933_ == 0)
{
lean_dec(v_a_2877_);
lean_del_object(v___x_2870_);
goto v___jp_2886_;
}
else
{
size_t v___x_2934_; uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_usize_of_nat(v___x_2932_);
v___x_2935_ = lean_unbox(v_a_2877_);
lean_dec(v_a_2877_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2935_, v___x_2810_, v_a_2885_, v___x_2883_, v___x_2934_);
if (v___x_2936_ == 0)
{
lean_del_object(v___x_2870_);
goto v___jp_2886_;
}
else
{
lean_object* v___x_2938_; 
lean_dec(v_a_2885_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2845_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2859_);
lean_ctor_set(v___x_2870_, 0, v___x_2839_);
v___x_2938_ = v___x_2870_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v___x_2859_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
v_a_2827_ = v___x_2938_;
goto v___jp_2826_;
}
}
}
}
v___jp_2886_:
{
uint8_t v___x_2887_; 
v___x_2887_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2885_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2889_; 
lean_dec(v_a_2885_);
lean_dec(v_val_2845_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2859_);
lean_ctor_set(v___x_2874_, 0, v___x_2839_);
v___x_2889_ = v___x_2874_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2859_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v_a_2827_ = v___x_2889_;
goto v___jp_2826_;
}
}
else
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2811_, v_a_2885_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2922_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2922_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
if (lean_obj_tag(v_a_2892_) == 1)
{
lean_object* v___x_2897_; 
lean_dec_ref_known(v_a_2892_, 1);
lean_del_object(v___x_2894_);
lean_dec(v_a_2885_);
lean_dec(v_val_2845_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2859_);
lean_ctor_set(v___x_2874_, 0, v___x_2839_);
v___x_2897_ = v___x_2874_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v___x_2859_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
v_a_2827_ = v___x_2897_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_fnName_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2809_);
v_fnName_2899_ = lean_ctor_get(v_recArgInfo_2813_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_recArgInfo_2813_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; lean_object* v_unused_2918_; lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; 
v_unused_2917_ = lean_ctor_get(v_recArgInfo_2813_, 5);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_recArgInfo_2813_, 4);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_recArgInfo_2813_, 3);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_recArgInfo_2813_, 2);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_recArgInfo_2813_, 1);
lean_dec(v_unused_2921_);
v___x_2901_ = v_recArgInfo_2813_;
v_isShared_2902_ = v_isSharedCheck_2916_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_fnName_2899_);
lean_dec(v_recArgInfo_2813_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2916_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
size_t v_sz_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v_sz_2903_ = lean_array_size(v_a_2885_);
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2812_, v_sz_2903_, v___x_2883_, v_a_2885_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 5, v_val_2845_);
lean_ctor_set(v___x_2901_, 4, v_group_2816_);
lean_ctor_set(v___x_2901_, 3, v___x_2904_);
lean_ctor_set(v___x_2901_, 2, v___x_2815_);
lean_ctor_set(v___x_2901_, 1, v___x_2814_);
v___x_2906_ = v___x_2901_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_fnName_2899_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_group_2816_);
lean_ctor_set(v_reuseFailAlloc_2915_, 5, v_val_2845_);
v___x_2906_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2859_);
lean_ctor_set(v___x_2874_, 0, v___x_2908_);
v___x_2910_ = v___x_2874_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2859_);
v___x_2910_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2912_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2910_);
v___x_2912_ = v___x_2894_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_a_2885_);
lean_del_object(v___x_2874_);
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2923_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2891_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2891_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2877_);
lean_del_object(v___x_2874_);
lean_del_object(v___x_2870_);
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2940_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2884_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2884_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_del_object(v___x_2874_);
lean_del_object(v___x_2870_);
lean_dec(v_fst_2868_);
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2948_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2876_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2876_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2863_);
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2959_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2865_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2865_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2967_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2862_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2862_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v___x_2859_);
lean_dec(v_val_2845_);
lean_dec_ref(v_group_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_recArgInfo_2813_);
lean_dec_ref(v___x_2809_);
v_a_2975_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2860_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2860_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
}
}
}
v___jp_2840_:
{
lean_object* v___x_2842_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2839_);
v___x_2842_ = v___x_2835_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_snd_2833_);
v___x_2842_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
}
}
v___jp_2826_:
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = ((size_t)1ULL);
v___x_2829_ = lean_usize_add(v_i_2819_, v___x_2828_);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2809_, v_ys_2811_, v___x_2812_, v_recArgInfo_2813_, v___x_2814_, v___x_2815_, v_group_2816_, v___x_2810_, v_as_2817_, v_sz_2818_, v___x_2829_, v_a_2827_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2991_ = _args[0];
lean_object* v___x_2992_ = _args[1];
lean_object* v_ys_2993_ = _args[2];
lean_object* v___x_2994_ = _args[3];
lean_object* v_recArgInfo_2995_ = _args[4];
lean_object* v___x_2996_ = _args[5];
lean_object* v___x_2997_ = _args[6];
lean_object* v_group_2998_ = _args[7];
lean_object* v_as_2999_ = _args[8];
lean_object* v_sz_3000_ = _args[9];
lean_object* v_i_3001_ = _args[10];
lean_object* v_b_3002_ = _args[11];
lean_object* v___y_3003_ = _args[12];
lean_object* v___y_3004_ = _args[13];
lean_object* v___y_3005_ = _args[14];
lean_object* v___y_3006_ = _args[15];
lean_object* v___y_3007_ = _args[16];
_start:
{
size_t v_sz_boxed_3008_; size_t v_i_boxed_3009_; lean_object* v_res_3010_; 
v_sz_boxed_3008_ = lean_unbox_usize(v_sz_3000_);
lean_dec(v_sz_3000_);
v_i_boxed_3009_ = lean_unbox_usize(v_i_3001_);
lean_dec(v_i_3001_);
v_res_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2991_, v___x_2992_, v_ys_2993_, v___x_2994_, v_recArgInfo_2995_, v___x_2996_, v___x_2997_, v_group_2998_, v_as_2999_, v_sz_boxed_3008_, v_i_boxed_3009_, v_b_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec_ref(v_as_2999_);
lean_dec_ref(v___x_2994_);
lean_dec_ref(v_ys_2993_);
lean_dec(v___x_2992_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3011_, lean_object* v_fixedParamPerm_3012_, lean_object* v_xs_3013_, lean_object* v___x_3014_, lean_object* v_recArgPos_3015_, lean_object* v_a_3016_, lean_object* v___x_3017_, lean_object* v___x_3018_, lean_object* v_ys_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_toIndGroupInfo_3026_; lean_object* v_all_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3065_; 
v_toIndGroupInfo_3026_ = lean_ctor_get(v_group_3011_, 0);
lean_inc_ref(v_toIndGroupInfo_3026_);
v_all_3027_ = lean_ctor_get(v_toIndGroupInfo_3026_, 0);
lean_inc_ref(v_ys_3019_);
lean_inc_ref(v_fixedParamPerm_3012_);
v___x_3028_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3012_, v_xs_3013_, v_ys_3019_);
v___x_3029_ = lean_array_get(v___x_3014_, v___x_3028_, v_recArgPos_3015_);
v___x_3030_ = lean_array_get_size(v_all_3027_);
v___x_3031_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3026_);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_toIndGroupInfo_3026_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; lean_object* v_unused_3067_; 
v_unused_3066_ = lean_ctor_get(v_toIndGroupInfo_3026_, 1);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v_toIndGroupInfo_3026_, 0);
lean_dec(v_unused_3067_);
v___x_3033_ = v_toIndGroupInfo_3026_;
v_isShared_3034_ = v_isSharedCheck_3065_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v_toIndGroupInfo_3026_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3065_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3030_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
lean_ctor_set(v___x_3033_, 0, v___x_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3031_);
v___x_3037_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3037_);
v_sz_3040_ = lean_array_size(v_a_3016_);
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3029_, v___x_3017_, v_ys_3019_, v___x_3028_, v___x_3018_, v_fixedParamPerm_3012_, v_recArgPos_3015_, v_group_3011_, v_a_3016_, v_sz_3040_, v___x_3041_, v___x_3039_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v_ys_3019_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3055_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_fst_3047_; 
v_fst_3047_ = lean_ctor_get(v_a_3043_, 0);
lean_inc(v_fst_3047_);
lean_dec(v_a_3043_);
if (lean_obj_tag(v_fst_3047_) == 0)
{
lean_object* v___x_3049_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3038_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3038_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v_val_3051_; lean_object* v___x_3053_; 
v_val_3051_ = lean_ctor_get(v_fst_3047_, 0);
lean_inc(v_val_3051_);
lean_dec_ref_known(v_fst_3047_, 1);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v_val_3051_);
v___x_3053_ = v___x_3045_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_val_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
v_a_3056_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3042_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3042_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3068_, lean_object* v_fixedParamPerm_3069_, lean_object* v_xs_3070_, lean_object* v___x_3071_, lean_object* v_recArgPos_3072_, lean_object* v_a_3073_, lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v_ys_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3068_, v_fixedParamPerm_3069_, v_xs_3070_, v___x_3071_, v_recArgPos_3072_, v_a_3073_, v___x_3074_, v___x_3075_, v_ys_3076_, v_x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec_ref(v_x_3077_);
lean_dec(v___x_3074_);
lean_dec_ref(v_a_3073_);
lean_dec_ref(v___x_3071_);
lean_dec_ref(v_xs_3070_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3084_, lean_object* v_a_3085_, lean_object* v_xs_3086_, lean_object* v_value_3087_, lean_object* v_as_3088_, size_t v_i_3089_, size_t v_stop_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_a_3098_; lean_object* v_val_3103_; uint8_t v___x_3105_; 
v___x_3105_ = lean_usize_dec_eq(v_i_3089_, v_stop_3090_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v_fixedParamPerm_3107_; lean_object* v_recArgPos_3108_; lean_object* v_indGroupInst_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = lean_array_uget_borrowed(v_as_3088_, v_i_3089_);
v_fixedParamPerm_3107_ = lean_ctor_get(v___x_3106_, 1);
v_recArgPos_3108_ = lean_ctor_get(v___x_3106_, 2);
v_indGroupInst_3109_ = lean_ctor_get(v___x_3106_, 4);
v___x_3110_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_indGroupInst_3109_);
lean_inc_ref(v_group_3084_);
v___x_3111_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3084_, v_indGroupInst_3109_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; uint8_t v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = lean_unbox(v_a_3112_);
lean_dec(v_a_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3114_ = lean_array_get_size(v_a_3085_);
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = lean_nat_dec_eq(v___x_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___f_3117_; lean_object* v___x_3118_; 
lean_inc(v___x_3106_);
lean_inc_ref(v_a_3085_);
lean_inc(v_recArgPos_3108_);
lean_inc_ref(v_xs_3086_);
lean_inc_ref(v_fixedParamPerm_3107_);
lean_inc_ref(v_group_3084_);
v___f_3117_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3117_, 0, v_group_3084_);
lean_closure_set(v___f_3117_, 1, v_fixedParamPerm_3107_);
lean_closure_set(v___f_3117_, 2, v_xs_3086_);
lean_closure_set(v___f_3117_, 3, v___x_3110_);
lean_closure_set(v___f_3117_, 4, v_recArgPos_3108_);
lean_closure_set(v___f_3117_, 5, v_a_3085_);
lean_closure_set(v___f_3117_, 6, v___x_3114_);
lean_closure_set(v___f_3117_, 7, v___x_3106_);
lean_inc_ref(v_value_3087_);
v___x_3118_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3087_, v___f_3117_, v___x_3116_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
if (lean_obj_tag(v_a_3119_) == 0)
{
v_a_3098_ = v_b_3091_;
goto v___jp_3097_;
}
else
{
lean_object* v_val_3120_; 
v_val_3120_ = lean_ctor_get(v_a_3119_, 0);
lean_inc(v_val_3120_);
lean_dec_ref_known(v_a_3119_, 1);
v_val_3103_ = v_val_3120_;
goto v___jp_3102_;
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
v_a_3121_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3118_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3118_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
v_a_3098_ = v_b_3091_;
goto v___jp_3097_;
}
}
else
{
lean_inc(v___x_3106_);
v_val_3103_ = v___x_3106_;
goto v___jp_3102_;
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
v_a_3129_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3111_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3111_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3137_; 
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_b_3091_);
return v___x_3137_;
}
v___jp_3097_:
{
size_t v___x_3099_; size_t v___x_3100_; 
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_i_3089_, v___x_3099_);
v_i_3089_ = v___x_3100_;
v_b_3091_ = v_a_3098_;
goto _start;
}
v___jp_3102_:
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_array_push(v_b_3091_, v_val_3103_);
v_a_3098_ = v___x_3104_;
goto v___jp_3097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3138_, lean_object* v_a_3139_, lean_object* v_xs_3140_, lean_object* v_value_3141_, lean_object* v_as_3142_, lean_object* v_i_3143_, lean_object* v_stop_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
size_t v_i_boxed_3151_; size_t v_stop_boxed_3152_; lean_object* v_res_3153_; 
v_i_boxed_3151_ = lean_unbox_usize(v_i_3143_);
lean_dec(v_i_3143_);
v_stop_boxed_3152_ = lean_unbox_usize(v_stop_3144_);
lean_dec(v_stop_3144_);
v_res_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3138_, v_a_3139_, v_xs_3140_, v_value_3141_, v_as_3142_, v_i_boxed_3151_, v_stop_boxed_3152_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_as_3142_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3154_, lean_object* v_a_3155_, lean_object* v_xs_3156_, lean_object* v_value_3157_, lean_object* v_as_3158_, lean_object* v_start_3159_, lean_object* v_stop_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3167_ = lean_nat_dec_lt(v_start_3159_, v_stop_3160_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref(v_value_3157_);
lean_dec_ref(v_xs_3156_);
lean_dec_ref(v_a_3155_);
lean_dec_ref(v_group_3154_);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
return v___x_3168_;
}
else
{
lean_object* v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = lean_array_get_size(v_as_3158_);
v___x_3170_ = lean_nat_dec_le(v_stop_3160_, v___x_3169_);
if (v___x_3170_ == 0)
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_nat_dec_lt(v_start_3159_, v___x_3169_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec_ref(v_value_3157_);
lean_dec_ref(v_xs_3156_);
lean_dec_ref(v_a_3155_);
lean_dec_ref(v_group_3154_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
return v___x_3172_;
}
else
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_usize_of_nat(v_start_3159_);
v___x_3174_ = lean_usize_of_nat(v___x_3169_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3154_, v_a_3155_, v_xs_3156_, v_value_3157_, v_as_3158_, v___x_3173_, v___x_3174_, v___x_3166_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
return v___x_3175_;
}
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_usize_of_nat(v_start_3159_);
v___x_3177_ = lean_usize_of_nat(v_stop_3160_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3154_, v_a_3155_, v_xs_3156_, v_value_3157_, v_as_3158_, v___x_3176_, v___x_3177_, v___x_3166_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
return v___x_3178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3179_, lean_object* v_a_3180_, lean_object* v_xs_3181_, lean_object* v_value_3182_, lean_object* v_as_3183_, lean_object* v_start_3184_, lean_object* v_stop_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3179_, v_a_3180_, v_xs_3181_, v_value_3182_, v_as_3183_, v_start_3184_, v_stop_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v_stop_3185_);
lean_dec(v_start_3184_);
lean_dec_ref(v_as_3183_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3192_, lean_object* v_xs_3193_, lean_object* v_value_3194_, lean_object* v_recArgInfos_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3201_; 
lean_inc_ref(v_group_3192_);
v___x_3201_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3192_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = lean_array_get_size(v_recArgInfos_3195_);
v___x_3205_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3192_, v_a_3202_, v_xs_3193_, v_value_3194_, v_recArgInfos_3195_, v___x_3203_, v___x_3204_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v_value_3194_);
lean_dec_ref(v_xs_3193_);
lean_dec_ref(v_group_3192_);
v_a_3206_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3201_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3201_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3214_, lean_object* v_xs_3215_, lean_object* v_value_3216_, lean_object* v_recArgInfos_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_Elab_Structural_argsInGroup(v_group_3214_, v_xs_3215_, v_value_3216_, v_recArgInfos_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec_ref(v_recArgInfos_3217_);
return v_res_3223_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_unsigned_to_nat(10u);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3227_, lean_object* v_i_3228_, lean_object* v_acc_3229_){
_start:
{
lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = lean_array_get_size(v_xss_3227_);
v___x_3231_ = lean_nat_dec_lt(v_i_3228_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_mk_empty_array_with_capacity(v___x_3232_);
v___x_3234_ = lean_array_push(v___x_3233_, v_acc_3229_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3235_ = lean_array_fget_borrowed(v_xss_3227_, v_i_3228_);
v___x_3236_ = lean_unsigned_to_nat(0u);
v___x_3237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3238_ = lean_array_get_size(v___x_3235_);
v___x_3239_ = lean_nat_dec_lt(v___x_3236_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_dec_ref(v_acc_3229_);
return v___x_3237_;
}
else
{
size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = lean_usize_of_nat(v___x_3238_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3228_, v_acc_3229_, v_xss_3227_, v___x_3235_, v___x_3240_, v___x_3241_, v___x_3237_);
return v___x_3242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3243_, lean_object* v_acc_3244_, lean_object* v_xss_3245_, lean_object* v_as_3246_, size_t v_i_3247_, size_t v_stop_3248_, lean_object* v_b_3249_){
_start:
{
uint8_t v___x_3250_; 
v___x_3250_ = lean_usize_dec_eq(v_i_3247_, v_stop_3248_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; size_t v___x_3257_; size_t v___x_3258_; 
v___x_3251_ = lean_array_uget_borrowed(v_as_3246_, v_i_3247_);
v___x_3252_ = lean_unsigned_to_nat(1u);
v___x_3253_ = lean_nat_add(v_i_3243_, v___x_3252_);
lean_inc(v___x_3251_);
lean_inc_ref(v_acc_3244_);
v___x_3254_ = lean_array_push(v_acc_3244_, v___x_3251_);
v___x_3255_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3245_, v___x_3253_, v___x_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = l_Array_append___redArg(v_b_3249_, v___x_3255_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = ((size_t)1ULL);
v___x_3258_ = lean_usize_add(v_i_3247_, v___x_3257_);
v_i_3247_ = v___x_3258_;
v_b_3249_ = v___x_3256_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3244_);
return v_b_3249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3260_, lean_object* v_acc_3261_, lean_object* v_xss_3262_, lean_object* v_as_3263_, lean_object* v_i_3264_, lean_object* v_stop_3265_, lean_object* v_b_3266_){
_start:
{
size_t v_i_boxed_3267_; size_t v_stop_boxed_3268_; lean_object* v_res_3269_; 
v_i_boxed_3267_ = lean_unbox_usize(v_i_3264_);
lean_dec(v_i_3264_);
v_stop_boxed_3268_ = lean_unbox_usize(v_stop_3265_);
lean_dec(v_stop_3265_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3260_, v_acc_3261_, v_xss_3262_, v_as_3263_, v_i_boxed_3267_, v_stop_boxed_3268_, v_b_3266_);
lean_dec_ref(v_as_3263_);
lean_dec_ref(v_xss_3262_);
lean_dec(v_i_3260_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3270_, lean_object* v_i_3271_, lean_object* v_acc_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3270_, v_i_3271_, v_acc_3272_);
lean_dec(v_i_3271_);
lean_dec_ref(v_xss_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3274_, lean_object* v_xss_3275_, lean_object* v_i_3276_, lean_object* v_acc_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3275_, v_i_3276_, v_acc_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3279_, lean_object* v_xss_3280_, lean_object* v_i_3281_, lean_object* v_acc_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3279_, v_xss_3280_, v_i_3281_, v_acc_3282_);
lean_dec(v_i_3281_);
lean_dec_ref(v_xss_3280_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3284_, lean_object* v_i_3285_, lean_object* v_acc_3286_, lean_object* v_xss_3287_, lean_object* v_as_3288_, size_t v_i_3289_, size_t v_stop_3290_, lean_object* v_b_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3285_, v_acc_3286_, v_xss_3287_, v_as_3288_, v_i_3289_, v_stop_3290_, v_b_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3293_, lean_object* v_i_3294_, lean_object* v_acc_3295_, lean_object* v_xss_3296_, lean_object* v_as_3297_, lean_object* v_i_3298_, lean_object* v_stop_3299_, lean_object* v_b_3300_){
_start:
{
size_t v_i_boxed_3301_; size_t v_stop_boxed_3302_; lean_object* v_res_3303_; 
v_i_boxed_3301_ = lean_unbox_usize(v_i_3298_);
lean_dec(v_i_3298_);
v_stop_boxed_3302_ = lean_unbox_usize(v_stop_3299_);
lean_dec(v_stop_3299_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3293_, v_i_3294_, v_acc_3295_, v_xss_3296_, v_as_3297_, v_i_boxed_3301_, v_stop_boxed_3302_, v_b_3300_);
lean_dec_ref(v_as_3297_);
lean_dec_ref(v_xss_3296_);
lean_dec(v_i_3294_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3304_, size_t v_i_3305_, size_t v_stop_3306_, lean_object* v_b_3307_){
_start:
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_usize_dec_eq(v_i_3305_, v_stop_3306_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; size_t v___x_3312_; size_t v___x_3313_; 
v___x_3309_ = lean_array_uget_borrowed(v_as_3304_, v_i_3305_);
v___x_3310_ = lean_array_get_size(v___x_3309_);
v___x_3311_ = lean_nat_mul(v_b_3307_, v___x_3310_);
lean_dec(v_b_3307_);
v___x_3312_ = ((size_t)1ULL);
v___x_3313_ = lean_usize_add(v_i_3305_, v___x_3312_);
v_i_3305_ = v___x_3313_;
v_b_3307_ = v___x_3311_;
goto _start;
}
else
{
return v_b_3307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3315_, lean_object* v_i_3316_, lean_object* v_stop_3317_, lean_object* v_b_3318_){
_start:
{
size_t v_i_boxed_3319_; size_t v_stop_boxed_3320_; lean_object* v_res_3321_; 
v_i_boxed_3319_ = lean_unbox_usize(v_i_3316_);
lean_dec(v_i_3316_);
v_stop_boxed_3320_ = lean_unbox_usize(v_stop_3317_);
lean_dec(v_stop_3317_);
v_res_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3315_, v_i_boxed_3319_, v_stop_boxed_3320_, v_b_3318_);
lean_dec_ref(v_as_3315_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3322_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___y_3327_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3323_ = lean_unsigned_to_nat(10u);
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_array_get_size(v_xss_3322_);
v___x_3334_ = lean_nat_dec_lt(v___x_3325_, v___x_3333_);
if (v___x_3334_ == 0)
{
v___y_3327_ = v___x_3324_;
goto v___jp_3326_;
}
else
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_nat_dec_le(v___x_3333_, v___x_3333_);
if (v___x_3335_ == 0)
{
if (v___x_3334_ == 0)
{
v___y_3327_ = v___x_3324_;
goto v___jp_3326_;
}
else
{
size_t v___x_3336_; size_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = lean_usize_of_nat(v___x_3333_);
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3322_, v___x_3336_, v___x_3337_, v___x_3324_);
v___y_3327_ = v___x_3338_;
goto v___jp_3326_;
}
}
else
{
size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((size_t)0ULL);
v___x_3340_ = lean_usize_of_nat(v___x_3333_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3322_, v___x_3339_, v___x_3340_, v___x_3324_);
v___y_3327_ = v___x_3341_;
goto v___jp_3326_;
}
}
v___jp_3326_:
{
uint8_t v___x_3328_; 
v___x_3328_ = lean_nat_dec_lt(v___x_3323_, v___y_3327_);
lean_dec(v___y_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3330_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3322_, v___x_3325_, v___x_3329_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_box(0);
return v___x_3332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3342_);
lean_dec_ref(v_xss_3342_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3344_, lean_object* v_xss_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3347_, lean_object* v_xss_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3347_, v_xss_3348_);
lean_dec_ref(v_xss_3348_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3350_, lean_object* v_as_3351_, size_t v_i_3352_, size_t v_stop_3353_, lean_object* v_b_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3351_, v_i_3352_, v_stop_3353_, v_b_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3356_, lean_object* v_as_3357_, lean_object* v_i_3358_, lean_object* v_stop_3359_, lean_object* v_b_3360_){
_start:
{
size_t v_i_boxed_3361_; size_t v_stop_boxed_3362_; lean_object* v_res_3363_; 
v_i_boxed_3361_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_stop_boxed_3362_ = lean_unbox_usize(v_stop_3359_);
lean_dec(v_stop_3359_);
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3356_, v_as_3357_, v_i_boxed_3361_, v_stop_boxed_3362_, v_b_3360_);
lean_dec_ref(v_as_3357_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3364_, size_t v_i_3365_, size_t v_stop_3366_, lean_object* v_b_3367_){
_start:
{
uint8_t v___x_3368_; 
v___x_3368_ = lean_usize_dec_eq(v_i_3365_, v_stop_3366_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; size_t v___x_3371_; size_t v___x_3372_; 
v___x_3369_ = lean_array_uget_borrowed(v_as_3364_, v_i_3365_);
v___x_3370_ = l_Array_append___redArg(v_b_3367_, v___x_3369_);
v___x_3371_ = ((size_t)1ULL);
v___x_3372_ = lean_usize_add(v_i_3365_, v___x_3371_);
v_i_3365_ = v___x_3372_;
v_b_3367_ = v___x_3370_;
goto _start;
}
else
{
return v_b_3367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3374_, lean_object* v_i_3375_, lean_object* v_stop_3376_, lean_object* v_b_3377_){
_start:
{
size_t v_i_boxed_3378_; size_t v_stop_boxed_3379_; lean_object* v_res_3380_; 
v_i_boxed_3378_ = lean_unbox_usize(v_i_3375_);
lean_dec(v_i_3375_);
v_stop_boxed_3379_ = lean_unbox_usize(v_stop_3376_);
lean_dec(v_stop_3376_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3374_, v_i_boxed_3378_, v_stop_boxed_3379_, v_b_3377_);
lean_dec_ref(v_as_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
if (lean_obj_tag(v_a_3381_) == 0)
{
lean_object* v___x_3383_; 
v___x_3383_ = l_List_reverse___redArg(v_a_3382_);
return v___x_3383_;
}
else
{
lean_object* v_head_3384_; lean_object* v_tail_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3395_; 
v_head_3384_ = lean_ctor_get(v_a_3381_, 0);
v_tail_3385_ = lean_ctor_get(v_a_3381_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3387_ = v_a_3381_;
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_tail_3385_);
lean_inc(v_head_3384_);
lean_dec(v_a_3381_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3389_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3384_);
v___x_3390_ = l_Lean_MessageData_ofFormat(v___x_3389_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v_a_3382_);
lean_ctor_set(v___x_3387_, 0, v___x_3390_);
v___x_3392_ = v___x_3387_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_a_3382_);
v___x_3392_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v_a_3381_ = v_tail_3385_;
v_a_3382_ = v___x_3392_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_bs_3398_){
_start:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3399_ == 0)
{
return v_bs_3398_;
}
else
{
lean_object* v_v_3400_; lean_object* v___x_3401_; lean_object* v_bs_x27_3402_; lean_object* v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v_v_3400_ = lean_array_uget(v_bs_3398_, v_i_3397_);
v___x_3401_ = lean_unsigned_to_nat(0u);
v_bs_x27_3402_ = lean_array_uset(v_bs_3398_, v_i_3397_, v___x_3401_);
v___x_3403_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3400_);
lean_dec(v_v_3400_);
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_add(v_i_3397_, v___x_3404_);
v___x_3406_ = lean_array_uset(v_bs_x27_3402_, v_i_3397_, v___x_3403_);
v_i_3397_ = v___x_3405_;
v_bs_3398_ = v___x_3406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_bs_3410_){
_start:
{
size_t v_sz_boxed_3411_; size_t v_i_boxed_3412_; lean_object* v_res_3413_; 
v_sz_boxed_3411_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3411_, v_i_boxed_3412_, v_bs_3410_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3414_, lean_object* v_as_3415_, size_t v_sz_3416_, size_t v_i_3417_, lean_object* v_b_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_lt(v_i_3417_, v_sz_3416_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_dec_ref(v_xs_3414_);
v___x_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3425_, 0, v_b_3418_);
return v___x_3425_;
}
else
{
lean_object* v_snd_3426_; lean_object* v_snd_3427_; lean_object* v_snd_3428_; lean_object* v_snd_3429_; lean_object* v_fst_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3574_; 
v_snd_3426_ = lean_ctor_get(v_b_3418_, 1);
lean_inc(v_snd_3426_);
v_snd_3427_ = lean_ctor_get(v_snd_3426_, 1);
lean_inc(v_snd_3427_);
v_snd_3428_ = lean_ctor_get(v_snd_3427_, 1);
lean_inc(v_snd_3428_);
v_snd_3429_ = lean_ctor_get(v_snd_3428_, 1);
lean_inc(v_snd_3429_);
v_fst_3430_ = lean_ctor_get(v_b_3418_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_b_3418_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v_b_3418_, 1);
lean_dec(v_unused_3575_);
v___x_3432_ = v_b_3418_;
v_isShared_3433_ = v_isSharedCheck_3574_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_fst_3430_);
lean_dec(v_b_3418_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3574_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_fst_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3572_; 
v_fst_3434_ = lean_ctor_get(v_snd_3426_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_snd_3426_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_snd_3426_, 1);
lean_dec(v_unused_3573_);
v___x_3436_ = v_snd_3426_;
v_isShared_3437_ = v_isSharedCheck_3572_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_fst_3434_);
lean_dec(v_snd_3426_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3572_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_fst_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3570_; 
v_fst_3438_ = lean_ctor_get(v_snd_3427_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_snd_3427_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_snd_3427_, 1);
lean_dec(v_unused_3571_);
v___x_3440_ = v_snd_3427_;
v_isShared_3441_ = v_isSharedCheck_3570_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_fst_3438_);
lean_dec(v_snd_3427_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3570_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_fst_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3568_; 
v_fst_3442_ = lean_ctor_get(v_snd_3428_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_snd_3428_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_snd_3428_, 1);
lean_dec(v_unused_3569_);
v___x_3444_ = v_snd_3428_;
v_isShared_3445_ = v_isSharedCheck_3568_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_fst_3442_);
lean_dec(v_snd_3428_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3568_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v_array_3446_; lean_object* v_start_3447_; lean_object* v_stop_3448_; uint8_t v___x_3449_; 
v_array_3446_ = lean_ctor_get(v_snd_3429_, 0);
v_start_3447_ = lean_ctor_get(v_snd_3429_, 1);
v_stop_3448_ = lean_ctor_get(v_snd_3429_, 2);
v___x_3449_ = lean_nat_dec_lt(v_start_3447_, v_stop_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3451_; 
lean_dec_ref(v_xs_3414_);
if (v_isShared_3445_ == 0)
{
v___x_3451_ = v___x_3444_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_snd_3429_);
v___x_3451_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3451_);
v___x_3453_ = v___x_3440_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3453_);
v___x_3455_ = v___x_3436_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3455_);
v___x_3457_ = v___x_3432_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
}
}
}
else
{
lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3564_; 
lean_inc(v_stop_3448_);
lean_inc(v_start_3447_);
lean_inc_ref(v_array_3446_);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; lean_object* v_unused_3566_; lean_object* v_unused_3567_; 
v_unused_3565_ = lean_ctor_get(v_snd_3429_, 2);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_snd_3429_, 1);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v_snd_3429_, 0);
lean_dec(v_unused_3567_);
v___x_3464_ = v_snd_3429_;
v_isShared_3465_ = v_isSharedCheck_3564_;
goto v_resetjp_3463_;
}
else
{
lean_dec(v_snd_3429_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3564_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_array_3466_; lean_object* v_start_3467_; lean_object* v_stop_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v_array_3466_ = lean_ctor_get(v_fst_3442_, 0);
v_start_3467_ = lean_ctor_get(v_fst_3442_, 1);
v_stop_3468_ = lean_ctor_get(v_fst_3442_, 2);
v___x_3469_ = lean_array_fget(v_array_3446_, v_start_3447_);
v___x_3470_ = lean_unsigned_to_nat(1u);
v___x_3471_ = lean_nat_add(v_start_3447_, v___x_3470_);
lean_dec(v_start_3447_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v___x_3471_);
v___x_3473_ = v___x_3464_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_array_3446_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_stop_3448_);
v___x_3473_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
uint8_t v___x_3474_; 
v___x_3474_ = lean_nat_dec_lt(v_start_3467_, v_stop_3468_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3476_; 
lean_dec(v___x_3469_);
lean_dec_ref(v_xs_3414_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v___x_3473_);
v___x_3476_ = v___x_3444_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fst_3442_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3473_);
v___x_3476_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3476_);
v___x_3478_ = v___x_3440_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3478_);
v___x_3480_ = v___x_3436_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3482_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3480_);
v___x_3482_ = v___x_3432_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
}
}
}
else
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3559_; 
lean_inc(v_stop_3468_);
lean_inc(v_start_3467_);
lean_inc_ref(v_array_3466_);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_fst_3442_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3560_ = lean_ctor_get(v_fst_3442_, 2);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_fst_3442_, 1);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_fst_3442_, 0);
lean_dec(v_unused_3562_);
v___x_3489_ = v_fst_3442_;
v_isShared_3490_ = v_isSharedCheck_3559_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_fst_3442_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3559_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v_array_3491_; lean_object* v_start_3492_; lean_object* v_stop_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v_array_3491_ = lean_ctor_get(v_fst_3438_, 0);
v_start_3492_ = lean_ctor_get(v_fst_3438_, 1);
v_stop_3493_ = lean_ctor_get(v_fst_3438_, 2);
v___x_3494_ = lean_array_fget(v_array_3466_, v_start_3467_);
v___x_3495_ = lean_nat_add(v_start_3467_, v___x_3470_);
lean_dec(v_start_3467_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v___x_3495_);
v___x_3497_ = v___x_3489_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_array_3466_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_stop_3468_);
v___x_3497_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_nat_dec_lt(v_start_3492_, v_stop_3493_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___x_3494_);
lean_dec(v___x_3469_);
lean_dec_ref(v_xs_3414_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v___x_3473_);
lean_ctor_set(v___x_3444_, 0, v___x_3497_);
v___x_3500_ = v___x_3444_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___x_3473_);
v___x_3500_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3500_);
v___x_3502_ = v___x_3440_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3502_);
v___x_3504_ = v___x_3436_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3504_);
v___x_3506_ = v___x_3432_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3554_; 
lean_inc(v_stop_3493_);
lean_inc(v_start_3492_);
lean_inc_ref(v_array_3491_);
lean_del_object(v___x_3432_);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_fst_3438_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; lean_object* v_unused_3556_; lean_object* v_unused_3557_; 
v_unused_3555_ = lean_ctor_get(v_fst_3438_, 2);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_fst_3438_, 1);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_fst_3438_, 0);
lean_dec(v_unused_3557_);
v___x_3513_ = v_fst_3438_;
v_isShared_3514_ = v_isSharedCheck_3554_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v_fst_3438_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3554_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v_a_3515_ = lean_array_uget_borrowed(v_as_3415_, v_i_3417_);
v___x_3516_ = lean_array_fget(v_array_3491_, v_start_3492_);
v___x_3517_ = lean_nat_add(v_start_3492_, v___x_3470_);
lean_dec(v_start_3492_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v___x_3517_);
v___x_3519_ = v___x_3513_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_array_3491_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_stop_3493_);
v___x_3519_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; 
lean_inc_ref(v_xs_3414_);
lean_inc(v_a_3515_);
v___x_3520_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3515_, v___x_3469_, v_xs_3414_, v___x_3516_, v___x_3494_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3544_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
v_snd_3523_ = lean_ctor_get(v_a_3521_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3525_ = v_a_3521_;
v_isShared_3526_ = v_isSharedCheck_3544_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_snd_3523_);
lean_inc(v_fst_3522_);
lean_dec(v_a_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3544_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_fst_3430_);
lean_ctor_set(v___x_3527_, 1, v_snd_3523_);
v___x_3528_ = lean_array_push(v_fst_3434_, v_fst_3522_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 1, v___x_3473_);
lean_ctor_set(v___x_3525_, 0, v___x_3497_);
v___x_3530_ = v___x_3525_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3473_);
v___x_3530_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v___x_3530_);
lean_ctor_set(v___x_3444_, 0, v___x_3519_);
v___x_3532_ = v___x_3444_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3534_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3532_);
lean_ctor_set(v___x_3440_, 0, v___x_3528_);
v___x_3534_ = v___x_3440_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3534_);
lean_ctor_set(v___x_3436_, 0, v___x_3527_);
v___x_3536_ = v___x_3436_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
size_t v___x_3537_; size_t v___x_3538_; 
v___x_3537_ = ((size_t)1ULL);
v___x_3538_ = lean_usize_add(v_i_3417_, v___x_3537_);
v_i_3417_ = v___x_3538_;
v_b_3418_ = v___x_3536_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref(v___x_3497_);
lean_dec_ref(v___x_3473_);
lean_del_object(v___x_3444_);
lean_del_object(v___x_3440_);
lean_del_object(v___x_3436_);
lean_dec(v_fst_3434_);
lean_dec(v_fst_3430_);
lean_dec_ref(v_xs_3414_);
v_a_3545_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3520_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3520_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3576_, lean_object* v_as_3577_, lean_object* v_sz_3578_, lean_object* v_i_3579_, lean_object* v_b_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
size_t v_sz_boxed_3586_; size_t v_i_boxed_3587_; lean_object* v_res_3588_; 
v_sz_boxed_3586_ = lean_unbox_usize(v_sz_3578_);
lean_dec(v_sz_3578_);
v_i_boxed_3587_ = lean_unbox_usize(v_i_3579_);
lean_dec(v_i_3579_);
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3576_, v_as_3577_, v_sz_boxed_3586_, v_i_boxed_3587_, v_b_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v_as_3577_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
if (lean_obj_tag(v_a_3589_) == 0)
{
lean_object* v___x_3591_; 
v___x_3591_ = l_List_reverse___redArg(v_a_3590_);
return v___x_3591_;
}
else
{
lean_object* v_head_3592_; lean_object* v_tail_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3602_; 
v_head_3592_ = lean_ctor_get(v_a_3589_, 0);
v_tail_3593_ = lean_ctor_get(v_a_3589_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3595_ = v_a_3589_;
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_tail_3593_);
lean_inc(v_head_3592_);
lean_dec(v_a_3589_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3597_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3592_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_a_3590_);
lean_ctor_set(v___x_3595_, 0, v___x_3597_);
v___x_3599_ = v___x_3595_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_a_3590_);
v___x_3599_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
v_a_3589_ = v_tail_3593_;
v_a_3590_ = v___x_3599_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3603_, lean_object* v_j_3604_){
_start:
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = lean_array_get_size(v_as_3603_);
v___x_3606_ = lean_nat_dec_lt(v_j_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_j_3604_);
v___x_3607_ = lean_box(0);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3608_ = lean_array_fget_borrowed(v_as_3603_, v_j_3604_);
v___x_3609_ = lean_array_get_size(v___x_3608_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_nat_dec_eq(v___x_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_unsigned_to_nat(1u);
v___x_3613_ = lean_nat_add(v_j_3604_, v___x_3612_);
lean_dec(v_j_3604_);
v_j_3604_ = v___x_3613_;
goto _start;
}
else
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3615_, 0, v_j_3604_);
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3616_, lean_object* v_j_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3616_, v_j_3617_);
lean_dec_ref(v_as_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3619_, lean_object* v_as_3620_, size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_b_3623_){
_start:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref(v_a_3619_);
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_b_3623_);
return v___x_3626_;
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; size_t v___x_3630_; size_t v___x_3631_; 
v_a_3627_ = lean_array_uget_borrowed(v_as_3620_, v_i_3622_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3619_);
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v_a_3619_);
lean_ctor_set(v___x_3628_, 1, v_a_3627_);
v___x_3629_ = lean_array_push(v_b_3623_, v___x_3628_);
v___x_3630_ = ((size_t)1ULL);
v___x_3631_ = lean_usize_add(v_i_3622_, v___x_3630_);
v_i_3622_ = v___x_3631_;
v_b_3623_ = v___x_3629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3633_, lean_object* v_as_3634_, lean_object* v_sz_3635_, lean_object* v_i_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3635_);
lean_dec(v_sz_3635_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3633_, v_as_3634_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3637_);
lean_dec_ref(v_as_3634_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3642_, lean_object* v_xs_3643_, lean_object* v_as_3644_, size_t v_sz_3645_, size_t v_i_3646_, lean_object* v_b_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
uint8_t v___x_3653_; 
v___x_3653_ = lean_usize_dec_lt(v_i_3646_, v_sz_3645_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; 
lean_dec_ref(v_xs_3643_);
lean_dec_ref(v_a_3642_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v_b_3647_);
return v___x_3654_;
}
else
{
lean_object* v_snd_3655_; lean_object* v_fst_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3699_; 
v_snd_3655_ = lean_ctor_get(v_b_3647_, 1);
v_fst_3656_ = lean_ctor_get(v_b_3647_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_b_3647_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3658_ = v_b_3647_;
v_isShared_3659_ = v_isSharedCheck_3699_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_snd_3655_);
lean_inc(v_fst_3656_);
lean_dec(v_b_3647_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3699_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v_array_3660_; lean_object* v_start_3661_; lean_object* v_stop_3662_; uint8_t v___x_3663_; 
v_array_3660_ = lean_ctor_get(v_snd_3655_, 0);
v_start_3661_ = lean_ctor_get(v_snd_3655_, 1);
v_stop_3662_ = lean_ctor_get(v_snd_3655_, 2);
v___x_3663_ = lean_nat_dec_lt(v_start_3661_, v_stop_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3665_; 
lean_dec_ref(v_xs_3643_);
lean_dec_ref(v_a_3642_);
if (v_isShared_3659_ == 0)
{
v___x_3665_ = v___x_3658_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_fst_3656_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_snd_3655_);
v___x_3665_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
return v___x_3666_;
}
}
else
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3695_; 
lean_inc(v_stop_3662_);
lean_inc(v_start_3661_);
lean_inc_ref(v_array_3660_);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_snd_3655_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; lean_object* v_unused_3697_; lean_object* v_unused_3698_; 
v_unused_3696_ = lean_ctor_get(v_snd_3655_, 2);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_snd_3655_, 1);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_snd_3655_, 0);
lean_dec(v_unused_3698_);
v___x_3669_ = v_snd_3655_;
v_isShared_3670_ = v_isSharedCheck_3695_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v_snd_3655_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3695_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_a_3671_ = lean_array_uget_borrowed(v_as_3644_, v_i_3646_);
v___x_3672_ = lean_array_fget(v_array_3660_, v_start_3661_);
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_add(v_start_3661_, v___x_3673_);
lean_dec(v_start_3661_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3674_);
v___x_3676_ = v___x_3669_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_array_3660_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_stop_3662_);
v___x_3676_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
lean_inc(v_a_3671_);
lean_inc_ref(v_xs_3643_);
lean_inc_ref(v_a_3642_);
v___x_3677_ = l_Lean_Elab_Structural_argsInGroup(v_a_3642_, v_xs_3643_, v_a_3671_, v___x_3672_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___x_3672_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = lean_array_push(v_fst_3656_, v_a_3678_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v___x_3676_);
lean_ctor_set(v___x_3658_, 0, v___x_3679_);
v___x_3681_ = v___x_3658_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v___x_3676_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
size_t v___x_3682_; size_t v___x_3683_; 
v___x_3682_ = ((size_t)1ULL);
v___x_3683_ = lean_usize_add(v_i_3646_, v___x_3682_);
v_i_3646_ = v___x_3683_;
v_b_3647_ = v___x_3681_;
goto _start;
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v___x_3676_);
lean_del_object(v___x_3658_);
lean_dec(v_fst_3656_);
lean_dec_ref(v_xs_3643_);
lean_dec_ref(v_a_3642_);
v_a_3686_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3677_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3677_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3700_, lean_object* v_xs_3701_, lean_object* v_as_3702_, lean_object* v_sz_3703_, lean_object* v_i_3704_, lean_object* v_b_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
size_t v_sz_boxed_3711_; size_t v_i_boxed_3712_; lean_object* v_res_3713_; 
v_sz_boxed_3711_ = lean_unbox_usize(v_sz_3703_);
lean_dec(v_sz_3703_);
v_i_boxed_3712_ = lean_unbox_usize(v_i_3704_);
lean_dec(v_i_3704_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3700_, v_xs_3701_, v_as_3702_, v_sz_boxed_3711_, v_i_boxed_3712_, v_b_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_as_3702_);
return v_res_3713_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3724_ = l_Lean_stringToMessageData(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
return v___x_3727_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
return v___x_3730_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3733_ = l_Lean_stringToMessageData(v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3734_, lean_object* v_values_3735_, lean_object* v_xs_3736_, lean_object* v_fnNames_3737_, lean_object* v_as_3738_, size_t v_sz_3739_, size_t v_i_3740_, lean_object* v_b_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_a_3748_; uint8_t v___x_3752_; 
v___x_3752_ = lean_usize_dec_lt(v_i_3740_, v_sz_3739_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; 
lean_dec_ref(v_xs_3736_);
lean_dec_ref(v___x_3734_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_b_3741_);
return v___x_3753_;
}
else
{
lean_object* v_fst_3754_; lean_object* v_snd_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3829_; 
v_fst_3754_ = lean_ctor_get(v_b_3741_, 0);
v_snd_3755_ = lean_ctor_get(v_b_3741_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_b_3741_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3757_ = v_b_3741_;
v_isShared_3758_ = v_isSharedCheck_3829_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_snd_3755_);
lean_inc(v_fst_3754_);
lean_dec(v_b_3741_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3829_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3759_; lean_object* v_recArgInfoss_3760_; lean_object* v___x_3761_; lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3759_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3761_ = lean_box(0);
v_a_3762_ = lean_array_uget_borrowed(v_as_3738_, v_i_3740_);
v___x_3763_ = lean_array_get_size(v___x_3734_);
lean_inc_ref(v___x_3734_);
v___x_3764_ = l_Array_toSubarray___redArg(v___x_3734_, v___x_3759_, v___x_3763_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v___x_3764_);
lean_ctor_set(v___x_3757_, 0, v_recArgInfoss_3760_);
v___x_3766_ = v___x_3757_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_recArgInfoss_3760_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
size_t v_sz_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v_sz_3767_ = lean_array_size(v_values_3735_);
v___x_3768_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3736_);
lean_inc(v_a_3762_);
v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3762_, v_xs_3736_, v_values_3735_, v_sz_3767_, v___x_3768_, v___x_3766_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v_fst_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3818_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v_fst_3771_ = lean_ctor_get(v_a_3770_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3770_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_a_3770_, 1);
lean_dec(v_unused_3819_);
v___x_3773_ = v_a_3770_;
v_isShared_3774_ = v_isSharedCheck_3818_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_fst_3771_);
lean_dec(v_a_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3818_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3771_, v___x_3759_);
if (lean_obj_tag(v___x_3775_) == 1)
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_dec(v_fst_3771_);
v_val_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3762_);
v___x_3778_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3762_);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_array_get_borrowed(v___x_3761_, v_fnNames_3737_, v_val_3776_);
lean_dec(v_val_3776_);
lean_inc(v___x_3782_);
v___x_3783_ = l_Lean_MessageData_ofName(v___x_3782_);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3781_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v_fst_3754_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_snd_3755_);
lean_ctor_set(v___x_3773_, 0, v___x_3787_);
v___x_3789_ = v___x_3773_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_snd_3755_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v_a_3748_ = v___x_3789_;
goto v___jp_3747_;
}
}
else
{
lean_object* v___x_3791_; 
lean_dec(v___x_3775_);
v___x_3791_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3771_);
lean_dec(v_fst_3771_);
if (lean_obj_tag(v___x_3791_) == 1)
{
lean_object* v_val_3792_; size_t v_sz_3793_; lean_object* v___x_3794_; 
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v_sz_3793_ = lean_array_size(v_val_3792_);
lean_inc(v_a_3762_);
v___x_3794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3762_, v_val_3792_, v_sz_3793_, v___x_3768_, v_snd_3755_);
lean_dec(v_val_3792_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3797_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_a_3795_);
lean_ctor_set(v___x_3773_, 0, v_fst_3754_);
v___x_3797_ = v___x_3773_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fst_3754_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_a_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
v_a_3748_ = v___x_3797_;
goto v___jp_3747_;
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_del_object(v___x_3773_);
lean_dec(v_fst_3754_);
lean_dec_ref(v_xs_3736_);
lean_dec_ref(v___x_3734_);
v_a_3799_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3794_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3794_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_dec(v___x_3791_);
v___x_3807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3762_);
v___x_3808_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3762_);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_fst_3754_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_snd_3755_);
lean_ctor_set(v___x_3773_, 0, v___x_3814_);
v___x_3816_ = v___x_3773_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_snd_3755_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
v_a_3748_ = v___x_3816_;
goto v___jp_3747_;
}
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_snd_3755_);
lean_dec(v_fst_3754_);
lean_dec_ref(v_xs_3736_);
lean_dec_ref(v___x_3734_);
v_a_3820_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3769_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3769_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
v___jp_3747_:
{
size_t v___x_3749_; size_t v___x_3750_; 
v___x_3749_ = ((size_t)1ULL);
v___x_3750_ = lean_usize_add(v_i_3740_, v___x_3749_);
v_i_3740_ = v___x_3750_;
v_b_3741_ = v_a_3748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3830_, lean_object* v_values_3831_, lean_object* v_xs_3832_, lean_object* v_fnNames_3833_, lean_object* v_as_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_b_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
size_t v_sz_boxed_3843_; size_t v_i_boxed_3844_; lean_object* v_res_3845_; 
v_sz_boxed_3843_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3844_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3830_, v_values_3831_, v_xs_3832_, v_fnNames_3833_, v_as_3834_, v_sz_boxed_3843_, v_i_boxed_3844_, v_b_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v_as_3834_);
lean_dec_ref(v_fnNames_3833_);
lean_dec_ref(v_values_3831_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3846_, lean_object* v___x_3847_, lean_object* v_values_3848_, lean_object* v_fnNames_3849_, lean_object* v_as_3850_, size_t v_sz_3851_, size_t v_i_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_a_3860_; uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3852_, v_sz_3851_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
lean_dec_ref(v___x_3847_);
lean_dec_ref(v_xs_3846_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_b_3853_);
return v___x_3865_;
}
else
{
lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3941_; 
v_fst_3866_ = lean_ctor_get(v_b_3853_, 0);
v_snd_3867_ = lean_ctor_get(v_b_3853_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_b_3853_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3869_ = v_b_3853_;
v_isShared_3870_ = v_isSharedCheck_3941_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_snd_3867_);
lean_inc(v_fst_3866_);
lean_dec(v_b_3853_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3941_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3871_; lean_object* v_recArgInfoss_3872_; lean_object* v___x_3873_; lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3873_ = lean_box(0);
v_a_3874_ = lean_array_uget_borrowed(v_as_3850_, v_i_3852_);
v___x_3875_ = lean_array_get_size(v___x_3847_);
lean_inc_ref(v___x_3847_);
v___x_3876_ = l_Array_toSubarray___redArg(v___x_3847_, v___x_3871_, v___x_3875_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 1, v___x_3876_);
lean_ctor_set(v___x_3869_, 0, v_recArgInfoss_3872_);
v___x_3878_ = v___x_3869_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_recArgInfoss_3872_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
size_t v_sz_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
v_sz_3879_ = lean_array_size(v_values_3848_);
v___x_3880_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3846_);
lean_inc(v_a_3874_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3874_, v_xs_3846_, v_values_3848_, v_sz_3879_, v___x_3880_, v___x_3878_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v_fst_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3930_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v_fst_3883_ = lean_ctor_get(v_a_3882_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3882_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v_a_3882_, 1);
lean_dec(v_unused_3931_);
v___x_3885_ = v_a_3882_;
v_isShared_3886_ = v_isSharedCheck_3930_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_fst_3883_);
lean_dec(v_a_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3930_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3883_, v___x_3871_);
if (lean_obj_tag(v___x_3887_) == 1)
{
lean_object* v_val_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
lean_dec(v_fst_3883_);
v_val_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_val_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3874_);
v___x_3890_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3874_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_array_get_borrowed(v___x_3873_, v_fnNames_3849_, v_val_3888_);
lean_dec(v_val_3888_);
lean_inc(v___x_3894_);
v___x_3895_ = l_Lean_MessageData_ofName(v___x_3894_);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3893_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v_fst_3866_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 1, v_snd_3867_);
lean_ctor_set(v___x_3885_, 0, v___x_3899_);
v___x_3901_ = v___x_3885_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_snd_3867_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
v_a_3860_ = v___x_3901_;
goto v___jp_3859_;
}
}
else
{
lean_object* v___x_3903_; 
lean_dec(v___x_3887_);
v___x_3903_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3883_);
lean_dec(v_fst_3883_);
if (lean_obj_tag(v___x_3903_) == 1)
{
lean_object* v_val_3904_; size_t v_sz_3905_; lean_object* v___x_3906_; 
v_val_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_val_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v_sz_3905_ = lean_array_size(v_val_3904_);
lean_inc(v_a_3874_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3874_, v_val_3904_, v_sz_3905_, v___x_3880_, v_snd_3867_);
lean_dec(v_val_3904_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 1, v_a_3907_);
lean_ctor_set(v___x_3885_, 0, v_fst_3866_);
v___x_3909_ = v___x_3885_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_fst_3866_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_a_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
v_a_3860_ = v___x_3909_;
goto v___jp_3859_;
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_del_object(v___x_3885_);
lean_dec(v_fst_3866_);
lean_dec_ref(v___x_3847_);
lean_dec_ref(v_xs_3846_);
v_a_3911_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3906_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3906_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_dec(v___x_3903_);
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3874_);
v___x_3920_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3874_);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v_fst_3866_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 1, v_snd_3867_);
lean_ctor_set(v___x_3885_, 0, v___x_3926_);
v___x_3928_ = v___x_3885_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_snd_3867_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
v_a_3860_ = v___x_3928_;
goto v___jp_3859_;
}
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_snd_3867_);
lean_dec(v_fst_3866_);
lean_dec_ref(v___x_3847_);
lean_dec_ref(v_xs_3846_);
v_a_3932_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3881_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3881_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3852_, v___x_3861_);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3847_, v_values_3848_, v_xs_3846_, v_fnNames_3849_, v_as_3850_, v_sz_3851_, v___x_3862_, v_a_3860_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3942_, lean_object* v___x_3943_, lean_object* v_values_3944_, lean_object* v_fnNames_3945_, lean_object* v_as_3946_, lean_object* v_sz_3947_, lean_object* v_i_3948_, lean_object* v_b_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
size_t v_sz_boxed_3955_; size_t v_i_boxed_3956_; lean_object* v_res_3957_; 
v_sz_boxed_3955_ = lean_unbox_usize(v_sz_3947_);
lean_dec(v_sz_3947_);
v_i_boxed_3956_ = lean_unbox_usize(v_i_3948_);
lean_dec(v_i_3948_);
v_res_3957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3942_, v___x_3943_, v_values_3944_, v_fnNames_3945_, v_as_3946_, v_sz_boxed_3955_, v_i_boxed_3956_, v_b_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec_ref(v_as_3946_);
lean_dec_ref(v_fnNames_3945_);
lean_dec_ref(v_values_3944_);
return v_res_3957_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__2));
v___x_3964_ = l_Lean_MessageData_ofFormat(v___x_3963_);
return v___x_3964_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__4));
v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__7));
v___x_3972_ = l_Lean_stringToMessageData(v___x_3971_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_box(1);
v___x_3974_ = l_Lean_MessageData_ofFormat(v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3975_, lean_object* v_fixedParamPerms_3976_, lean_object* v_xs_3977_, lean_object* v_values_3978_, lean_object* v_termMeasure_x3fs_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_candidates_3986_; lean_object* v___x_3987_; lean_object* v_perms_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v_report_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; size_t v_sz_3999_; size_t v___x_4000_; lean_object* v___x_4001_; 
v___x_3985_ = lean_unsigned_to_nat(0u);
v_candidates_3986_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__0));
v___x_3987_ = lean_array_get_size(v_values_3978_);
v_perms_3988_ = lean_ctor_get(v_fixedParamPerms_3976_, 1);
lean_inc_ref(v_perms_3988_);
lean_dec_ref(v_fixedParamPerms_3976_);
lean_inc_ref(v_values_3978_);
v___x_3989_ = l_Array_toSubarray___redArg(v_values_3978_, v___x_3985_, v___x_3987_);
v___x_3990_ = lean_array_get_size(v_termMeasure_x3fs_3979_);
v_report_3991_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3992_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3979_, v___x_3985_, v___x_3990_);
v___x_3993_ = lean_array_get_size(v_perms_3988_);
v___x_3994_ = l_Array_toSubarray___redArg(v_perms_3988_, v___x_3985_, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3992_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3989_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v_candidates_3986_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v_report_3991_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v_sz_3999_ = lean_array_size(v_fnNames_3975_);
v___x_4000_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3977_);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3977_, v_fnNames_3975_, v_sz_3999_, v___x_4000_, v___x_3998_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_snd_4003_; lean_object* v_toCold_4004_; lean_object* v_options_4005_; lean_object* v_fst_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4144_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v_snd_4003_ = lean_ctor_get(v_a_4002_, 1);
lean_inc(v_snd_4003_);
v_toCold_4004_ = lean_ctor_get(v_a_3982_, 0);
v_options_4005_ = lean_ctor_get(v_toCold_4004_, 2);
v_fst_4006_ = lean_ctor_get(v_a_4002_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_a_4002_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_a_4002_, 1);
lean_dec(v_unused_4145_);
v___x_4008_ = v_a_4002_;
v_isShared_4009_ = v_isSharedCheck_4144_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_fst_4006_);
lean_dec(v_a_4002_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4144_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_fst_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4142_; 
v_fst_4010_ = lean_ctor_get(v_snd_4003_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_snd_4003_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; 
v_unused_4143_ = lean_ctor_get(v_snd_4003_, 1);
lean_dec(v_unused_4143_);
v___x_4012_ = v_snd_4003_;
v_isShared_4013_ = v_isSharedCheck_4142_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_fst_4010_);
lean_dec(v_snd_4003_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4142_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_inheritedTraceOptions_4014_; uint8_t v_hasTrace_4015_; size_t v_sz_4016_; lean_object* v___x_4017_; lean_object* v___y_4019_; lean_object* v_report_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___x_4067_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; 
v_inheritedTraceOptions_4014_ = lean_ctor_get(v_toCold_4004_, 11);
v_hasTrace_4015_ = lean_ctor_get_uint8(v_options_4005_, sizeof(void*)*1);
v_sz_4016_ = lean_array_size(v_fst_4010_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4016_, v___x_4000_, v_fst_4010_);
v___x_4067_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4015_ == 0)
{
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
v___y_4109_ = v_a_3982_;
v___y_4110_ = v_a_3983_;
goto v___jp_4106_;
}
else
{
lean_object* v___x_4116_; uint8_t v___x_4117_; 
v___x_4116_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4014_, v_options_4005_, v___x_4116_);
if (v___x_4117_ == 0)
{
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
v___y_4109_ = v_a_3982_;
v___y_4110_ = v_a_3983_;
goto v___jp_4106_;
}
else
{
lean_object* v___x_4118_; lean_object* v___y_4120_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4137_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4138_ = lean_array_get_size(v___x_4017_);
v___x_4139_ = lean_nat_dec_lt(v___x_3985_, v___x_4138_);
if (v___x_4139_ == 0)
{
v___y_4120_ = v___x_4137_;
goto v___jp_4119_;
}
else
{
size_t v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_usize_of_nat(v___x_4138_);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4017_, v___x_4000_, v___x_4140_, v___x_4137_);
v___y_4120_ = v___x_4141_;
goto v___jp_4119_;
}
v___jp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4121_ = lean_array_to_list(v___y_4120_);
v___x_4122_ = lean_box(0);
v___x_4123_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4121_, v___x_4122_);
v___x_4124_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__9, &l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9);
v___x_4125_ = l_Lean_MessageData_joinSep(v___x_4123_, v___x_4124_);
v___x_4126_ = l_Lean_indentD(v___x_4125_);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4118_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4067_, v___x_4127_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_dec_ref_known(v___x_4128_, 1);
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
v___y_4109_ = v_a_3982_;
v___y_4110_ = v_a_3983_;
goto v___jp_4106_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___x_4017_);
lean_del_object(v___x_4012_);
lean_del_object(v___x_4008_);
lean_dec(v_fst_4006_);
lean_dec_ref(v_values_3978_);
lean_dec_ref(v_xs_3977_);
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
}
v___jp_4018_:
{
lean_object* v___x_4026_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 1, v_candidates_3986_);
lean_ctor_set(v___x_4012_, 0, v_report_4020_);
v___x_4026_ = v___x_4012_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_report_4020_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_candidates_3986_);
v___x_4026_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
size_t v_sz_4027_; lean_object* v___x_4028_; 
v_sz_4027_ = lean_array_size(v___y_4019_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3977_, v___x_4017_, v_values_3978_, v_fnNames_3975_, v___y_4019_, v_sz_4027_, v___x_4000_, v___x_4026_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec_ref(v___y_4019_);
lean_dec_ref(v_values_3978_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4045_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4045_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4045_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v_fst_4033_; lean_object* v_snd_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4044_; 
v_fst_4033_ = lean_ctor_get(v_a_4029_, 0);
v_snd_4034_ = lean_ctor_get(v_a_4029_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4036_ = v_a_4029_;
v_isShared_4037_ = v_isSharedCheck_4044_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_snd_4034_);
lean_inc(v_fst_4033_);
lean_dec(v_a_4029_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4044_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v_fst_4033_);
lean_ctor_set(v___x_4036_, 0, v_snd_4034_);
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_snd_4034_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_fst_4033_);
v___x_4039_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4041_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4039_);
v___x_4041_ = v___x_4031_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
v_a_4046_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4028_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4028_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
v___jp_4055_:
{
lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4061_ = lean_array_get_size(v___y_4056_);
v___x_4062_ = lean_nat_dec_eq(v___x_4061_, v___x_3985_);
if (v___x_4062_ == 0)
{
lean_del_object(v___x_4008_);
v___y_4019_ = v___y_4056_;
v_report_4020_ = v_fst_4006_;
v___y_4021_ = v___y_4057_;
v___y_4022_ = v___y_4058_;
v___y_4023_ = v___y_4059_;
v___y_4024_ = v___y_4060_;
goto v___jp_4018_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4063_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__3, &l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3);
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 7);
lean_ctor_set(v___x_4008_, 1, v___x_4063_);
v___x_4065_ = v___x_4008_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_fst_4006_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
v___y_4019_ = v___y_4056_;
v_report_4020_ = v___x_4065_;
v___y_4021_ = v___y_4057_;
v___y_4022_ = v___y_4058_;
v___y_4023_ = v___y_4059_;
v___y_4024_ = v___y_4060_;
goto v___jp_4018_;
}
}
}
v___jp_4068_:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4073_, v___y_4071_, v___y_4069_, v___y_4072_, v___y_4070_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_toCold_4075_; lean_object* v_options_4076_; uint8_t v_hasTrace_4077_; 
v_toCold_4075_ = lean_ctor_get(v___y_4072_, 0);
v_options_4076_ = lean_ctor_get(v_toCold_4075_, 2);
v_hasTrace_4077_ = lean_ctor_get_uint8(v_options_4076_, sizeof(void*)*1);
if (v_hasTrace_4077_ == 0)
{
lean_object* v_a_4078_; 
v_a_4078_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4074_, 1);
v___y_4056_ = v_a_4078_;
v___y_4057_ = v___y_4071_;
v___y_4058_ = v___y_4069_;
v___y_4059_ = v___y_4072_;
v___y_4060_ = v___y_4070_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4079_; lean_object* v_inheritedTraceOptions_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_a_4079_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4074_, 1);
v_inheritedTraceOptions_4080_ = lean_ctor_get(v_toCold_4075_, 11);
v___x_4081_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4080_, v_options_4076_, v___x_4081_);
if (v___x_4082_ == 0)
{
v___y_4056_ = v_a_4079_;
v___y_4057_ = v___y_4071_;
v___y_4058_ = v___y_4069_;
v___y_4059_ = v___y_4072_;
v___y_4060_ = v___y_4070_;
goto v___jp_4055_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4083_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__5, &l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5);
lean_inc(v_a_4079_);
v___x_4084_ = lean_array_to_list(v_a_4079_);
v___x_4085_ = lean_box(0);
v___x_4086_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4084_, v___x_4085_);
v___x_4087_ = l_Lean_MessageData_ofList(v___x_4086_);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4083_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4067_, v___x_4088_, v___y_4071_, v___y_4069_, v___y_4072_, v___y_4070_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_dec_ref_known(v___x_4089_, 1);
v___y_4056_ = v_a_4079_;
v___y_4057_ = v___y_4071_;
v___y_4058_ = v___y_4069_;
v___y_4059_ = v___y_4072_;
v___y_4060_ = v___y_4070_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4079_);
lean_dec_ref(v___x_4017_);
lean_del_object(v___x_4012_);
lean_del_object(v___x_4008_);
lean_dec(v_fst_4006_);
lean_dec_ref(v_values_3978_);
lean_dec_ref(v_xs_3977_);
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec_ref(v___x_4017_);
lean_del_object(v___x_4012_);
lean_del_object(v___x_4008_);
lean_dec(v_fst_4006_);
lean_dec_ref(v_values_3978_);
lean_dec_ref(v_xs_3977_);
v_a_4098_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4074_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4074_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
v___jp_4106_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4111_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4112_ = lean_array_get_size(v___x_4017_);
v___x_4113_ = lean_nat_dec_lt(v___x_3985_, v___x_4112_);
if (v___x_4113_ == 0)
{
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4110_;
v___y_4071_ = v___y_4107_;
v___y_4072_ = v___y_4109_;
v___y_4073_ = v___x_4111_;
goto v___jp_4068_;
}
else
{
size_t v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_usize_of_nat(v___x_4112_);
v___x_4115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4017_, v___x_4000_, v___x_4114_, v___x_4111_);
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4110_;
v___y_4071_ = v___y_4107_;
v___y_4072_ = v___y_4109_;
v___y_4073_ = v___x_4115_;
goto v___jp_4068_;
}
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v_values_3978_);
lean_dec_ref(v_xs_3977_);
v_a_4146_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4001_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4001_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4154_, lean_object* v_fixedParamPerms_4155_, lean_object* v_xs_4156_, lean_object* v_values_4157_, lean_object* v_termMeasure_x3fs_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4154_, v_fixedParamPerms_4155_, v_xs_4156_, v_values_4157_, v_termMeasure_x3fs_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec_ref(v_fnNames_4154_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4165_, lean_object* v_as_4166_, size_t v_sz_4167_, size_t v_i_4168_, lean_object* v_b_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4165_, v_as_4166_, v_sz_4167_, v_i_4168_, v_b_4169_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4176_, lean_object* v_as_4177_, lean_object* v_sz_4178_, lean_object* v_i_4179_, lean_object* v_b_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
size_t v_sz_boxed_4186_; size_t v_i_boxed_4187_; lean_object* v_res_4188_; 
v_sz_boxed_4186_ = lean_unbox_usize(v_sz_4178_);
lean_dec(v_sz_4178_);
v_i_boxed_4187_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4176_, v_as_4177_, v_sz_boxed_4186_, v_i_boxed_4187_, v_b_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec_ref(v_as_4177_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4189_, uint8_t v_skipRealize_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v_env_4194_; uint8_t v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4193_ = lean_st_ref_get(v___y_4191_);
v_env_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc_ref(v_env_4194_);
lean_dec(v___x_4193_);
v___x_4195_ = l_Lean_Environment_contains(v_env_4194_, v_constName_4189_, v_skipRealize_4190_);
v___x_4196_ = lean_box(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4198_, lean_object* v_skipRealize_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
uint8_t v_skipRealize_boxed_4202_; lean_object* v_res_4203_; 
v_skipRealize_boxed_4202_ = lean_unbox(v_skipRealize_4199_);
v_res_4203_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4198_, v_skipRealize_boxed_4202_, v___y_4200_);
lean_dec(v___y_4200_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4204_, uint8_t v_skipRealize_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4204_, v_skipRealize_4205_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4212_, lean_object* v_skipRealize_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
uint8_t v_skipRealize_boxed_4219_; lean_object* v_res_4220_; 
v_skipRealize_boxed_4219_ = lean_unbox(v_skipRealize_4213_);
v_res_4220_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4212_, v_skipRealize_boxed_4219_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_Meta_saveState___redArg(v___y_4223_, v___y_4225_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
lean_inc(v___y_4225_);
lean_inc_ref(v___y_4224_);
lean_inc(v___y_4223_);
lean_inc_ref(v___y_4222_);
v___x_4229_ = lean_apply_5(v_x_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, lean_box(0));
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_dec(v_a_4228_);
return v___x_4229_;
}
else
{
lean_object* v_a_4230_; uint8_t v___y_4232_; uint8_t v___x_4250_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
v___x_4250_ = l_Lean_Exception_isInterrupt(v_a_4230_);
if (v___x_4250_ == 0)
{
uint8_t v___x_4251_; 
lean_inc(v_a_4230_);
v___x_4251_ = l_Lean_Exception_isRuntime(v_a_4230_);
v___y_4232_ = v___x_4251_;
goto v___jp_4231_;
}
else
{
v___y_4232_ = v___x_4250_;
goto v___jp_4231_;
}
v___jp_4231_:
{
if (v___y_4232_ == 0)
{
lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4229_, 1);
v___x_4233_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4228_, v___y_4223_, v___y_4225_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; 
v_unused_4241_ = lean_ctor_get(v___x_4233_, 0);
lean_dec(v_unused_4241_);
v___x_4235_ = v___x_4233_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_dec(v___x_4233_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
lean_ctor_set_tag(v___x_4235_, 1);
lean_ctor_set(v___x_4235_, 0, v_a_4230_);
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4230_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec(v_a_4230_);
v_a_4242_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4233_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4233_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec_ref(v_x_4221_);
v_a_4252_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4227_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4227_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4275_, lean_object* v_x_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4275_, v_x_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4285_ = l_Lean_stringToMessageData(v___x_4284_);
return v___x_4285_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4288_ = l_Lean_stringToMessageData(v___x_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4289_, uint8_t v___x_4290_, lean_object* v_group_4291_, lean_object* v_k_4292_, lean_object* v_comb_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4289_, v___x_4290_, v___y_4297_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; uint8_t v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = lean_unbox(v_a_4300_);
lean_dec(v_a_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4303_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4291_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4306_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v___x_4308_; 
lean_dec_ref_known(v___x_4307_, 1);
v___x_4308_ = lean_apply_6(v_k_4292_, v_comb_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, lean_box(0));
return v___x_4308_;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec_ref(v_comb_4293_);
lean_dec_ref(v_k_4292_);
v_a_4309_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4307_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4307_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v___x_4317_; 
lean_dec_ref(v_group_4291_);
v___x_4317_ = lean_apply_6(v_k_4292_, v_comb_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, lean_box(0));
return v___x_4317_;
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec_ref(v_comb_4293_);
lean_dec_ref(v_k_4292_);
lean_dec_ref(v_group_4291_);
v_a_4318_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4299_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4299_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4326_, lean_object* v___x_4327_, lean_object* v_group_4328_, lean_object* v_k_4329_, lean_object* v_comb_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
uint8_t v___x_4328__boxed_4336_; lean_object* v_res_4337_; 
v___x_4328__boxed_4336_ = lean_unbox(v___x_4327_);
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4326_, v___x_4328__boxed_4336_, v_group_4328_, v_k_4329_, v_comb_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v_res_4337_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4340_ = l_Lean_stringToMessageData(v___x_4339_);
return v___x_4340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4343_, lean_object* v_fnNames_4344_, lean_object* v_xs_4345_, lean_object* v_values_4346_, lean_object* v_as_4347_, size_t v_sz_4348_, size_t v_i_4349_, lean_object* v_b_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = lean_usize_dec_lt(v_i_4349_, v_sz_4348_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4357_; 
lean_dec_ref(v_values_4346_);
lean_dec_ref(v_xs_4345_);
lean_dec_ref(v_k_4343_);
v___x_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4357_, 0, v_b_4350_);
return v___x_4357_;
}
else
{
lean_object* v_snd_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4428_; 
v_snd_4358_ = lean_ctor_get(v_b_4350_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_b_4350_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; 
v_unused_4429_ = lean_ctor_get(v_b_4350_, 0);
lean_dec(v_unused_4429_);
v___x_4360_ = v_b_4350_;
v_isShared_4361_ = v_isSharedCheck_4428_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_snd_4358_);
lean_dec(v_b_4350_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4428_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_a_4362_; lean_object* v_group_4363_; lean_object* v_comb_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4427_; 
v_a_4362_ = lean_array_uget(v_as_4347_, v_i_4349_);
v_group_4363_ = lean_ctor_get(v_a_4362_, 0);
v_comb_4364_ = lean_ctor_get(v_a_4362_, 1);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_a_4362_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4366_ = v_a_4362_;
v_isShared_4367_ = v_isSharedCheck_4427_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_comb_4364_);
lean_inc(v_group_4363_);
lean_dec(v_a_4362_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4427_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v_toIndGroupInfo_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___f_4373_; lean_object* v___x_4374_; 
v_toIndGroupInfo_4368_ = lean_ctor_get(v_group_4363_, 0);
v___x_4369_ = lean_box(0);
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4368_, v___x_4370_);
v___x_4372_ = lean_box(v___x_4356_);
lean_inc_ref(v_comb_4364_);
lean_inc_ref(v_k_4343_);
v___f_4373_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4373_, 0, v___x_4371_);
lean_closure_set(v___f_4373_, 1, v___x_4372_);
lean_closure_set(v___f_4373_, 2, v_group_4363_);
lean_closure_set(v___f_4373_, 3, v_k_4343_);
lean_closure_set(v___f_4373_, 4, v_comb_4364_);
v___x_4374_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4373_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4386_; 
lean_del_object(v___x_4366_);
lean_dec_ref(v_comb_4364_);
lean_dec_ref(v_values_4346_);
lean_dec_ref(v_xs_4345_);
lean_dec_ref(v_k_4343_);
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4386_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4386_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v_a_4375_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4379_);
v___x_4381_ = v___x_4360_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_snd_4358_);
v___x_4381_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
lean_object* v___x_4383_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 0, v___x_4381_);
v___x_4383_ = v___x_4377_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4426_; 
v_a_4387_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4389_ = v___x_4374_;
v_isShared_4390_ = v_isSharedCheck_4426_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4374_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4426_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
uint8_t v___y_4392_; uint8_t v___x_4424_; 
v___x_4424_ = l_Lean_Exception_isInterrupt(v_a_4387_);
if (v___x_4424_ == 0)
{
uint8_t v___x_4425_; 
lean_inc(v_a_4387_);
v___x_4425_ = l_Lean_Exception_isRuntime(v_a_4387_);
v___y_4392_ = v___x_4425_;
goto v___jp_4391_;
}
else
{
v___y_4392_ = v___x_4424_;
goto v___jp_4391_;
}
v___jp_4391_:
{
if (v___y_4392_ == 0)
{
lean_object* v___x_4393_; 
lean_del_object(v___x_4389_);
lean_inc_ref(v_values_4346_);
lean_inc_ref(v_xs_4345_);
v___x_4393_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4344_, v_xs_4345_, v_values_4346_, v_comb_4364_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 7);
lean_ctor_set(v___x_4366_, 1, v_a_4394_);
lean_ctor_set(v___x_4366_, 0, v___x_4395_);
v___x_4397_ = v___x_4366_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_a_4394_);
v___x_4397_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4398_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = l_Lean_Exception_toMessageData(v_a_4387_);
v___x_4401_ = l_Lean_indentD(v___x_4400_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4399_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4405_, 0, v_snd_4358_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 1, v___x_4405_);
lean_ctor_set(v___x_4360_, 0, v___x_4369_);
v___x_4407_ = v___x_4360_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4369_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
size_t v___x_4408_; size_t v___x_4409_; 
v___x_4408_ = ((size_t)1ULL);
v___x_4409_ = lean_usize_add(v_i_4349_, v___x_4408_);
v_i_4349_ = v___x_4409_;
v_b_4350_ = v___x_4407_;
goto _start;
}
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_a_4387_);
lean_del_object(v___x_4366_);
lean_del_object(v___x_4360_);
lean_dec(v_snd_4358_);
lean_dec_ref(v_values_4346_);
lean_dec_ref(v_xs_4345_);
lean_dec_ref(v_k_4343_);
v_a_4413_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4393_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4393_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v___x_4422_; 
lean_del_object(v___x_4366_);
lean_dec_ref(v_comb_4364_);
lean_del_object(v___x_4360_);
lean_dec(v_snd_4358_);
lean_dec_ref(v_values_4346_);
lean_dec_ref(v_xs_4345_);
lean_dec_ref(v_k_4343_);
if (v_isShared_4390_ == 0)
{
v___x_4422_ = v___x_4389_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4387_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4430_, lean_object* v_fnNames_4431_, lean_object* v_xs_4432_, lean_object* v_values_4433_, lean_object* v_as_4434_, lean_object* v_sz_4435_, lean_object* v_i_4436_, lean_object* v_b_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
size_t v_sz_boxed_4443_; size_t v_i_boxed_4444_; lean_object* v_res_4445_; 
v_sz_boxed_4443_ = lean_unbox_usize(v_sz_4435_);
lean_dec(v_sz_4435_);
v_i_boxed_4444_ = lean_unbox_usize(v_i_4436_);
lean_dec(v_i_4436_);
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4430_, v_fnNames_4431_, v_xs_4432_, v_values_4433_, v_as_4434_, v_sz_boxed_4443_, v_i_boxed_4444_, v_b_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v_as_4434_);
lean_dec_ref(v_fnNames_4431_);
return v_res_4445_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4447_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4448_ = l_Lean_stringToMessageData(v___x_4447_);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4451_ = l_Lean_stringToMessageData(v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4452_, lean_object* v_xs_4453_, lean_object* v_values_4454_, lean_object* v_candidates_4455_, lean_object* v_k_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_candidates_4462_; lean_object* v_report_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4523_; 
v_candidates_4462_ = lean_ctor_get(v_candidates_4455_, 0);
v_report_4463_ = lean_ctor_get(v_candidates_4455_, 1);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_candidates_4455_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4465_ = v_candidates_4455_;
v_isShared_4466_ = v_isSharedCheck_4523_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_report_4463_);
lean_inc(v_candidates_4462_);
lean_dec(v_candidates_4455_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4523_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_box(0);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4467_);
v___x_4469_ = v___x_4465_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_report_4463_);
v___x_4469_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
size_t v_sz_4470_; size_t v___x_4471_; lean_object* v___x_4472_; 
v_sz_4470_ = lean_array_size(v_candidates_4462_);
v___x_4471_ = ((size_t)0ULL);
v___x_4472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4456_, v_fnNames_4452_, v_xs_4453_, v_values_4454_, v_candidates_4462_, v_sz_4470_, v___x_4471_, v___x_4469_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec_ref(v_candidates_4462_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4513_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4513_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4513_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_fst_4477_; 
v_fst_4477_ = lean_ctor_get(v_a_4473_, 0);
if (lean_obj_tag(v_fst_4477_) == 0)
{
lean_object* v_toCold_4478_; lean_object* v_options_4479_; lean_object* v_snd_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4507_; 
lean_del_object(v___x_4475_);
v_toCold_4478_ = lean_ctor_get(v_a_4459_, 0);
v_options_4479_ = lean_ctor_get(v_toCold_4478_, 2);
v_snd_4480_ = lean_ctor_get(v_a_4473_, 1);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_a_4473_);
if (v_isSharedCheck_4507_ == 0)
{
lean_object* v_unused_4508_; 
v_unused_4508_ = lean_ctor_get(v_a_4473_, 0);
lean_dec(v_unused_4508_);
v___x_4482_ = v_a_4473_;
v_isShared_4483_ = v_isSharedCheck_4507_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_snd_4480_);
lean_dec(v_a_4473_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4507_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v_inheritedTraceOptions_4484_; uint8_t v_hasTrace_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
v_inheritedTraceOptions_4484_ = lean_ctor_get(v_toCold_4478_, 11);
v_hasTrace_4485_ = lean_ctor_get_uint8(v_options_4479_, sizeof(void*)*1);
v___x_4486_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4483_ == 0)
{
lean_ctor_set_tag(v___x_4482_, 7);
lean_ctor_set(v___x_4482_, 0, v___x_4486_);
v___x_4488_ = v___x_4482_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_snd_4480_);
v___x_4488_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
if (v_hasTrace_4485_ == 0)
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4488_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
return v___x_4489_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4490_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4491_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4484_, v_options_4479_, v___x_4491_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4488_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4488_);
v___x_4495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
lean_ctor_set(v___x_4495_, 1, v___x_4488_);
v___x_4496_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4490_, v___x_4495_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v___x_4497_; 
lean_dec_ref_known(v___x_4496_, 1);
v___x_4497_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4488_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
return v___x_4497_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v___x_4488_);
v_a_4498_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4496_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4496_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
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
lean_object* v_val_4509_; lean_object* v___x_4511_; 
lean_inc_ref(v_fst_4477_);
lean_dec(v_a_4473_);
v_val_4509_ = lean_ctor_get(v_fst_4477_, 0);
lean_inc(v_val_4509_);
lean_dec_ref_known(v_fst_4477_, 1);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v_val_4509_);
v___x_4511_ = v___x_4475_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_val_4509_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_a_4514_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4472_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4472_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4524_, lean_object* v_xs_4525_, lean_object* v_values_4526_, lean_object* v_candidates_4527_, lean_object* v_k_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4524_, v_xs_4525_, v_values_4526_, v_candidates_4527_, v_k_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec_ref(v_fnNames_4524_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4535_, lean_object* v_fnNames_4536_, lean_object* v_xs_4537_, lean_object* v_values_4538_, lean_object* v_candidates_4539_, lean_object* v_k_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4536_, v_xs_4537_, v_values_4538_, v_candidates_4539_, v_k_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4547_, lean_object* v_fnNames_4548_, lean_object* v_xs_4549_, lean_object* v_values_4550_, lean_object* v_candidates_4551_, lean_object* v_k_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4547_, v_fnNames_4548_, v_xs_4549_, v_values_4550_, v_candidates_4551_, v_k_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec_ref(v_fnNames_4548_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4559_, lean_object* v_k_4560_, lean_object* v_fnNames_4561_, lean_object* v_xs_4562_, lean_object* v_values_4563_, lean_object* v_as_4564_, size_t v_sz_4565_, size_t v_i_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4560_, v_fnNames_4561_, v_xs_4562_, v_values_4563_, v_as_4564_, v_sz_4565_, v_i_4566_, v_b_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4574_, lean_object* v_k_4575_, lean_object* v_fnNames_4576_, lean_object* v_xs_4577_, lean_object* v_values_4578_, lean_object* v_as_4579_, lean_object* v_sz_4580_, lean_object* v_i_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
size_t v_sz_boxed_4588_; size_t v_i_boxed_4589_; lean_object* v_res_4590_; 
v_sz_boxed_4588_ = lean_unbox_usize(v_sz_4580_);
lean_dec(v_sz_4580_);
v_i_boxed_4589_ = lean_unbox_usize(v_i_4581_);
lean_dec(v_i_4581_);
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4574_, v_k_4575_, v_fnNames_4576_, v_xs_4577_, v_values_4578_, v_as_4579_, v_sz_boxed_4588_, v_i_boxed_4589_, v_b_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec_ref(v_as_4579_);
lean_dec_ref(v_fnNames_4576_);
return v_res_4590_;
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
