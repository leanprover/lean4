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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
size_t v___x_561_; size_t v___x_562_; uint8_t v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_559_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_557_, v_as_556_, v___x_561_, v___x_562_);
return v___x_563_;
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
v___x_1229_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1219_);
if (v___x_1229_ == 0)
{
lean_object* v_name_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1230_ = lean_ctor_get(v___y_1227_, 0);
lean_inc(v_name_1230_);
lean_dec_ref(v___y_1227_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1232_ = l_Lean_MessageData_ofName(v_name_1230_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_indentExpr(v___y_1224_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1237_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1202_, v_xs_1203_);
v___x_1240_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1239_, v___y_1219_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
if (lean_obj_tag(v_a_1241_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1239_, v___y_1228_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
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
lean_dec_ref(v___y_1224_);
v_name_1247_ = lean_ctor_get(v___y_1227_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1227_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; 
v_unused_1268_ = lean_ctor_get(v___y_1227_, 2);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v___y_1227_, 1);
lean_dec(v_unused_1269_);
v___x_1249_ = v___y_1227_;
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_name_1247_);
lean_dec(v___y_1227_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_array_mk(v___y_1225_);
v___x_1252_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1251_, v_name_1247_);
lean_dec(v_name_1247_);
lean_dec_ref(v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; size_t v_sz_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_sz_1254_ = lean_array_size(v___y_1219_);
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1203_, v_sz_1254_, v___x_1255_, v___y_1219_);
v___x_1257_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1222_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 2, v___y_1228_);
lean_ctor_set(v___x_1249_, 1, v___y_1220_);
lean_ctor_set(v___x_1249_, 0, v___x_1257_);
v___x_1259_ = v___x_1249_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___y_1220_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___y_1228_);
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
lean_dec_ref(v___y_1228_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1266_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1265_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_val_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
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
v___x_1277_ = l_Lean_indentExpr(v___y_1224_);
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
v___x_1290_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1289_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
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
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
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
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
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
v_name_1308_ = lean_ctor_get(v___y_1227_, 0);
lean_inc(v_name_1308_);
lean_dec_ref(v___y_1227_);
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
v___x_1315_ = l_Lean_indentExpr(v___y_1224_);
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
v___x_1325_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1324_, v___y_1221_, v___y_1226_, v___y_1223_, v___y_1218_);
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
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
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
v___x_1353_ = l_Array_toSubarray___redArg(v___y_1348_, v_lower_1351_, v_upper_1352_);
v___x_1354_ = l_Subarray_copy___redArg(v___x_1353_);
v___x_1355_ = lean_array_get_size(v___x_1354_);
v___x_1356_ = lean_nat_dec_lt(v___y_1350_, v___x_1355_);
lean_dec(v___y_1350_);
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___x_1354_;
v___y_1220_ = v___y_1340_;
v___y_1221_ = v___y_1341_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___y_1346_;
v___y_1224_ = v___y_1343_;
v___y_1225_ = v___y_1344_;
v___y_1226_ = v___y_1347_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1349_;
goto v___jp_1217_;
}
else
{
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___x_1354_;
v___y_1220_ = v___y_1340_;
v___y_1221_ = v___y_1341_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___y_1346_;
v___y_1224_ = v___y_1343_;
v___y_1225_ = v___y_1344_;
v___y_1226_ = v___y_1347_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1349_;
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
v___y_1219_ = v___x_1354_;
v___y_1220_ = v___y_1340_;
v___y_1221_ = v___y_1341_;
v___y_1222_ = v___y_1342_;
v___y_1223_ = v___y_1346_;
v___y_1224_ = v___y_1343_;
v___y_1225_ = v___y_1344_;
v___y_1226_ = v___y_1347_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1349_;
goto v___jp_1217_;
}
else
{
lean_object* v_name_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1340_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1360_ = lean_ctor_get(v___y_1345_, 0);
lean_inc(v_name_1360_);
lean_dec_ref(v___y_1345_);
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1362_ = l_Lean_MessageData_ofName(v_name_1360_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_indentExpr(v___y_1343_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1367_, v___y_1341_, v___y_1347_, v___y_1346_, v___y_1339_);
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
v___y_1339_ = v___y_1374_;
v___y_1340_ = v_us_1380_;
v___y_1341_ = v___y_1371_;
v___y_1342_ = v_val_1386_;
v___y_1343_ = v_a_1377_;
v___y_1344_ = v_all_1389_;
v___y_1345_ = v_toConstantVal_1387_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___x_1395_;
v___y_1349_ = v___x_1398_;
v___y_1350_ = v___x_1396_;
v_lower_1351_ = v_numParams_1388_;
v_upper_1352_ = v___x_1399_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v___y_1374_;
v___y_1340_ = v_us_1380_;
v___y_1341_ = v___y_1371_;
v___y_1342_ = v_val_1386_;
v___y_1343_ = v_a_1377_;
v___y_1344_ = v_all_1389_;
v___y_1345_ = v_toConstantVal_1387_;
v___y_1346_ = v___y_1373_;
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___x_1395_;
v___y_1349_ = v___x_1398_;
v___y_1350_ = v___x_1396_;
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
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1617_; 
v_fst_1570_ = lean_ctor_get(v_b_1555_, 0);
v_snd_1571_ = lean_ctor_get(v_b_1555_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_b_1555_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1573_ = v_b_1555_;
v_isShared_1574_ = v_isSharedCheck_1617_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_b_1555_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1617_;
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
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1616_; 
v_a_1578_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1580_ = v___x_1575_;
v_isShared_1581_ = v_isSharedCheck_1616_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1616_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_Exception_isInterrupt(v_a_1578_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; 
lean_inc(v_a_1578_);
v___x_1583_ = l_Lean_Exception_isRuntime(v_a_1578_);
if (v___x_1583_ == 0)
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
else
{
lean_object* v___x_1614_; 
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec(v_a_1554_);
lean_dec_ref(v_fixedParamPerm_1552_);
lean_dec(v_fnName_1551_);
if (v_isShared_1581_ == 0)
{
v___x_1614_ = v___x_1580_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1578_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1618_, lean_object* v_fnName_1619_, lean_object* v_fixedParamPerm_1620_, lean_object* v_args_1621_, lean_object* v_a_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1618_, v_fnName_1619_, v_fixedParamPerm_1620_, v_args_1621_, v_a_1622_, v_b_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v_args_1621_);
lean_dec(v_upperBound_1618_);
return v_res_1629_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1630_; double v___x_1631_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_float_of_nat(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1633_, lean_object* v_msg_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_ref_1640_; lean_object* v___x_1641_; lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1687_; 
v_ref_1640_ = lean_ctor_get(v___y_1637_, 2);
v___x_1641_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1687_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1687_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v_traceState_1647_; lean_object* v_env_1648_; lean_object* v_nextMacroScope_1649_; lean_object* v_ngen_1650_; lean_object* v_auxDeclNGen_1651_; lean_object* v_cache_1652_; lean_object* v_recordedDeps_1653_; lean_object* v_messages_1654_; lean_object* v_infoState_1655_; lean_object* v_snapshotTasks_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1686_; 
v___x_1646_ = lean_st_ref_take(v___y_1638_);
v_traceState_1647_ = lean_ctor_get(v___x_1646_, 4);
v_env_1648_ = lean_ctor_get(v___x_1646_, 0);
v_nextMacroScope_1649_ = lean_ctor_get(v___x_1646_, 1);
v_ngen_1650_ = lean_ctor_get(v___x_1646_, 2);
v_auxDeclNGen_1651_ = lean_ctor_get(v___x_1646_, 3);
v_cache_1652_ = lean_ctor_get(v___x_1646_, 5);
v_recordedDeps_1653_ = lean_ctor_get(v___x_1646_, 6);
v_messages_1654_ = lean_ctor_get(v___x_1646_, 7);
v_infoState_1655_ = lean_ctor_get(v___x_1646_, 8);
v_snapshotTasks_1656_ = lean_ctor_get(v___x_1646_, 9);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1658_ = v___x_1646_;
v_isShared_1659_ = v_isSharedCheck_1686_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_snapshotTasks_1656_);
lean_inc(v_infoState_1655_);
lean_inc(v_messages_1654_);
lean_inc(v_recordedDeps_1653_);
lean_inc(v_cache_1652_);
lean_inc(v_traceState_1647_);
lean_inc(v_auxDeclNGen_1651_);
lean_inc(v_ngen_1650_);
lean_inc(v_nextMacroScope_1649_);
lean_inc(v_env_1648_);
lean_dec(v___x_1646_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1686_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
uint64_t v_tid_1660_; lean_object* v_traces_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1685_; 
v_tid_1660_ = lean_ctor_get_uint64(v_traceState_1647_, sizeof(void*)*1);
v_traces_1661_ = lean_ctor_get(v_traceState_1647_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_traceState_1647_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1663_ = v_traceState_1647_;
v_isShared_1664_ = v_isSharedCheck_1685_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_traces_1661_);
lean_dec(v_traceState_1647_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1685_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; double v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1668_ = 0;
v___x_1669_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1670_, 0, v_cls_1633_);
lean_ctor_set(v___x_1670_, 1, v___x_1666_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3, v___x_1667_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3 + 8, v___x_1667_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 16, v___x_1668_);
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1672_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v_a_1642_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_inc(v_ref_1640_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_ref_1640_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_PersistentArray_push___redArg(v_traces_1661_, v___x_1673_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1674_);
v___x_1676_ = v___x_1663_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1674_);
lean_ctor_set_uint64(v_reuseFailAlloc_1684_, sizeof(void*)*1, v_tid_1660_);
v___x_1676_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v___x_1676_);
v___x_1678_ = v___x_1658_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_env_1648_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_nextMacroScope_1649_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_ngen_1650_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_auxDeclNGen_1651_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1683_, 5, v_cache_1652_);
lean_ctor_set(v_reuseFailAlloc_1683_, 6, v_recordedDeps_1653_);
lean_ctor_set(v_reuseFailAlloc_1683_, 7, v_messages_1654_);
lean_ctor_set(v_reuseFailAlloc_1683_, 8, v_infoState_1655_);
lean_ctor_set(v_reuseFailAlloc_1683_, 9, v_snapshotTasks_1656_);
v___x_1678_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_st_ref_put(v___y_1638_, v___x_1678_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1665_);
v___x_1681_ = v___x_1644_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1665_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1688_, lean_object* v_msg_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1688_, v_msg_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___f_1700_; 
v___x_1699_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1700_, 0, v___x_1699_);
return v___f_1700_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1705_; lean_object* v_recArgInfos_1706_; lean_object* v___x_1707_; 
v_report_1705_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1706_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_recArgInfos_1706_);
lean_ctor_set(v___x_1707_, 1, v_report_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1719_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1720_ = l_Lean_Name_append(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1724_, lean_object* v_fixedParamPerm_1725_, lean_object* v_xs_1726_, lean_object* v_fnName_1727_, lean_object* v_ys_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1724_) == 1)
{
lean_object* v_val_1735_; lean_object* v_ref_1736_; lean_object* v_toCold_1737_; lean_object* v_currRecDepth_1738_; lean_object* v_ref_1739_; uint16_t v_optionFlags_1740_; uint8_t v_suppressElabErrors_1741_; uint8_t v_isRecordingDeps_1742_; lean_object* v___f_1743_; lean_object* v_args_1744_; lean_object* v___f_1745_; lean_object* v_ref_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_val_1735_ = lean_ctor_get(v_termMeasure_x3f_1724_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_termMeasure_x3f_1724_, 1);
v_ref_1736_ = lean_ctor_get(v_val_1735_, 0);
lean_inc(v_ref_1736_);
v_toCold_1737_ = lean_ctor_get(v___y_1732_, 0);
v_currRecDepth_1738_ = lean_ctor_get(v___y_1732_, 1);
v_ref_1739_ = lean_ctor_get(v___y_1732_, 2);
v_optionFlags_1740_ = lean_ctor_get_uint16(v___y_1732_, sizeof(void*)*3);
v_suppressElabErrors_1741_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1742_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*3 + 3);
v___f_1743_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1725_);
v_args_1744_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1725_, v_xs_1726_, v_ys_1728_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1745_, 0, v_val_1735_);
lean_closure_set(v___f_1745_, 1, v_fnName_1727_);
lean_closure_set(v___f_1745_, 2, v_fixedParamPerm_1725_);
lean_closure_set(v___f_1745_, 3, v_args_1744_);
v_ref_1746_ = l_Lean_replaceRef(v_ref_1736_, v_ref_1739_);
lean_dec(v_ref_1736_);
lean_inc(v_currRecDepth_1738_);
lean_inc_ref(v_toCold_1737_);
v___x_1747_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1747_, 0, v_toCold_1737_);
lean_ctor_set(v___x_1747_, 1, v_currRecDepth_1738_);
lean_ctor_set(v___x_1747_, 2, v_ref_1746_);
lean_ctor_set_uint16(v___x_1747_, sizeof(void*)*3, v_optionFlags_1740_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*3 + 2, v_suppressElabErrors_1741_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*3 + 3, v_isRecordingDeps_1742_);
v___x_1748_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1745_, v___f_1743_, v___y_1730_, v___y_1731_, v___x_1747_, v___y_1733_);
lean_dec_ref_known(v___x_1747_, 3);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1761_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
v___x_1755_ = lean_array_push(v___x_1754_, v_a_1749_);
v___x_1756_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1757_);
v___x_1759_ = v___x_1751_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1748_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1748_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_args_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v_termMeasure_x3f_1724_);
lean_inc_ref(v_fixedParamPerm_1725_);
v_args_1770_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1725_, v_xs_1726_, v_ys_1728_);
v___x_1771_ = lean_array_get_size(v_args_1770_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1774_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1771_, v_fnName_1727_, v_fixedParamPerm_1725_, v_args_1770_, v___x_1772_, v___x_1773_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec_ref(v_args_1770_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1810_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1810_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1810_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1809_; 
v_fst_1779_ = lean_ctor_get(v_a_1775_, 0);
v_snd_1780_ = lean_ctor_get(v_a_1775_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1782_ = v_a_1775_;
v_isShared_1783_ = v_isSharedCheck_1809_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_dec(v_a_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1809_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_toCold_1791_; lean_object* v_options_1792_; uint8_t v_hasTrace_1793_; 
v_toCold_1791_ = lean_ctor_get(v___y_1732_, 0);
v_options_1792_ = lean_ctor_get(v_toCold_1791_, 2);
v_hasTrace_1793_ = lean_ctor_get_uint8(v_options_1792_, sizeof(void*)*1);
if (v_hasTrace_1793_ == 0)
{
goto v___jp_1784_;
}
else
{
lean_object* v_inheritedTraceOptions_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_inheritedTraceOptions_1794_ = lean_ctor_get(v_toCold_1791_, 11);
v___x_1795_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1796_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1794_, v_options_1792_, v___x_1796_);
if (v___x_1797_ == 0)
{
goto v___jp_1784_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1780_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_snd_1780_);
v___x_1800_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1795_, v___x_1799_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_dec_ref_known(v___x_1800_, 1);
goto v___jp_1784_;
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_del_object(v___x_1782_);
lean_dec(v_snd_1780_);
lean_dec(v_fst_1779_);
lean_del_object(v___x_1777_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
v___jp_1784_:
{
lean_object* v___x_1786_; 
if (v_isShared_1783_ == 0)
{
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_snd_1780_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1786_);
v___x_1788_ = v___x_1777_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
else
{
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1811_, lean_object* v_fixedParamPerm_1812_, lean_object* v_xs_1813_, lean_object* v_fnName_1814_, lean_object* v_ys_1815_, lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1811_, v_fixedParamPerm_1812_, v_xs_1813_, v_fnName_1814_, v_ys_1815_, v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v_x_1816_);
lean_dec_ref(v_xs_1813_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1823_, lean_object* v_fixedParamPerm_1824_, lean_object* v_xs_1825_, lean_object* v_value_1826_, lean_object* v_termMeasure_x3f_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___f_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1833_, 0, v_termMeasure_x3f_1827_);
lean_closure_set(v___f_1833_, 1, v_fixedParamPerm_1824_);
lean_closure_set(v___f_1833_, 2, v_xs_1825_);
lean_closure_set(v___f_1833_, 3, v_fnName_1823_);
v___x_1834_ = 0;
v___x_1835_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1826_, v___f_1833_, v___x_1834_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1836_, lean_object* v_fixedParamPerm_1837_, lean_object* v_xs_1838_, lean_object* v_value_1839_, lean_object* v_termMeasure_x3f_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1836_, v_fixedParamPerm_1837_, v_xs_1838_, v_value_1839_, v_termMeasure_x3f_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1847_, lean_object* v_fnName_1848_, lean_object* v_fixedParamPerm_1849_, lean_object* v_args_1850_, lean_object* v_inst_1851_, lean_object* v_R_1852_, lean_object* v_a_1853_, lean_object* v_b_1854_, lean_object* v_c_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1847_, v_fnName_1848_, v_fixedParamPerm_1849_, v_args_1850_, v_a_1853_, v_b_1854_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1862_, lean_object* v_fnName_1863_, lean_object* v_fixedParamPerm_1864_, lean_object* v_args_1865_, lean_object* v_inst_1866_, lean_object* v_R_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_c_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1862_, v_fnName_1863_, v_fixedParamPerm_1864_, v_args_1865_, v_inst_1866_, v_R_1867_, v_a_1868_, v_b_1869_, v_c_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v_args_1865_);
lean_dec(v_upperBound_1862_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
if (lean_obj_tag(v_x_1878_) == 0)
{
return v_x_1877_;
}
else
{
lean_object* v_key_1879_; lean_object* v_value_1880_; lean_object* v_tail_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1904_; 
v_key_1879_ = lean_ctor_get(v_x_1878_, 0);
v_value_1880_ = lean_ctor_get(v_x_1878_, 1);
v_tail_1881_ = lean_ctor_get(v_x_1878_, 2);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_x_1878_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1883_ = v_x_1878_;
v_isShared_1884_ = v_isSharedCheck_1904_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_tail_1881_);
lean_inc(v_value_1880_);
lean_inc(v_key_1879_);
lean_dec(v_x_1878_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1904_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; uint64_t v_fold_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1885_ = lean_array_get_size(v_x_1877_);
v___x_1886_ = lean_uint64_of_nat(v_key_1879_);
v___x_1887_ = 32ULL;
v___x_1888_ = lean_uint64_shift_right(v___x_1886_, v___x_1887_);
v_fold_1889_ = lean_uint64_xor(v___x_1886_, v___x_1888_);
v___x_1890_ = 16ULL;
v___x_1891_ = lean_uint64_shift_right(v_fold_1889_, v___x_1890_);
v___x_1892_ = lean_uint64_xor(v_fold_1889_, v___x_1891_);
v___x_1893_ = lean_uint64_to_usize(v___x_1892_);
v___x_1894_ = lean_usize_of_nat(v___x_1885_);
v___x_1895_ = ((size_t)1ULL);
v___x_1896_ = lean_usize_sub(v___x_1894_, v___x_1895_);
v___x_1897_ = lean_usize_land(v___x_1893_, v___x_1896_);
v___x_1898_ = lean_array_uget_borrowed(v_x_1877_, v___x_1897_);
lean_inc(v___x_1898_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 2, v___x_1898_);
v___x_1900_ = v___x_1883_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_key_1879_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_value_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_array_uset(v_x_1877_, v___x_1897_, v___x_1900_);
v_x_1877_ = v___x_1901_;
v_x_1878_ = v_tail_1881_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1905_, lean_object* v_source_1906_, lean_object* v_target_1907_){
_start:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = lean_array_get_size(v_source_1906_);
v___x_1909_ = lean_nat_dec_lt(v_i_1905_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_source_1906_);
lean_dec(v_i_1905_);
return v_target_1907_;
}
else
{
lean_object* v_es_1910_; lean_object* v___x_1911_; lean_object* v_source_1912_; lean_object* v_target_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_es_1910_ = lean_array_fget(v_source_1906_, v_i_1905_);
v___x_1911_ = lean_box(0);
v_source_1912_ = lean_array_fset(v_source_1906_, v_i_1905_, v___x_1911_);
v_target_1913_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1907_, v_es_1910_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_add(v_i_1905_, v___x_1914_);
lean_dec(v_i_1905_);
v_i_1905_ = v___x_1915_;
v_source_1906_ = v_source_1912_;
v_target_1907_ = v_target_1913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_nbuckets_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1918_ = lean_array_get_size(v_data_1917_);
v___x_1919_ = lean_unsigned_to_nat(2u);
v_nbuckets_1920_ = lean_nat_mul(v___x_1918_, v___x_1919_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_mk_array(v_nbuckets_1920_, v___x_1922_);
v___x_1924_ = lean_array_propagate_mark(v_data_1917_, v___x_1923_);
v___x_1925_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1921_, v_data_1917_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
else
{
lean_object* v_key_1929_; lean_object* v_tail_1930_; uint8_t v___x_1931_; 
v_key_1929_ = lean_ctor_get(v_x_1927_, 0);
v_tail_1930_ = lean_ctor_get(v_x_1927_, 2);
v___x_1931_ = lean_nat_dec_eq(v_key_1929_, v_a_1926_);
if (v___x_1931_ == 0)
{
v_x_1927_ = v_tail_1930_;
goto _start;
}
else
{
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1933_, lean_object* v_x_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1933_, v_x_1934_);
lean_dec(v_x_1934_);
lean_dec(v_a_1933_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1937_, lean_object* v_a_1938_, lean_object* v_b_1939_){
_start:
{
lean_object* v_size_1940_; lean_object* v_buckets_1941_; lean_object* v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; uint64_t v_fold_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; uint64_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; lean_object* v_bkt_1955_; uint8_t v___x_1956_; 
v_size_1940_ = lean_ctor_get(v_m_1937_, 0);
v_buckets_1941_ = lean_ctor_get(v_m_1937_, 1);
v___x_1942_ = lean_array_get_size(v_buckets_1941_);
v___x_1943_ = lean_uint64_of_nat(v_a_1938_);
v___x_1944_ = 32ULL;
v___x_1945_ = lean_uint64_shift_right(v___x_1943_, v___x_1944_);
v_fold_1946_ = lean_uint64_xor(v___x_1943_, v___x_1945_);
v___x_1947_ = 16ULL;
v___x_1948_ = lean_uint64_shift_right(v_fold_1946_, v___x_1947_);
v___x_1949_ = lean_uint64_xor(v_fold_1946_, v___x_1948_);
v___x_1950_ = lean_uint64_to_usize(v___x_1949_);
v___x_1951_ = lean_usize_of_nat(v___x_1942_);
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_sub(v___x_1951_, v___x_1952_);
v___x_1954_ = lean_usize_land(v___x_1950_, v___x_1953_);
v_bkt_1955_ = lean_array_uget_borrowed(v_buckets_1941_, v___x_1954_);
v___x_1956_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1938_, v_bkt_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1977_; 
lean_inc_ref(v_buckets_1941_);
lean_inc(v_size_1940_);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_m_1937_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; lean_object* v_unused_1979_; 
v_unused_1978_ = lean_ctor_get(v_m_1937_, 1);
lean_dec(v_unused_1978_);
v_unused_1979_ = lean_ctor_get(v_m_1937_, 0);
lean_dec(v_unused_1979_);
v___x_1958_ = v_m_1937_;
v_isShared_1959_ = v_isSharedCheck_1977_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v_m_1937_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1977_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v_size_x27_1961_; lean_object* v___x_1962_; lean_object* v_buckets_x27_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1960_ = lean_unsigned_to_nat(1u);
v_size_x27_1961_ = lean_nat_add(v_size_1940_, v___x_1960_);
lean_dec(v_size_1940_);
lean_inc(v_bkt_1955_);
v___x_1962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1962_, 0, v_a_1938_);
lean_ctor_set(v___x_1962_, 1, v_b_1939_);
lean_ctor_set(v___x_1962_, 2, v_bkt_1955_);
v_buckets_x27_1963_ = lean_array_uset(v_buckets_1941_, v___x_1954_, v___x_1962_);
v___x_1964_ = lean_unsigned_to_nat(4u);
v___x_1965_ = lean_nat_mul(v_size_x27_1961_, v___x_1964_);
v___x_1966_ = lean_unsigned_to_nat(3u);
v___x_1967_ = lean_nat_div(v___x_1965_, v___x_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_array_get_size(v_buckets_x27_1963_);
v___x_1969_ = lean_nat_dec_le(v___x_1967_, v___x_1968_);
lean_dec(v___x_1967_);
if (v___x_1969_ == 0)
{
lean_object* v_val_1970_; lean_object* v___x_1972_; 
v_val_1970_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1963_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_val_1970_);
lean_ctor_set(v___x_1958_, 0, v_size_x27_1961_);
v___x_1972_ = v___x_1958_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_size_x27_1961_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_val_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v___x_1975_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_buckets_x27_1963_);
lean_ctor_set(v___x_1958_, 0, v_size_x27_1961_);
v___x_1975_ = v___x_1958_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_size_x27_1961_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_buckets_x27_1963_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_dec(v_b_1939_);
lean_dec(v_a_1938_);
return v_m_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1980_, size_t v_sz_1981_, size_t v_i_1982_, lean_object* v_b_1983_){
_start:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_usize_dec_lt(v_i_1982_, v_sz_1981_);
if (v___x_1984_ == 0)
{
return v_b_1983_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; size_t v___x_1988_; size_t v___x_1989_; 
v_a_1985_ = lean_array_uget_borrowed(v_as_1980_, v_i_1982_);
v___x_1986_ = lean_box(0);
lean_inc(v_a_1985_);
v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1983_, v_a_1985_, v___x_1986_);
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_add(v_i_1982_, v___x_1988_);
v_i_1982_ = v___x_1989_;
v_b_1983_ = v___x_1987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1991_, lean_object* v_sz_1992_, lean_object* v_i_1993_, lean_object* v_b_1994_){
_start:
{
size_t v_sz_boxed_1995_; size_t v_i_boxed_1996_; lean_object* v_res_1997_; 
v_sz_boxed_1995_ = lean_unbox_usize(v_sz_1992_);
lean_dec(v_sz_1992_);
v_i_boxed_1996_ = lean_unbox_usize(v_i_1993_);
lean_dec(v_i_1993_);
v_res_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1991_, v_sz_boxed_1995_, v_i_boxed_1996_, v_b_1994_);
lean_dec_ref(v_as_1991_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1998_, size_t v_sz_1999_, size_t v_i_2000_, lean_object* v_b_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_2000_, v_sz_1999_);
if (v___x_2002_ == 0)
{
return v_b_2001_;
}
else
{
lean_object* v_a_2003_; lean_object* v_indicesPos_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; 
v_a_2003_ = lean_array_uget_borrowed(v_as_1998_, v_i_2000_);
v_indicesPos_2004_ = lean_ctor_get(v_a_2003_, 3);
v_sz_2005_ = lean_array_size(v_indicesPos_2004_);
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2004_, v_sz_2005_, v___x_2006_, v_b_2001_);
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_2000_, v___x_2008_);
v_i_2000_ = v___x_2009_;
v_b_2001_ = v___x_2007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2011_, lean_object* v_sz_2012_, lean_object* v_i_2013_, lean_object* v_b_2014_){
_start:
{
size_t v_sz_boxed_2015_; size_t v_i_boxed_2016_; lean_object* v_res_2017_; 
v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2011_, v_sz_boxed_2015_, v_i_boxed_2016_, v_b_2014_);
lean_dec_ref(v_as_2011_);
return v_res_2017_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_buckets_2020_; lean_object* v___x_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; uint64_t v___x_2024_; uint64_t v_fold_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; uint64_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_buckets_2020_ = lean_ctor_get(v_m_2018_, 1);
v___x_2021_ = lean_array_get_size(v_buckets_2020_);
v___x_2022_ = lean_uint64_of_nat(v_a_2019_);
v___x_2023_ = 32ULL;
v___x_2024_ = lean_uint64_shift_right(v___x_2022_, v___x_2023_);
v_fold_2025_ = lean_uint64_xor(v___x_2022_, v___x_2024_);
v___x_2026_ = 16ULL;
v___x_2027_ = lean_uint64_shift_right(v_fold_2025_, v___x_2026_);
v___x_2028_ = lean_uint64_xor(v_fold_2025_, v___x_2027_);
v___x_2029_ = lean_uint64_to_usize(v___x_2028_);
v___x_2030_ = lean_usize_of_nat(v___x_2021_);
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_sub(v___x_2030_, v___x_2031_);
v___x_2033_ = lean_usize_land(v___x_2029_, v___x_2032_);
v___x_2034_ = lean_array_uget_borrowed(v_buckets_2020_, v___x_2033_);
v___x_2035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2019_, v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2036_, lean_object* v_a_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2036_, v_a_2037_);
lean_dec(v_a_2037_);
lean_dec_ref(v_m_2036_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2040_, lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_a_2046_; uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2050_ == 0)
{
return v_b_2044_;
}
else
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2067_; 
v_fst_2051_ = lean_ctor_get(v_b_2044_, 0);
v_snd_2052_ = lean_ctor_get(v_b_2044_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_b_2044_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2054_ = v_b_2044_;
v_isShared_2055_ = v_isSharedCheck_2067_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_dec(v_b_2044_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2067_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_a_2056_; lean_object* v_recArgPos_2057_; uint8_t v___x_2058_; 
v_a_2056_ = lean_array_uget_borrowed(v_as_2041_, v_i_2043_);
v_recArgPos_2057_ = lean_ctor_get(v_a_2056_, 2);
v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2040_, v_recArgPos_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_inc(v_a_2056_);
v___x_2059_ = lean_array_push(v_snd_2052_, v_a_2056_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2059_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_fst_2051_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
v_a_2046_ = v___x_2061_;
goto v___jp_2045_;
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_inc(v_a_2056_);
v___x_2063_ = lean_array_push(v_fst_2051_, v_a_2056_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2063_);
v___x_2065_ = v___x_2054_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_snd_2052_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v_a_2046_ = v___x_2065_;
goto v___jp_2045_;
}
}
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; 
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2043_, v___x_2047_);
v_i_2043_ = v___x_2048_;
v_b_2044_ = v_a_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2068_, lean_object* v_as_2069_, lean_object* v_sz_2070_, lean_object* v_i_2071_, lean_object* v_b_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2070_);
lean_dec(v_sz_2070_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2071_);
lean_dec(v_i_2071_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2068_, v_as_2069_, v_sz_boxed_2073_, v_i_boxed_2074_, v_b_2072_);
lean_dec_ref(v_as_2069_);
lean_dec_ref(v___x_2068_);
return v_res_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_unsigned_to_nat(16u);
v___x_2078_ = lean_mk_array(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_indicesPos_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2080_ = lean_unsigned_to_nat(0u);
v_indicesPos_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2081_, 0, v___x_2080_);
lean_ctor_set(v_indicesPos_2081_, 1, v___x_2079_);
return v_indicesPos_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2084_){
_start:
{
lean_object* v_indicesPos_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v___x_2093_; 
v_indicesPos_2085_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2086_ = lean_array_size(v_recArgInfos_2084_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2084_, v_sz_2086_, v___x_2087_, v_indicesPos_2085_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2088_, v_recArgInfos_2084_, v_sz_2086_, v___x_2087_, v___x_2089_);
lean_dec_ref(v___x_2088_);
v_fst_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_fst_2091_);
v_snd_2092_ = lean_ctor_get(v___x_2090_, 1);
lean_inc(v_snd_2092_);
lean_dec_ref(v___x_2090_);
v___x_2093_ = l_Array_append___redArg(v_snd_2092_, v_fst_2091_);
lean_dec(v_fst_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2094_);
lean_dec_ref(v_recArgInfos_2094_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2096_, lean_object* v_m_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2097_, v_a_2098_, v_b_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2101_, lean_object* v_m_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2102_, v_a_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2105_, lean_object* v_m_2106_, lean_object* v_a_2107_){
_start:
{
uint8_t v_res_2108_; lean_object* v_r_2109_; 
v_res_2108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2105_, v_m_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_m_2106_);
v_r_2109_ = lean_box(v_res_2108_);
return v_r_2109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2110_, lean_object* v_a_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2111_, v_x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2114_, lean_object* v_a_2115_, lean_object* v_x_2116_){
_start:
{
uint8_t v_res_2117_; lean_object* v_r_2118_; 
v_res_2117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2114_, v_a_2115_, v_x_2116_);
lean_dec(v_x_2116_);
lean_dec(v_a_2115_);
v_r_2118_ = lean_box(v_res_2117_);
return v_r_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2119_, lean_object* v_data_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2122_, lean_object* v_i_2123_, lean_object* v_source_2124_, lean_object* v_target_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2123_, v_source_2124_, v_target_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2128_, v_x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2131_, lean_object* v_a_2132_, lean_object* v_toPure_2133_, uint8_t v_____do__lift_2134_){
_start:
{
if (v_____do__lift_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_array_push(v___y_2131_, v_a_2132_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___x_2137_ = lean_apply_2(v_toPure_2133_, lean_box(0), v___x_2136_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_a_2132_);
v___x_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___y_2131_);
v___x_2139_ = lean_apply_2(v_toPure_2133_, lean_box(0), v___x_2138_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2140_, lean_object* v_a_2141_, lean_object* v_toPure_2142_, lean_object* v_____do__lift_2143_){
_start:
{
uint8_t v_____do__lift_159__boxed_2144_; lean_object* v_res_2145_; 
v_____do__lift_159__boxed_2144_ = lean_unbox(v_____do__lift_2143_);
v_res_2145_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2140_, v_a_2141_, v_toPure_2142_, v_____do__lift_159__boxed_2144_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2146_, lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_apply_2(v_eq_2146_, v_x_2148_, v_a_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2150_, lean_object* v___x_2151_, lean_object* v_toBind_2152_, lean_object* v_eq_2153_, lean_object* v_inst_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___f_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
lean_inc(v_toPure_2150_);
lean_inc(v_a_2155_);
lean_inc_ref(v___y_2157_);
v___f_2158_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2158_, 0, v___y_2157_);
lean_closure_set(v___f_2158_, 1, v_a_2155_);
lean_closure_set(v___f_2158_, 2, v_toPure_2150_);
v___x_2159_ = lean_array_get_size(v___y_2157_);
v___x_2160_ = lean_nat_dec_lt(v___x_2151_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v___y_2157_);
lean_dec(v_a_2155_);
lean_dec_ref(v_inst_2154_);
lean_dec(v_eq_2153_);
v___x_2161_ = lean_box(v___x_2160_);
v___x_2162_ = lean_apply_2(v_toPure_2150_, lean_box(0), v___x_2161_);
v___x_2163_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2162_, v___f_2158_);
return v___x_2163_;
}
else
{
if (v___x_2160_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec_ref(v___y_2157_);
lean_dec(v_a_2155_);
lean_dec_ref(v_inst_2154_);
lean_dec(v_eq_2153_);
v___x_2164_ = lean_box(v___x_2160_);
v___x_2165_ = lean_apply_2(v_toPure_2150_, lean_box(0), v___x_2164_);
v___x_2166_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2165_, v___f_2158_);
return v___x_2166_;
}
else
{
lean_object* v___f_2167_; size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v_toPure_2150_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2167_, 0, v_eq_2153_);
lean_closure_set(v___f_2167_, 1, v_a_2155_);
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = lean_usize_of_nat(v___x_2159_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2154_, v___f_2167_, v___y_2157_, v___x_2168_, v___x_2169_);
v___x_2171_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2170_, v___f_2158_);
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2172_, lean_object* v___x_2173_, lean_object* v_toBind_2174_, lean_object* v_eq_2175_, lean_object* v_inst_2176_, lean_object* v_a_2177_, lean_object* v_x_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2172_, v___x_2173_, v_toBind_2174_, v_eq_2175_, v_inst_2176_, v_a_2177_, v_x_2178_, v___y_2179_);
lean_dec(v___x_2173_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2181_, lean_object* v_____s_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_apply_2(v_toPure_2181_, lean_box(0), v_____s_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2186_, lean_object* v_eq_2187_, lean_object* v_xs_2188_){
_start:
{
lean_object* v_toApplicative_2189_; lean_object* v_toBind_2190_; lean_object* v_toPure_2191_; lean_object* v___x_2192_; lean_object* v_ret_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_toApplicative_2189_ = lean_ctor_get(v_inst_2186_, 0);
v_toBind_2190_ = lean_ctor_get(v_inst_2186_, 1);
lean_inc_n(v_toBind_2190_, 2);
v_toPure_2191_ = lean_ctor_get(v_toApplicative_2189_, 1);
v___x_2192_ = lean_unsigned_to_nat(0u);
v_ret_2193_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2186_);
lean_inc_n(v_toPure_2191_, 2);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2194_, 0, v_toPure_2191_);
lean_closure_set(v___f_2194_, 1, v___x_2192_);
lean_closure_set(v___f_2194_, 2, v_toBind_2190_);
lean_closure_set(v___f_2194_, 3, v_eq_2187_);
lean_closure_set(v___f_2194_, 4, v_inst_2186_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2195_, 0, v_toPure_2191_);
v_sz_2196_ = lean_array_size(v_xs_2188_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2186_, v_xs_2188_, v___f_2194_, v_sz_2196_, v___x_2197_, v_ret_2193_);
v___x_2199_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v___x_2198_, v___f_2195_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2200_, lean_object* v_00_u03b1_2201_, lean_object* v_inst_2202_, lean_object* v_eq_2203_, lean_object* v_xs_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2202_, v_eq_2203_, v_xs_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_bs_2208_){
_start:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_usize_dec_lt(v_i_2207_, v_sz_2206_);
if (v___x_2209_ == 0)
{
return v_bs_2208_;
}
else
{
lean_object* v_v_2210_; lean_object* v_indGroupInst_2211_; lean_object* v___x_2212_; lean_object* v_bs_x27_2213_; size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v_v_2210_ = lean_array_uget_borrowed(v_bs_2208_, v_i_2207_);
v_indGroupInst_2211_ = lean_ctor_get(v_v_2210_, 4);
lean_inc_ref(v_indGroupInst_2211_);
v___x_2212_ = lean_unsigned_to_nat(0u);
v_bs_x27_2213_ = lean_array_uset(v_bs_2208_, v_i_2207_, v___x_2212_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_add(v_i_2207_, v___x_2214_);
v___x_2216_ = lean_array_uset(v_bs_x27_2213_, v_i_2207_, v_indGroupInst_2211_);
v_i_2207_ = v___x_2215_;
v_bs_2208_ = v___x_2216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_bs_2220_){
_start:
{
size_t v_sz_boxed_2221_; size_t v_i_boxed_2222_; lean_object* v_res_2223_; 
v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2222_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2221_, v_i_boxed_2222_, v_bs_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2224_, lean_object* v_a_2225_, lean_object* v_as_2226_, size_t v_i_2227_, size_t v_stop_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_eq(v_i_2227_, v_stop_2228_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = 1;
v___x_2236_ = lean_array_uget_borrowed(v_as_2226_, v_i_2227_);
lean_inc_ref(v_eq_2224_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
lean_inc(v_a_2225_);
lean_inc(v___x_2236_);
v___x_2237_ = lean_apply_7(v_eq_2224_, v___x_2236_, v_a_2225_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, lean_box(0));
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2250_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2250_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2250_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
if (v___x_2242_ == 0)
{
size_t v___x_2243_; size_t v___x_2244_; 
lean_del_object(v___x_2240_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2227_, v___x_2243_);
v_i_2227_ = v___x_2244_;
goto _start;
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_dec(v_a_2225_);
lean_dec_ref(v_eq_2224_);
v___x_2246_ = lean_box(v___x_2235_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2246_);
v___x_2248_ = v___x_2240_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec(v_a_2225_);
lean_dec_ref(v_eq_2224_);
return v___x_2237_;
}
}
else
{
uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_a_2225_);
lean_dec_ref(v_eq_2224_);
v___x_2251_ = 0;
v___x_2252_ = lean_box(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2254_, lean_object* v_a_2255_, lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_stop_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
size_t v_i_boxed_2264_; size_t v_stop_boxed_2265_; lean_object* v_res_2266_; 
v_i_boxed_2264_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_stop_boxed_2265_ = lean_unbox_usize(v_stop_2258_);
lean_dec(v_stop_2258_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2254_, v_a_2255_, v_as_2256_, v_i_boxed_2264_, v_stop_boxed_2265_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_as_2256_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2267_, lean_object* v_a_2268_, uint8_t v_____do__lift_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
if (v_____do__lift_2269_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_array_push(v_b_2267_, v_a_2268_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec(v_a_2268_);
v___x_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_b_2267_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2280_, lean_object* v_a_2281_, lean_object* v_____do__lift_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_____do__lift_1276__boxed_2288_; lean_object* v_res_2289_; 
v_____do__lift_1276__boxed_2288_ = lean_unbox(v_____do__lift_2282_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2280_, v_a_2281_, v_____do__lift_1276__boxed_2288_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2290_, lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___y_2301_; uint8_t v___x_2323_; 
v___x_2323_ = lean_usize_dec_lt(v_i_2293_, v_sz_2292_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_dec_ref(v_eq_2290_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_b_2294_);
return v___x_2324_;
}
else
{
lean_object* v___x_2325_; lean_object* v_a_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2325_ = lean_unsigned_to_nat(0u);
v_a_2326_ = lean_array_uget_borrowed(v_as_2291_, v_i_2293_);
v___x_2327_ = lean_array_get_size(v_b_2294_);
v___x_2328_ = lean_nat_dec_lt(v___x_2325_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
lean_inc(v_a_2326_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2294_, v_a_2326_, v___x_2328_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
v___y_2301_ = v___x_2329_;
goto v___jp_2300_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_eq_2290_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2290_, v_a_2326_, v_b_2294_, v___x_2330_, v___x_2331_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
lean_inc(v_a_2326_);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2294_, v_a_2326_, v___x_2334_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
v___y_2301_ = v___x_2335_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_b_2294_);
lean_dec_ref(v_eq_2290_);
v_a_2336_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2332_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2332_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
v___jp_2300_:
{
if (lean_obj_tag(v___y_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2314_; 
v_a_2302_ = lean_ctor_get(v___y_2301_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___y_2301_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2304_ = v___y_2301_;
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___y_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
if (lean_obj_tag(v_a_2302_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; 
lean_dec_ref(v_eq_2290_);
v_a_2306_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v_a_2302_, 1);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_a_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v_a_2310_; size_t v___x_2311_; size_t v___x_2312_; 
lean_del_object(v___x_2304_);
v_a_2310_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v_a_2302_, 1);
v___x_2311_ = ((size_t)1ULL);
v___x_2312_ = lean_usize_add(v_i_2293_, v___x_2311_);
v_i_2293_ = v___x_2312_;
v_b_2294_ = v_a_2310_;
goto _start;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v_eq_2290_);
v_a_2315_ = lean_ctor_get(v___y_2301_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___y_2301_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___y_2301_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___y_2301_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2344_, lean_object* v_as_2345_, lean_object* v_sz_2346_, lean_object* v_i_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
size_t v_sz_boxed_2354_; size_t v_i_boxed_2355_; lean_object* v_res_2356_; 
v_sz_boxed_2354_ = lean_unbox_usize(v_sz_2346_);
lean_dec(v_sz_2346_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2347_);
lean_dec(v_i_2347_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2344_, v_as_2345_, v_sz_boxed_2354_, v_i_boxed_2355_, v_b_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_as_2345_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2357_, lean_object* v_xs_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_ret_2364_; size_t v_sz_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v_ret_2364_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2365_ = lean_array_size(v_xs_2358_);
v___x_2366_ = ((size_t)0ULL);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2357_, v_xs_2358_, v_sz_2365_, v___x_2366_, v_ret_2364_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2368_, lean_object* v_xs_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2368_, v_xs_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_xs_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2383_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2384_ = lean_array_size(v_recArgInfos_2377_);
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2384_, v___x_2385_, v_recArgInfos_2377_);
v___x_2387_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2383_, v___x_2386_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec_ref(v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2395_, lean_object* v_eq_2396_, lean_object* v_xs_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2396_, v_xs_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_eq_2405_, lean_object* v_xs_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2404_, v_eq_2405_, v_xs_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_xs_2406_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2413_, lean_object* v_eq_2414_, lean_object* v_a_2415_, lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2414_, v_a_2415_, v_as_2416_, v_i_2417_, v_stop_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_eq_2426_, lean_object* v_a_2427_, lean_object* v_as_2428_, lean_object* v_i_2429_, lean_object* v_stop_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
size_t v_i_boxed_2436_; size_t v_stop_boxed_2437_; lean_object* v_res_2438_; 
v_i_boxed_2436_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_stop_boxed_2437_ = lean_unbox_usize(v_stop_2430_);
lean_dec(v_stop_2430_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2425_, v_eq_2426_, v_a_2427_, v_as_2428_, v_i_boxed_2436_, v_stop_boxed_2437_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_as_2428_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2439_, lean_object* v_eq_2440_, lean_object* v_as_2441_, size_t v_sz_2442_, size_t v_i_2443_, lean_object* v_b_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2440_, v_as_2441_, v_sz_2442_, v_i_2443_, v_b_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_eq_2452_, lean_object* v_as_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_b_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2451_, v_eq_2452_, v_as_2453_, v_sz_boxed_2462_, v_i_boxed_2463_, v_b_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_as_2453_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = l_Lean_Expr_hasMVar(v_e_2465_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_e_2465_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v_mctx_2471_; lean_object* v___x_2472_; lean_object* v_fst_2473_; lean_object* v_snd_2474_; lean_object* v___x_2475_; lean_object* v_cache_2476_; lean_object* v_zetaDeltaFVarIds_2477_; lean_object* v_postponed_2478_; lean_object* v_diag_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2488_; 
v___x_2470_ = lean_st_ref_get(v___y_2466_);
v_mctx_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_ref(v_mctx_2471_);
lean_dec(v___x_2470_);
v___x_2472_ = l_Lean_instantiateMVarsCore(v_mctx_2471_, v_e_2465_);
v_fst_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_fst_2473_);
v_snd_2474_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2474_);
lean_dec_ref(v___x_2472_);
v___x_2475_ = lean_st_ref_take(v___y_2466_);
v_cache_2476_ = lean_ctor_get(v___x_2475_, 1);
v_zetaDeltaFVarIds_2477_ = lean_ctor_get(v___x_2475_, 2);
v_postponed_2478_ = lean_ctor_get(v___x_2475_, 3);
v_diag_2479_ = lean_ctor_get(v___x_2475_, 4);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2475_, 0);
lean_dec(v_unused_2489_);
v___x_2481_ = v___x_2475_;
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_diag_2479_);
lean_inc(v_postponed_2478_);
lean_inc(v_zetaDeltaFVarIds_2477_);
lean_inc(v_cache_2476_);
lean_dec(v___x_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_snd_2474_);
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_snd_2474_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_cache_2476_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_zetaDeltaFVarIds_2477_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_postponed_2478_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_diag_2479_);
v___x_2484_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_st_ref_put(v___y_2466_, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_fst_2473_);
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2490_, v___y_2491_);
lean_dec(v___y_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2494_, v___y_2496_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2510_ = lean_unsigned_to_nat(109u);
v___x_2511_ = lean_unsigned_to_nat(216u);
v___x_2512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2514_ = l_mkPanicMessageWithDecl(v___x_2513_, v___x_2512_, v___x_2511_, v___x_2510_, v___x_2509_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2515_, size_t v_sz_2516_, size_t v_i_2517_, lean_object* v_bs_2518_){
_start:
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_usize_dec_lt(v_i_2517_, v_sz_2516_);
if (v___x_2519_ == 0)
{
return v_bs_2518_;
}
else
{
lean_object* v_v_2520_; lean_object* v___x_2521_; lean_object* v_bs_x27_2522_; lean_object* v___y_2524_; lean_object* v___x_2529_; 
v_v_2520_ = lean_array_uget(v_bs_2518_, v_i_2517_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v_bs_x27_2522_ = lean_array_uset(v_bs_2518_, v_i_2517_, v___x_2521_);
v___x_2529_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2515_, v_v_2520_);
lean_dec(v_v_2520_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2531_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2530_);
v___y_2524_ = v___x_2531_;
goto v___jp_2523_;
}
else
{
lean_object* v_val_2532_; 
v_val_2532_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2529_, 1);
v___y_2524_ = v_val_2532_;
goto v___jp_2523_;
}
v___jp_2523_:
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)1ULL);
v___x_2526_ = lean_usize_add(v_i_2517_, v___x_2525_);
v___x_2527_ = lean_array_uset(v_bs_x27_2522_, v_i_2517_, v___y_2524_);
v_i_2517_ = v___x_2526_;
v_bs_2518_ = v___x_2527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2533_, lean_object* v_sz_2534_, lean_object* v_i_2535_, lean_object* v_bs_2536_){
_start:
{
size_t v_sz_boxed_2537_; size_t v_i_boxed_2538_; lean_object* v_res_2539_; 
v_sz_boxed_2537_ = lean_unbox_usize(v_sz_2534_);
lean_dec(v_sz_2534_);
v_i_boxed_2538_ = lean_unbox_usize(v_i_2535_);
lean_dec(v_i_2535_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2533_, v_sz_boxed_2537_, v_i_boxed_2538_, v_bs_2536_);
lean_dec_ref(v___x_2533_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2540_, size_t v_i_2541_, lean_object* v_bs_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_usize_dec_lt(v_i_2541_, v_sz_2540_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_bs_2542_);
return v___x_2549_;
}
else
{
lean_object* v_v_2550_; lean_object* v___x_2551_; lean_object* v_bs_x27_2552_; lean_object* v___x_2553_; 
v_v_2550_ = lean_array_uget(v_bs_2542_, v_i_2541_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v_bs_x27_2552_ = lean_array_uset(v_bs_2542_, v_i_2541_, v___x_2551_);
v___x_2553_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2550_, v___y_2544_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = ((size_t)1ULL);
v___x_2556_ = lean_usize_add(v_i_2541_, v___x_2555_);
v___x_2557_ = lean_array_uset(v_bs_x27_2552_, v_i_2541_, v_a_2554_);
v_i_2541_ = v___x_2556_;
v_bs_2542_ = v___x_2557_;
goto _start;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_bs_x27_2552_);
v_a_2559_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2553_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2553_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2567_, lean_object* v_i_2568_, lean_object* v_bs_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
size_t v_sz_boxed_2575_; size_t v_i_boxed_2576_; lean_object* v_res_2577_; 
v_sz_boxed_2575_ = lean_unbox_usize(v_sz_2567_);
lean_dec(v_sz_2567_);
v_i_boxed_2576_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2575_, v_i_boxed_2576_, v_bs_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2577_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2578_, lean_object* v___x_2579_, lean_object* v_as_2580_, size_t v_i_2581_, size_t v_stop_2582_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_eq(v_i_2581_, v_stop_2582_);
if (v___x_2583_ == 0)
{
uint8_t v___x_2584_; uint8_t v___y_2586_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2584_ = 1;
v___x_2590_ = lean_array_uget_borrowed(v_as_2580_, v_i_2581_);
v___x_2591_ = l_Lean_Expr_isFVar(v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2586_ = v_a_2578_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_nat_dec_eq(v___x_2579_, v___x_2592_);
v___y_2586_ = v___x_2593_;
goto v___jp_2585_;
}
v___jp_2585_:
{
if (v___y_2586_ == 0)
{
size_t v___x_2587_; size_t v___x_2588_; 
v___x_2587_ = ((size_t)1ULL);
v___x_2588_ = lean_usize_add(v_i_2581_, v___x_2587_);
v_i_2581_ = v___x_2588_;
goto _start;
}
else
{
return v___x_2584_;
}
}
}
else
{
uint8_t v___x_2594_; 
v___x_2594_ = 0;
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2595_, lean_object* v___x_2596_, lean_object* v_as_2597_, lean_object* v_i_2598_, lean_object* v_stop_2599_){
_start:
{
uint8_t v_a_7784__boxed_2600_; size_t v_i_boxed_2601_; size_t v_stop_boxed_2602_; uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_a_7784__boxed_2600_ = lean_unbox(v_a_2595_);
v_i_boxed_2601_ = lean_unbox_usize(v_i_2598_);
lean_dec(v_i_2598_);
v_stop_boxed_2602_ = lean_unbox_usize(v_stop_2599_);
lean_dec(v_stop_2599_);
v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7784__boxed_2600_, v___x_2596_, v_as_2597_, v_i_boxed_2601_, v_stop_boxed_2602_);
lean_dec_ref(v_as_2597_);
lean_dec(v___x_2596_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2605_, lean_object* v_ys_2606_, lean_object* v___x_2607_, lean_object* v_recArgInfo_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v_group_2611_, lean_object* v___x_2612_, lean_object* v_as_2613_, size_t v_sz_2614_, size_t v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_a_2623_; uint8_t v___x_2627_; 
v___x_2627_ = lean_usize_dec_lt(v_i_2615_, v_sz_2614_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2616_);
return v___x_2628_;
}
else
{
lean_object* v_snd_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2785_; 
v_snd_2629_ = lean_ctor_get(v_b_2616_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_b_2616_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_b_2616_, 0);
lean_dec(v_unused_2786_);
v___x_2631_ = v_b_2616_;
v_isShared_2632_ = v_isSharedCheck_2785_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_snd_2629_);
lean_dec(v_b_2616_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2785_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_next_2633_; lean_object* v_upperBound_2634_; lean_object* v___x_2635_; 
v_next_2633_ = lean_ctor_get(v_snd_2629_, 0);
lean_inc(v_next_2633_);
v_upperBound_2634_ = lean_ctor_get(v_snd_2629_, 1);
v___x_2635_ = lean_box(0);
if (lean_obj_tag(v_next_2633_) == 0)
{
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
goto v___jp_2636_;
}
else
{
lean_object* v_val_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2784_; 
v_val_2641_ = lean_ctor_get(v_next_2633_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_next_2633_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2643_ = v_next_2633_;
v_isShared_2644_ = v_isSharedCheck_2784_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_val_2641_);
lean_dec(v_next_2633_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2784_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_nat_dec_lt(v_val_2641_, v_upperBound_2634_);
if (v___x_2645_ == 0)
{
lean_del_object(v___x_2643_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
goto v___jp_2636_;
}
else
{
lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2781_; 
lean_inc(v_upperBound_2634_);
lean_del_object(v___x_2631_);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_snd_2629_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2782_ = lean_ctor_get(v_snd_2629_, 1);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_snd_2629_, 0);
lean_dec(v_unused_2783_);
v___x_2647_ = v_snd_2629_;
v_isShared_2648_ = v_isSharedCheck_2781_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v_snd_2629_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2781_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_a_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v_a_2649_ = lean_array_uget_borrowed(v_as_2613_, v_i_2615_);
v___x_2650_ = lean_unsigned_to_nat(1u);
v___x_2651_ = lean_nat_add(v_val_2641_, v___x_2650_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2651_);
v___x_2653_ = v___x_2643_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2653_);
v___x_2655_ = v___x_2647_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_upperBound_2634_);
v___x_2655_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; 
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc_ref(v___x_2605_);
v___x_2656_ = lean_infer_type(v___x_2605_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_whnfD(v_a_2657_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = 0;
lean_inc(v_a_2649_);
v___x_2661_ = l_Lean_Meta_forallMetaTelescope(v_a_2649_, v___x_2660_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_snd_2663_; lean_object* v_fst_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2754_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v_snd_2663_ = lean_ctor_get(v_a_2662_, 1);
v_fst_2664_ = lean_ctor_get(v_a_2662_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2662_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2666_ = v_a_2662_;
v_isShared_2667_ = v_isSharedCheck_2754_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snd_2663_);
lean_inc(v_fst_2664_);
lean_dec(v_a_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2754_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_snd_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2752_; 
v_snd_2668_ = lean_ctor_get(v_snd_2663_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_snd_2663_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; 
v_unused_2753_ = lean_ctor_get(v_snd_2663_, 0);
lean_dec(v_unused_2753_);
v___x_2670_ = v_snd_2663_;
v_isShared_2671_ = v_isSharedCheck_2752_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2668_);
lean_dec(v_snd_2663_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2752_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2668_, v_a_2659_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; uint8_t v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_unbox(v_a_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2676_; 
lean_dec(v_a_2673_);
lean_del_object(v___x_2666_);
lean_dec(v_fst_2664_);
lean_dec(v_val_2641_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2655_);
lean_ctor_set(v___x_2670_, 0, v___x_2635_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2655_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v_a_2623_ = v___x_2676_;
goto v___jp_2622_;
}
}
else
{
size_t v_sz_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v_sz_2678_ = lean_array_size(v_fst_2664_);
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2678_, v___x_2679_, v_fst_2664_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = lean_array_get_size(v_a_2681_);
v___x_2729_ = lean_nat_dec_lt(v___x_2727_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_dec(v_a_2673_);
lean_del_object(v___x_2666_);
goto v___jp_2682_;
}
else
{
if (v___x_2729_ == 0)
{
lean_dec(v_a_2673_);
lean_del_object(v___x_2666_);
goto v___jp_2682_;
}
else
{
size_t v___x_2730_; uint8_t v___x_2731_; uint8_t v___x_2732_; 
v___x_2730_ = lean_usize_of_nat(v___x_2728_);
v___x_2731_ = lean_unbox(v_a_2673_);
lean_dec(v_a_2673_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2731_, v___x_2612_, v_a_2681_, v___x_2679_, v___x_2730_);
if (v___x_2732_ == 0)
{
lean_del_object(v___x_2666_);
goto v___jp_2682_;
}
else
{
lean_object* v___x_2734_; 
lean_dec(v_a_2681_);
lean_del_object(v___x_2670_);
lean_dec(v_val_2641_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2655_);
lean_ctor_set(v___x_2666_, 0, v___x_2635_);
v___x_2734_ = v___x_2666_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2655_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v_a_2623_ = v___x_2734_;
goto v___jp_2622_;
}
}
}
}
v___jp_2682_:
{
uint8_t v___x_2683_; 
v___x_2683_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2681_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2685_; 
lean_dec(v_a_2681_);
lean_dec(v_val_2641_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2655_);
lean_ctor_set(v___x_2670_, 0, v___x_2635_);
v___x_2685_ = v___x_2670_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2655_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
v_a_2623_ = v___x_2685_;
goto v___jp_2622_;
}
}
else
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2606_, v_a_2681_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2718_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
if (lean_obj_tag(v_a_2688_) == 1)
{
lean_object* v___x_2693_; 
lean_dec_ref_known(v_a_2688_, 1);
lean_del_object(v___x_2690_);
lean_dec(v_a_2681_);
lean_dec(v_val_2641_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2655_);
lean_ctor_set(v___x_2670_, 0, v___x_2635_);
v___x_2693_ = v___x_2670_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2655_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v_a_2623_ = v___x_2693_;
goto v___jp_2622_;
}
}
else
{
lean_object* v_fnName_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_a_2688_);
lean_dec_ref(v___x_2605_);
v_fnName_2695_ = lean_ctor_get(v_recArgInfo_2608_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_recArgInfo_2608_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; 
v_unused_2713_ = lean_ctor_get(v_recArgInfo_2608_, 5);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_recArgInfo_2608_, 4);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_recArgInfo_2608_, 3);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_recArgInfo_2608_, 2);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_recArgInfo_2608_, 1);
lean_dec(v_unused_2717_);
v___x_2697_ = v_recArgInfo_2608_;
v_isShared_2698_ = v_isSharedCheck_2712_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_fnName_2695_);
lean_dec(v_recArgInfo_2608_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2712_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
size_t v_sz_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v_sz_2699_ = lean_array_size(v_a_2681_);
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2607_, v_sz_2699_, v___x_2679_, v_a_2681_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 5, v_val_2641_);
lean_ctor_set(v___x_2697_, 4, v_group_2611_);
lean_ctor_set(v___x_2697_, 3, v___x_2700_);
lean_ctor_set(v___x_2697_, 2, v___x_2610_);
lean_ctor_set(v___x_2697_, 1, v___x_2609_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_fnName_2695_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_group_2611_);
lean_ctor_set(v_reuseFailAlloc_2711_, 5, v_val_2641_);
v___x_2702_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2655_);
lean_ctor_set(v___x_2670_, 0, v___x_2704_);
v___x_2706_ = v___x_2670_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2655_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2706_);
v___x_2708_ = v___x_2690_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2681_);
lean_del_object(v___x_2670_);
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2719_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2687_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2687_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2673_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2736_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2680_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2680_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec(v_fst_2664_);
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2744_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2672_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2672_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_a_2659_);
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2755_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2661_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2661_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2763_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2658_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2658_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v___x_2655_);
lean_dec(v_val_2641_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2605_);
v_a_2771_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2656_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2656_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
}
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2635_);
v___x_2638_ = v___x_2631_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_snd_2629_);
v___x_2638_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
}
}
v___jp_2622_:
{
size_t v___x_2624_; size_t v___x_2625_; 
v___x_2624_ = ((size_t)1ULL);
v___x_2625_ = lean_usize_add(v_i_2615_, v___x_2624_);
v_i_2615_ = v___x_2625_;
v_b_2616_ = v_a_2623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2787_ = _args[0];
lean_object* v_ys_2788_ = _args[1];
lean_object* v___x_2789_ = _args[2];
lean_object* v_recArgInfo_2790_ = _args[3];
lean_object* v___x_2791_ = _args[4];
lean_object* v___x_2792_ = _args[5];
lean_object* v_group_2793_ = _args[6];
lean_object* v___x_2794_ = _args[7];
lean_object* v_as_2795_ = _args[8];
lean_object* v_sz_2796_ = _args[9];
lean_object* v_i_2797_ = _args[10];
lean_object* v_b_2798_ = _args[11];
lean_object* v___y_2799_ = _args[12];
lean_object* v___y_2800_ = _args[13];
lean_object* v___y_2801_ = _args[14];
lean_object* v___y_2802_ = _args[15];
lean_object* v___y_2803_ = _args[16];
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2796_);
lean_dec(v_sz_2796_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2797_);
lean_dec(v_i_2797_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2787_, v_ys_2788_, v___x_2789_, v_recArgInfo_2790_, v___x_2791_, v___x_2792_, v_group_2793_, v___x_2794_, v_as_2795_, v_sz_boxed_2804_, v_i_boxed_2805_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_as_2795_);
lean_dec(v___x_2794_);
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_ys_2788_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v_ys_2809_, lean_object* v___x_2810_, lean_object* v_recArgInfo_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v_group_2814_, lean_object* v_as_2815_, size_t v_sz_2816_, size_t v_i_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_a_2825_; uint8_t v___x_2829_; 
v___x_2829_ = lean_usize_dec_lt(v_i_2817_, v_sz_2816_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_b_2818_);
return v___x_2830_;
}
else
{
lean_object* v_snd_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2987_; 
v_snd_2831_ = lean_ctor_get(v_b_2818_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_b_2818_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_b_2818_, 0);
lean_dec(v_unused_2988_);
v___x_2833_ = v_b_2818_;
v_isShared_2834_ = v_isSharedCheck_2987_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snd_2831_);
lean_dec(v_b_2818_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2987_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v_next_2835_; lean_object* v_upperBound_2836_; lean_object* v___x_2837_; 
v_next_2835_ = lean_ctor_get(v_snd_2831_, 0);
lean_inc(v_next_2835_);
v_upperBound_2836_ = lean_ctor_get(v_snd_2831_, 1);
v___x_2837_ = lean_box(0);
if (lean_obj_tag(v_next_2835_) == 0)
{
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
goto v___jp_2838_;
}
else
{
lean_object* v_val_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2986_; 
v_val_2843_ = lean_ctor_get(v_next_2835_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_next_2835_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2845_ = v_next_2835_;
v_isShared_2846_ = v_isSharedCheck_2986_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_val_2843_);
lean_dec(v_next_2835_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2986_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_nat_dec_lt(v_val_2843_, v_upperBound_2836_);
if (v___x_2847_ == 0)
{
lean_del_object(v___x_2845_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
goto v___jp_2838_;
}
else
{
lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2983_; 
lean_inc(v_upperBound_2836_);
lean_del_object(v___x_2833_);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_snd_2831_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; lean_object* v_unused_2985_; 
v_unused_2984_ = lean_ctor_get(v_snd_2831_, 1);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_snd_2831_, 0);
lean_dec(v_unused_2985_);
v___x_2849_ = v_snd_2831_;
v_isShared_2850_ = v_isSharedCheck_2983_;
goto v_resetjp_2848_;
}
else
{
lean_dec(v_snd_2831_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2983_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
v_a_2851_ = lean_array_uget_borrowed(v_as_2815_, v_i_2817_);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_add(v_val_2843_, v___x_2852_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2853_);
v___x_2855_ = v___x_2845_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2855_);
v___x_2857_ = v___x_2849_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_upperBound_2836_);
v___x_2857_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; 
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc_ref(v___y_2819_);
lean_inc_ref(v___x_2807_);
v___x_2858_ = lean_infer_type(v___x_2807_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = l_Lean_Meta_whnfD(v_a_2859_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = 0;
lean_inc(v_a_2851_);
v___x_2863_ = l_Lean_Meta_forallMetaTelescope(v_a_2851_, v___x_2862_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v_snd_2865_; lean_object* v_fst_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2956_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v_snd_2865_ = lean_ctor_get(v_a_2864_, 1);
v_fst_2866_ = lean_ctor_get(v_a_2864_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_a_2864_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2868_ = v_a_2864_;
v_isShared_2869_ = v_isSharedCheck_2956_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_snd_2865_);
lean_inc(v_fst_2866_);
lean_dec(v_a_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2956_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_snd_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2954_; 
v_snd_2870_ = lean_ctor_get(v_snd_2865_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_snd_2865_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_snd_2865_, 0);
lean_dec(v_unused_2955_);
v___x_2872_ = v_snd_2865_;
v_isShared_2873_ = v_isSharedCheck_2954_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snd_2870_);
lean_dec(v_snd_2865_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2954_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2870_, v_a_2861_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; uint8_t v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = lean_unbox(v_a_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v_a_2875_);
lean_del_object(v___x_2868_);
lean_dec(v_fst_2866_);
lean_dec(v_val_2843_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2857_);
lean_ctor_set(v___x_2872_, 0, v___x_2837_);
v___x_2878_ = v___x_2872_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2857_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v_a_2825_ = v___x_2878_;
goto v___jp_2824_;
}
}
else
{
size_t v_sz_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v_sz_2880_ = lean_array_size(v_fst_2866_);
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2880_, v___x_2881_, v_fst_2866_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_array_get_size(v_a_2883_);
v___x_2931_ = lean_nat_dec_lt(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_dec(v_a_2875_);
lean_del_object(v___x_2868_);
goto v___jp_2884_;
}
else
{
if (v___x_2931_ == 0)
{
lean_dec(v_a_2875_);
lean_del_object(v___x_2868_);
goto v___jp_2884_;
}
else
{
size_t v___x_2932_; uint8_t v___x_2933_; uint8_t v___x_2934_; 
v___x_2932_ = lean_usize_of_nat(v___x_2930_);
v___x_2933_ = lean_unbox(v_a_2875_);
lean_dec(v_a_2875_);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2933_, v___x_2808_, v_a_2883_, v___x_2881_, v___x_2932_);
if (v___x_2934_ == 0)
{
lean_del_object(v___x_2868_);
goto v___jp_2884_;
}
else
{
lean_object* v___x_2936_; 
lean_dec(v_a_2883_);
lean_del_object(v___x_2872_);
lean_dec(v_val_2843_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2857_);
lean_ctor_set(v___x_2868_, 0, v___x_2837_);
v___x_2936_ = v___x_2868_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2857_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
v_a_2825_ = v___x_2936_;
goto v___jp_2824_;
}
}
}
}
v___jp_2884_:
{
uint8_t v___x_2885_; 
v___x_2885_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2883_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2887_; 
lean_dec(v_a_2883_);
lean_dec(v_val_2843_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2857_);
lean_ctor_set(v___x_2872_, 0, v___x_2837_);
v___x_2887_ = v___x_2872_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2857_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v_a_2825_ = v___x_2887_;
goto v___jp_2824_;
}
}
else
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2809_, v_a_2883_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2920_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2920_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2920_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
if (lean_obj_tag(v_a_2890_) == 1)
{
lean_object* v___x_2895_; 
lean_dec_ref_known(v_a_2890_, 1);
lean_del_object(v___x_2892_);
lean_dec(v_a_2883_);
lean_dec(v_val_2843_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2857_);
lean_ctor_set(v___x_2872_, 0, v___x_2837_);
v___x_2895_ = v___x_2872_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2857_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
v_a_2825_ = v___x_2895_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_fnName_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_a_2890_);
lean_dec_ref(v___x_2807_);
v_fnName_2897_ = lean_ctor_get(v_recArgInfo_2811_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_recArgInfo_2811_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; lean_object* v_unused_2919_; 
v_unused_2915_ = lean_ctor_get(v_recArgInfo_2811_, 5);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_recArgInfo_2811_, 4);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_recArgInfo_2811_, 3);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_recArgInfo_2811_, 2);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_recArgInfo_2811_, 1);
lean_dec(v_unused_2919_);
v___x_2899_ = v_recArgInfo_2811_;
v_isShared_2900_ = v_isSharedCheck_2914_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_fnName_2897_);
lean_dec(v_recArgInfo_2811_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2914_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
size_t v_sz_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v_sz_2901_ = lean_array_size(v_a_2883_);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2810_, v_sz_2901_, v___x_2881_, v_a_2883_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 5, v_val_2843_);
lean_ctor_set(v___x_2899_, 4, v_group_2814_);
lean_ctor_set(v___x_2899_, 3, v___x_2902_);
lean_ctor_set(v___x_2899_, 2, v___x_2813_);
lean_ctor_set(v___x_2899_, 1, v___x_2812_);
v___x_2904_ = v___x_2899_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_fnName_2897_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_group_2814_);
lean_ctor_set(v_reuseFailAlloc_2913_, 5, v_val_2843_);
v___x_2904_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2857_);
lean_ctor_set(v___x_2872_, 0, v___x_2906_);
v___x_2908_ = v___x_2872_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2857_);
v___x_2908_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2910_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2908_);
v___x_2910_ = v___x_2892_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_a_2883_);
lean_del_object(v___x_2872_);
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2921_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2889_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2889_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2875_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2938_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2882_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2882_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_fst_2866_);
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2946_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2874_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2874_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_a_2861_);
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2957_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2863_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2863_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2965_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2860_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2860_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___x_2857_);
lean_dec(v_val_2843_);
lean_dec_ref(v_group_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_recArgInfo_2811_);
lean_dec_ref(v___x_2807_);
v_a_2973_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2858_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2858_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
}
}
}
v___jp_2838_:
{
lean_object* v___x_2840_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2837_);
v___x_2840_ = v___x_2833_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_snd_2831_);
v___x_2840_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
}
}
v___jp_2824_:
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2817_, v___x_2826_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2807_, v_ys_2809_, v___x_2810_, v_recArgInfo_2811_, v___x_2812_, v___x_2813_, v_group_2814_, v___x_2808_, v_as_2815_, v_sz_2816_, v___x_2827_, v_a_2825_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2989_ = _args[0];
lean_object* v___x_2990_ = _args[1];
lean_object* v_ys_2991_ = _args[2];
lean_object* v___x_2992_ = _args[3];
lean_object* v_recArgInfo_2993_ = _args[4];
lean_object* v___x_2994_ = _args[5];
lean_object* v___x_2995_ = _args[6];
lean_object* v_group_2996_ = _args[7];
lean_object* v_as_2997_ = _args[8];
lean_object* v_sz_2998_ = _args[9];
lean_object* v_i_2999_ = _args[10];
lean_object* v_b_3000_ = _args[11];
lean_object* v___y_3001_ = _args[12];
lean_object* v___y_3002_ = _args[13];
lean_object* v___y_3003_ = _args[14];
lean_object* v___y_3004_ = _args[15];
lean_object* v___y_3005_ = _args[16];
_start:
{
size_t v_sz_boxed_3006_; size_t v_i_boxed_3007_; lean_object* v_res_3008_; 
v_sz_boxed_3006_ = lean_unbox_usize(v_sz_2998_);
lean_dec(v_sz_2998_);
v_i_boxed_3007_ = lean_unbox_usize(v_i_2999_);
lean_dec(v_i_2999_);
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2989_, v___x_2990_, v_ys_2991_, v___x_2992_, v_recArgInfo_2993_, v___x_2994_, v___x_2995_, v_group_2996_, v_as_2997_, v_sz_boxed_3006_, v_i_boxed_3007_, v_b_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v_as_2997_);
lean_dec_ref(v___x_2992_);
lean_dec_ref(v_ys_2991_);
lean_dec(v___x_2990_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3009_, lean_object* v_fixedParamPerm_3010_, lean_object* v_xs_3011_, lean_object* v___x_3012_, lean_object* v_recArgPos_3013_, lean_object* v_a_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v_ys_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_toIndGroupInfo_3024_; lean_object* v_all_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3063_; 
v_toIndGroupInfo_3024_ = lean_ctor_get(v_group_3009_, 0);
lean_inc_ref(v_toIndGroupInfo_3024_);
v_all_3025_ = lean_ctor_get(v_toIndGroupInfo_3024_, 0);
lean_inc_ref(v_ys_3017_);
lean_inc_ref(v_fixedParamPerm_3010_);
v___x_3026_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3010_, v_xs_3011_, v_ys_3017_);
v___x_3027_ = lean_array_get(v___x_3012_, v___x_3026_, v_recArgPos_3013_);
v___x_3028_ = lean_array_get_size(v_all_3025_);
v___x_3029_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3024_);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_toIndGroupInfo_3024_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; lean_object* v_unused_3065_; 
v_unused_3064_ = lean_ctor_get(v_toIndGroupInfo_3024_, 1);
lean_dec(v_unused_3064_);
v_unused_3065_ = lean_ctor_get(v_toIndGroupInfo_3024_, 0);
lean_dec(v_unused_3065_);
v___x_3031_ = v_toIndGroupInfo_3024_;
v_isShared_3032_ = v_isSharedCheck_3063_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v_toIndGroupInfo_3024_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3063_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3028_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 1, v___x_3029_);
lean_ctor_set(v___x_3031_, 0, v___x_3033_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3029_);
v___x_3035_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
v_sz_3038_ = lean_array_size(v_a_3014_);
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3027_, v___x_3015_, v_ys_3017_, v___x_3026_, v___x_3016_, v_fixedParamPerm_3010_, v_recArgPos_3013_, v_group_3009_, v_a_3014_, v_sz_3038_, v___x_3039_, v___x_3037_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec_ref(v___x_3026_);
lean_dec_ref(v_ys_3017_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3053_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3053_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3053_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_fst_3045_; 
v_fst_3045_ = lean_ctor_get(v_a_3041_, 0);
lean_inc(v_fst_3045_);
lean_dec(v_a_3041_);
if (lean_obj_tag(v_fst_3045_) == 0)
{
lean_object* v___x_3047_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3036_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3036_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
else
{
lean_object* v_val_3049_; lean_object* v___x_3051_; 
v_val_3049_ = lean_ctor_get(v_fst_3045_, 0);
lean_inc(v_val_3049_);
lean_dec_ref_known(v_fst_3045_, 1);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_val_3049_);
v___x_3051_ = v___x_3043_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_val_3049_);
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
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3040_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3040_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3066_, lean_object* v_fixedParamPerm_3067_, lean_object* v_xs_3068_, lean_object* v___x_3069_, lean_object* v_recArgPos_3070_, lean_object* v_a_3071_, lean_object* v___x_3072_, lean_object* v___x_3073_, lean_object* v_ys_3074_, lean_object* v_x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3066_, v_fixedParamPerm_3067_, v_xs_3068_, v___x_3069_, v_recArgPos_3070_, v_a_3071_, v___x_3072_, v___x_3073_, v_ys_3074_, v_x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_x_3075_);
lean_dec(v___x_3072_);
lean_dec_ref(v_a_3071_);
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_xs_3068_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3082_, lean_object* v_a_3083_, lean_object* v_xs_3084_, lean_object* v_value_3085_, lean_object* v_as_3086_, size_t v_i_3087_, size_t v_stop_3088_, lean_object* v_b_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_a_3096_; lean_object* v_val_3101_; uint8_t v___x_3103_; 
v___x_3103_ = lean_usize_dec_eq(v_i_3087_, v_stop_3088_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v_fixedParamPerm_3105_; lean_object* v_recArgPos_3106_; lean_object* v_indGroupInst_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3104_ = lean_array_uget_borrowed(v_as_3086_, v_i_3087_);
v_fixedParamPerm_3105_ = lean_ctor_get(v___x_3104_, 1);
v_recArgPos_3106_ = lean_ctor_get(v___x_3104_, 2);
v_indGroupInst_3107_ = lean_ctor_get(v___x_3104_, 4);
v___x_3108_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_indGroupInst_3107_);
lean_inc_ref(v_group_3082_);
v___x_3109_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3082_, v_indGroupInst_3107_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; uint8_t v___x_3111_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = lean_unbox(v_a_3110_);
lean_dec(v_a_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3112_ = lean_array_get_size(v_a_3083_);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_nat_dec_eq(v___x_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___f_3115_; lean_object* v___x_3116_; 
lean_inc(v___x_3104_);
lean_inc_ref(v_a_3083_);
lean_inc(v_recArgPos_3106_);
lean_inc_ref(v_xs_3084_);
lean_inc_ref(v_fixedParamPerm_3105_);
lean_inc_ref(v_group_3082_);
v___f_3115_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3115_, 0, v_group_3082_);
lean_closure_set(v___f_3115_, 1, v_fixedParamPerm_3105_);
lean_closure_set(v___f_3115_, 2, v_xs_3084_);
lean_closure_set(v___f_3115_, 3, v___x_3108_);
lean_closure_set(v___f_3115_, 4, v_recArgPos_3106_);
lean_closure_set(v___f_3115_, 5, v_a_3083_);
lean_closure_set(v___f_3115_, 6, v___x_3112_);
lean_closure_set(v___f_3115_, 7, v___x_3104_);
lean_inc_ref(v_value_3085_);
v___x_3116_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3085_, v___f_3115_, v___x_3114_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
if (lean_obj_tag(v_a_3117_) == 0)
{
v_a_3096_ = v_b_3089_;
goto v___jp_3095_;
}
else
{
lean_object* v_val_3118_; 
v_val_3118_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_val_3118_);
lean_dec_ref_known(v_a_3117_, 1);
v_val_3101_ = v_val_3118_;
goto v___jp_3100_;
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_b_3089_);
lean_dec_ref(v_value_3085_);
lean_dec_ref(v_xs_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_group_3082_);
v_a_3119_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3116_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3116_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
v_a_3096_ = v_b_3089_;
goto v___jp_3095_;
}
}
else
{
lean_inc(v___x_3104_);
v_val_3101_ = v___x_3104_;
goto v___jp_3100_;
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_b_3089_);
lean_dec_ref(v_value_3085_);
lean_dec_ref(v_xs_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_group_3082_);
v_a_3127_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3109_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3109_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v___x_3135_; 
lean_dec_ref(v_value_3085_);
lean_dec_ref(v_xs_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_group_3082_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_b_3089_);
return v___x_3135_;
}
v___jp_3095_:
{
size_t v___x_3097_; size_t v___x_3098_; 
v___x_3097_ = ((size_t)1ULL);
v___x_3098_ = lean_usize_add(v_i_3087_, v___x_3097_);
v_i_3087_ = v___x_3098_;
v_b_3089_ = v_a_3096_;
goto _start;
}
v___jp_3100_:
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_array_push(v_b_3089_, v_val_3101_);
v_a_3096_ = v___x_3102_;
goto v___jp_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3136_, lean_object* v_a_3137_, lean_object* v_xs_3138_, lean_object* v_value_3139_, lean_object* v_as_3140_, lean_object* v_i_3141_, lean_object* v_stop_3142_, lean_object* v_b_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
size_t v_i_boxed_3149_; size_t v_stop_boxed_3150_; lean_object* v_res_3151_; 
v_i_boxed_3149_ = lean_unbox_usize(v_i_3141_);
lean_dec(v_i_3141_);
v_stop_boxed_3150_ = lean_unbox_usize(v_stop_3142_);
lean_dec(v_stop_3142_);
v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3136_, v_a_3137_, v_xs_3138_, v_value_3139_, v_as_3140_, v_i_boxed_3149_, v_stop_boxed_3150_, v_b_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec_ref(v_as_3140_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3152_, lean_object* v_a_3153_, lean_object* v_xs_3154_, lean_object* v_value_3155_, lean_object* v_as_3156_, lean_object* v_start_3157_, lean_object* v_stop_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3165_ = lean_nat_dec_lt(v_start_3157_, v_stop_3158_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v_value_3155_);
lean_dec_ref(v_xs_3154_);
lean_dec_ref(v_a_3153_);
lean_dec_ref(v_group_3152_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = lean_array_get_size(v_as_3156_);
v___x_3168_ = lean_nat_dec_le(v_stop_3158_, v___x_3167_);
if (v___x_3168_ == 0)
{
uint8_t v___x_3169_; 
v___x_3169_ = lean_nat_dec_lt(v_start_3157_, v___x_3167_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref(v_value_3155_);
lean_dec_ref(v_xs_3154_);
lean_dec_ref(v_a_3153_);
lean_dec_ref(v_group_3152_);
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3164_);
return v___x_3170_;
}
else
{
size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_usize_of_nat(v_start_3157_);
v___x_3172_ = lean_usize_of_nat(v___x_3167_);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3152_, v_a_3153_, v_xs_3154_, v_value_3155_, v_as_3156_, v___x_3171_, v___x_3172_, v___x_3164_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3173_;
}
}
else
{
size_t v___x_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_usize_of_nat(v_start_3157_);
v___x_3175_ = lean_usize_of_nat(v_stop_3158_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3152_, v_a_3153_, v_xs_3154_, v_value_3155_, v_as_3156_, v___x_3174_, v___x_3175_, v___x_3164_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3177_, lean_object* v_a_3178_, lean_object* v_xs_3179_, lean_object* v_value_3180_, lean_object* v_as_3181_, lean_object* v_start_3182_, lean_object* v_stop_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3177_, v_a_3178_, v_xs_3179_, v_value_3180_, v_as_3181_, v_start_3182_, v_stop_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v_stop_3183_);
lean_dec(v_start_3182_);
lean_dec_ref(v_as_3181_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3190_, lean_object* v_xs_3191_, lean_object* v_value_3192_, lean_object* v_recArgInfos_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v___x_3199_; 
lean_inc_ref(v_group_3190_);
v___x_3199_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3190_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_array_get_size(v_recArgInfos_3193_);
v___x_3203_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3190_, v_a_3200_, v_xs_3191_, v_value_3192_, v_recArgInfos_3193_, v___x_3201_, v___x_3202_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
return v___x_3203_;
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v_value_3192_);
lean_dec_ref(v_xs_3191_);
lean_dec_ref(v_group_3190_);
v_a_3204_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3199_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3199_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3212_, lean_object* v_xs_3213_, lean_object* v_value_3214_, lean_object* v_recArgInfos_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Elab_Structural_argsInGroup(v_group_3212_, v_xs_3213_, v_value_3214_, v_recArgInfos_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec_ref(v_recArgInfos_3215_);
return v_res_3221_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_unsigned_to_nat(10u);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3225_, lean_object* v_i_3226_, lean_object* v_acc_3227_){
_start:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_array_get_size(v_xss_3225_);
v___x_3229_ = lean_nat_dec_lt(v_i_3226_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_unsigned_to_nat(1u);
v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
v___x_3232_ = lean_array_push(v___x_3231_, v_acc_3227_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3233_ = lean_array_fget_borrowed(v_xss_3225_, v_i_3226_);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3236_ = lean_array_get_size(v___x_3233_);
v___x_3237_ = lean_nat_dec_lt(v___x_3234_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec_ref(v_acc_3227_);
return v___x_3235_;
}
else
{
size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = lean_usize_of_nat(v___x_3236_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3226_, v_acc_3227_, v_xss_3225_, v___x_3233_, v___x_3238_, v___x_3239_, v___x_3235_);
return v___x_3240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3241_, lean_object* v_acc_3242_, lean_object* v_xss_3243_, lean_object* v_as_3244_, size_t v_i_3245_, size_t v_stop_3246_, lean_object* v_b_3247_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_eq(v_i_3245_, v_stop_3246_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; size_t v___x_3255_; size_t v___x_3256_; 
v___x_3249_ = lean_array_uget_borrowed(v_as_3244_, v_i_3245_);
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_nat_add(v_i_3241_, v___x_3250_);
lean_inc(v___x_3249_);
lean_inc_ref(v_acc_3242_);
v___x_3252_ = lean_array_push(v_acc_3242_, v___x_3249_);
v___x_3253_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3243_, v___x_3251_, v___x_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = l_Array_append___redArg(v_b_3247_, v___x_3253_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = ((size_t)1ULL);
v___x_3256_ = lean_usize_add(v_i_3245_, v___x_3255_);
v_i_3245_ = v___x_3256_;
v_b_3247_ = v___x_3254_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3242_);
return v_b_3247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3258_, lean_object* v_acc_3259_, lean_object* v_xss_3260_, lean_object* v_as_3261_, lean_object* v_i_3262_, lean_object* v_stop_3263_, lean_object* v_b_3264_){
_start:
{
size_t v_i_boxed_3265_; size_t v_stop_boxed_3266_; lean_object* v_res_3267_; 
v_i_boxed_3265_ = lean_unbox_usize(v_i_3262_);
lean_dec(v_i_3262_);
v_stop_boxed_3266_ = lean_unbox_usize(v_stop_3263_);
lean_dec(v_stop_3263_);
v_res_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3258_, v_acc_3259_, v_xss_3260_, v_as_3261_, v_i_boxed_3265_, v_stop_boxed_3266_, v_b_3264_);
lean_dec_ref(v_as_3261_);
lean_dec_ref(v_xss_3260_);
lean_dec(v_i_3258_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3268_, lean_object* v_i_3269_, lean_object* v_acc_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3268_, v_i_3269_, v_acc_3270_);
lean_dec(v_i_3269_);
lean_dec_ref(v_xss_3268_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3272_, lean_object* v_xss_3273_, lean_object* v_i_3274_, lean_object* v_acc_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3273_, v_i_3274_, v_acc_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3277_, lean_object* v_xss_3278_, lean_object* v_i_3279_, lean_object* v_acc_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3277_, v_xss_3278_, v_i_3279_, v_acc_3280_);
lean_dec(v_i_3279_);
lean_dec_ref(v_xss_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3282_, lean_object* v_i_3283_, lean_object* v_acc_3284_, lean_object* v_xss_3285_, lean_object* v_as_3286_, size_t v_i_3287_, size_t v_stop_3288_, lean_object* v_b_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3283_, v_acc_3284_, v_xss_3285_, v_as_3286_, v_i_3287_, v_stop_3288_, v_b_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3291_, lean_object* v_i_3292_, lean_object* v_acc_3293_, lean_object* v_xss_3294_, lean_object* v_as_3295_, lean_object* v_i_3296_, lean_object* v_stop_3297_, lean_object* v_b_3298_){
_start:
{
size_t v_i_boxed_3299_; size_t v_stop_boxed_3300_; lean_object* v_res_3301_; 
v_i_boxed_3299_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_stop_boxed_3300_ = lean_unbox_usize(v_stop_3297_);
lean_dec(v_stop_3297_);
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3291_, v_i_3292_, v_acc_3293_, v_xss_3294_, v_as_3295_, v_i_boxed_3299_, v_stop_boxed_3300_, v_b_3298_);
lean_dec_ref(v_as_3295_);
lean_dec_ref(v_xss_3294_);
lean_dec(v_i_3292_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3302_, size_t v_i_3303_, size_t v_stop_3304_, lean_object* v_b_3305_){
_start:
{
uint8_t v___x_3306_; 
v___x_3306_ = lean_usize_dec_eq(v_i_3303_, v_stop_3304_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; size_t v___x_3310_; size_t v___x_3311_; 
v___x_3307_ = lean_array_uget_borrowed(v_as_3302_, v_i_3303_);
v___x_3308_ = lean_array_get_size(v___x_3307_);
v___x_3309_ = lean_nat_mul(v_b_3305_, v___x_3308_);
lean_dec(v_b_3305_);
v___x_3310_ = ((size_t)1ULL);
v___x_3311_ = lean_usize_add(v_i_3303_, v___x_3310_);
v_i_3303_ = v___x_3311_;
v_b_3305_ = v___x_3309_;
goto _start;
}
else
{
return v_b_3305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3313_, lean_object* v_i_3314_, lean_object* v_stop_3315_, lean_object* v_b_3316_){
_start:
{
size_t v_i_boxed_3317_; size_t v_stop_boxed_3318_; lean_object* v_res_3319_; 
v_i_boxed_3317_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_stop_boxed_3318_ = lean_unbox_usize(v_stop_3315_);
lean_dec(v_stop_3315_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3313_, v_i_boxed_3317_, v_stop_boxed_3318_, v_b_3316_);
lean_dec_ref(v_as_3313_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___y_3325_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3321_ = lean_unsigned_to_nat(10u);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_array_get_size(v_xss_3320_);
v___x_3332_ = lean_nat_dec_lt(v___x_3323_, v___x_3331_);
if (v___x_3332_ == 0)
{
v___y_3325_ = v___x_3322_;
goto v___jp_3324_;
}
else
{
size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = lean_usize_of_nat(v___x_3331_);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3320_, v___x_3333_, v___x_3334_, v___x_3322_);
v___y_3325_ = v___x_3335_;
goto v___jp_3324_;
}
v___jp_3324_:
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_nat_dec_lt(v___x_3321_, v___y_3325_);
lean_dec(v___y_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3328_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3320_, v___x_3323_, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_box(0);
return v___x_3330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3336_);
lean_dec_ref(v_xss_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3338_, lean_object* v_xss_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3341_, lean_object* v_xss_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3341_, v_xss_3342_);
lean_dec_ref(v_xss_3342_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3344_, lean_object* v_as_3345_, size_t v_i_3346_, size_t v_stop_3347_, lean_object* v_b_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3345_, v_i_3346_, v_stop_3347_, v_b_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3350_, lean_object* v_as_3351_, lean_object* v_i_3352_, lean_object* v_stop_3353_, lean_object* v_b_3354_){
_start:
{
size_t v_i_boxed_3355_; size_t v_stop_boxed_3356_; lean_object* v_res_3357_; 
v_i_boxed_3355_ = lean_unbox_usize(v_i_3352_);
lean_dec(v_i_3352_);
v_stop_boxed_3356_ = lean_unbox_usize(v_stop_3353_);
lean_dec(v_stop_3353_);
v_res_3357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3350_, v_as_3351_, v_i_boxed_3355_, v_stop_boxed_3356_, v_b_3354_);
lean_dec_ref(v_as_3351_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3358_, size_t v_i_3359_, size_t v_stop_3360_, lean_object* v_b_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_usize_dec_eq(v_i_3359_, v_stop_3360_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; size_t v___x_3365_; size_t v___x_3366_; 
v___x_3363_ = lean_array_uget_borrowed(v_as_3358_, v_i_3359_);
v___x_3364_ = l_Array_append___redArg(v_b_3361_, v___x_3363_);
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3359_, v___x_3365_);
v_i_3359_ = v___x_3366_;
v_b_3361_ = v___x_3364_;
goto _start;
}
else
{
return v_b_3361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3368_, lean_object* v_i_3369_, lean_object* v_stop_3370_, lean_object* v_b_3371_){
_start:
{
size_t v_i_boxed_3372_; size_t v_stop_boxed_3373_; lean_object* v_res_3374_; 
v_i_boxed_3372_ = lean_unbox_usize(v_i_3369_);
lean_dec(v_i_3369_);
v_stop_boxed_3373_ = lean_unbox_usize(v_stop_3370_);
lean_dec(v_stop_3370_);
v_res_3374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3368_, v_i_boxed_3372_, v_stop_boxed_3373_, v_b_3371_);
lean_dec_ref(v_as_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
if (lean_obj_tag(v_a_3375_) == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = l_List_reverse___redArg(v_a_3376_);
return v___x_3377_;
}
else
{
lean_object* v_head_3378_; lean_object* v_tail_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3389_; 
v_head_3378_ = lean_ctor_get(v_a_3375_, 0);
v_tail_3379_ = lean_ctor_get(v_a_3375_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3375_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3381_ = v_a_3375_;
v_isShared_3382_ = v_isSharedCheck_3389_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_tail_3379_);
lean_inc(v_head_3378_);
lean_dec(v_a_3375_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3389_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3383_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3378_);
v___x_3384_ = l_Lean_MessageData_ofFormat(v___x_3383_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v_a_3376_);
lean_ctor_set(v___x_3381_, 0, v___x_3384_);
v___x_3386_ = v___x_3381_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_a_3376_);
v___x_3386_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v_a_3375_ = v_tail_3379_;
v_a_3376_ = v___x_3386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3390_, size_t v_i_3391_, lean_object* v_bs_3392_){
_start:
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_usize_dec_lt(v_i_3391_, v_sz_3390_);
if (v___x_3393_ == 0)
{
return v_bs_3392_;
}
else
{
lean_object* v_v_3394_; lean_object* v___x_3395_; lean_object* v_bs_x27_3396_; lean_object* v___x_3397_; size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_v_3394_ = lean_array_uget(v_bs_3392_, v_i_3391_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v_bs_x27_3396_ = lean_array_uset(v_bs_3392_, v_i_3391_, v___x_3395_);
v___x_3397_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3394_);
lean_dec(v_v_3394_);
v___x_3398_ = ((size_t)1ULL);
v___x_3399_ = lean_usize_add(v_i_3391_, v___x_3398_);
v___x_3400_ = lean_array_uset(v_bs_x27_3396_, v_i_3391_, v___x_3397_);
v_i_3391_ = v___x_3399_;
v_bs_3392_ = v___x_3400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3402_, lean_object* v_i_3403_, lean_object* v_bs_3404_){
_start:
{
size_t v_sz_boxed_3405_; size_t v_i_boxed_3406_; lean_object* v_res_3407_; 
v_sz_boxed_3405_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v_i_boxed_3406_ = lean_unbox_usize(v_i_3403_);
lean_dec(v_i_3403_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3405_, v_i_boxed_3406_, v_bs_3404_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3408_, lean_object* v_as_3409_, size_t v_sz_3410_, size_t v_i_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_usize_dec_lt(v_i_3411_, v_sz_3410_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec_ref(v_xs_3408_);
v___x_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_b_3412_);
return v___x_3419_;
}
else
{
lean_object* v_snd_3420_; lean_object* v_snd_3421_; lean_object* v_snd_3422_; lean_object* v_snd_3423_; lean_object* v_fst_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3568_; 
v_snd_3420_ = lean_ctor_get(v_b_3412_, 1);
lean_inc(v_snd_3420_);
v_snd_3421_ = lean_ctor_get(v_snd_3420_, 1);
lean_inc(v_snd_3421_);
v_snd_3422_ = lean_ctor_get(v_snd_3421_, 1);
lean_inc(v_snd_3422_);
v_snd_3423_ = lean_ctor_get(v_snd_3422_, 1);
lean_inc(v_snd_3423_);
v_fst_3424_ = lean_ctor_get(v_b_3412_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_b_3412_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_b_3412_, 1);
lean_dec(v_unused_3569_);
v___x_3426_ = v_b_3412_;
v_isShared_3427_ = v_isSharedCheck_3568_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_fst_3424_);
lean_dec(v_b_3412_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3568_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_fst_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3566_; 
v_fst_3428_ = lean_ctor_get(v_snd_3420_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_snd_3420_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_snd_3420_, 1);
lean_dec(v_unused_3567_);
v___x_3430_ = v_snd_3420_;
v_isShared_3431_ = v_isSharedCheck_3566_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_fst_3428_);
lean_dec(v_snd_3420_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3566_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_fst_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3564_; 
v_fst_3432_ = lean_ctor_get(v_snd_3421_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_snd_3421_, 1);
lean_dec(v_unused_3565_);
v___x_3434_ = v_snd_3421_;
v_isShared_3435_ = v_isSharedCheck_3564_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_fst_3432_);
lean_dec(v_snd_3421_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3564_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3562_; 
v_fst_3436_ = lean_ctor_get(v_snd_3422_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v_snd_3422_, 1);
lean_dec(v_unused_3563_);
v___x_3438_ = v_snd_3422_;
v_isShared_3439_ = v_isSharedCheck_3562_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_fst_3436_);
lean_dec(v_snd_3422_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3562_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_array_3440_; lean_object* v_start_3441_; lean_object* v_stop_3442_; uint8_t v___x_3443_; 
v_array_3440_ = lean_ctor_get(v_snd_3423_, 0);
v_start_3441_ = lean_ctor_get(v_snd_3423_, 1);
v_stop_3442_ = lean_ctor_get(v_snd_3423_, 2);
v___x_3443_ = lean_nat_dec_lt(v_start_3441_, v_stop_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3445_; 
lean_dec_ref(v_xs_3408_);
if (v_isShared_3439_ == 0)
{
v___x_3445_ = v___x_3438_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_snd_3423_);
v___x_3445_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3445_);
v___x_3447_ = v___x_3434_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3447_);
v___x_3449_ = v___x_3430_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___x_3449_);
v___x_3451_ = v___x_3426_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3558_; 
lean_inc(v_stop_3442_);
lean_inc(v_start_3441_);
lean_inc_ref(v_array_3440_);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_snd_3423_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; lean_object* v_unused_3560_; lean_object* v_unused_3561_; 
v_unused_3559_ = lean_ctor_get(v_snd_3423_, 2);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_snd_3423_, 1);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_snd_3423_, 0);
lean_dec(v_unused_3561_);
v___x_3458_ = v_snd_3423_;
v_isShared_3459_ = v_isSharedCheck_3558_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_snd_3423_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3558_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_array_3460_; lean_object* v_start_3461_; lean_object* v_stop_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v_array_3460_ = lean_ctor_get(v_fst_3436_, 0);
v_start_3461_ = lean_ctor_get(v_fst_3436_, 1);
v_stop_3462_ = lean_ctor_get(v_fst_3436_, 2);
v___x_3463_ = lean_array_fget(v_array_3440_, v_start_3441_);
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_nat_add(v_start_3441_, v___x_3464_);
lean_dec(v_start_3441_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v___x_3465_);
v___x_3467_ = v___x_3458_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_array_3440_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_stop_3442_);
v___x_3467_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
uint8_t v___x_3468_; 
v___x_3468_ = lean_nat_dec_lt(v_start_3461_, v_stop_3462_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3470_; 
lean_dec(v___x_3463_);
lean_dec_ref(v_xs_3408_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3467_);
v___x_3470_ = v___x_3438_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3467_);
v___x_3470_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3470_);
v___x_3472_ = v___x_3434_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3472_);
v___x_3474_ = v___x_3430_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___x_3474_);
v___x_3476_ = v___x_3426_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
}
}
}
else
{
lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3553_; 
lean_inc(v_stop_3462_);
lean_inc(v_start_3461_);
lean_inc_ref(v_array_3460_);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_fst_3436_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3554_ = lean_ctor_get(v_fst_3436_, 2);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_fst_3436_, 1);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_fst_3436_, 0);
lean_dec(v_unused_3556_);
v___x_3483_ = v_fst_3436_;
v_isShared_3484_ = v_isSharedCheck_3553_;
goto v_resetjp_3482_;
}
else
{
lean_dec(v_fst_3436_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3553_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_array_3485_; lean_object* v_start_3486_; lean_object* v_stop_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v_array_3485_ = lean_ctor_get(v_fst_3432_, 0);
v_start_3486_ = lean_ctor_get(v_fst_3432_, 1);
v_stop_3487_ = lean_ctor_get(v_fst_3432_, 2);
v___x_3488_ = lean_array_fget(v_array_3460_, v_start_3461_);
v___x_3489_ = lean_nat_add(v_start_3461_, v___x_3464_);
lean_dec(v_start_3461_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v___x_3489_);
v___x_3491_ = v___x_3483_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_array_3460_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_stop_3462_);
v___x_3491_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
uint8_t v___x_3492_; 
v___x_3492_ = lean_nat_dec_lt(v_start_3486_, v_stop_3487_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3494_; 
lean_dec(v___x_3488_);
lean_dec(v___x_3463_);
lean_dec_ref(v_xs_3408_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3467_);
lean_ctor_set(v___x_3438_, 0, v___x_3491_);
v___x_3494_ = v___x_3438_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3467_);
v___x_3494_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3494_);
v___x_3496_ = v___x_3434_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3498_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3496_);
v___x_3498_ = v___x_3430_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___x_3498_);
v___x_3500_ = v___x_3426_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
return v___x_3501_;
}
}
}
}
}
else
{
lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3548_; 
lean_inc(v_stop_3487_);
lean_inc(v_start_3486_);
lean_inc_ref(v_array_3485_);
lean_del_object(v___x_3426_);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_fst_3432_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; lean_object* v_unused_3550_; lean_object* v_unused_3551_; 
v_unused_3549_ = lean_ctor_get(v_fst_3432_, 2);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_fst_3432_, 1);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_fst_3432_, 0);
lean_dec(v_unused_3551_);
v___x_3507_ = v_fst_3432_;
v_isShared_3508_ = v_isSharedCheck_3548_;
goto v_resetjp_3506_;
}
else
{
lean_dec(v_fst_3432_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3548_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v_a_3509_ = lean_array_uget_borrowed(v_as_3409_, v_i_3411_);
v___x_3510_ = lean_array_fget(v_array_3485_, v_start_3486_);
v___x_3511_ = lean_nat_add(v_start_3486_, v___x_3464_);
lean_dec(v_start_3486_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3511_);
v___x_3513_ = v___x_3507_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_array_3485_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_stop_3487_);
v___x_3513_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; 
lean_inc_ref(v_xs_3408_);
lean_inc(v_a_3509_);
v___x_3514_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3509_, v___x_3463_, v_xs_3408_, v___x_3510_, v___x_3488_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3538_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v_fst_3516_ = lean_ctor_get(v_a_3515_, 0);
v_snd_3517_ = lean_ctor_get(v_a_3515_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3519_ = v_a_3515_;
v_isShared_3520_ = v_isSharedCheck_3538_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_a_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3538_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_fst_3424_);
lean_ctor_set(v___x_3521_, 1, v_snd_3517_);
v___x_3522_ = lean_array_push(v_fst_3428_, v_fst_3516_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3467_);
lean_ctor_set(v___x_3519_, 0, v___x_3491_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3467_);
v___x_3524_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3524_);
lean_ctor_set(v___x_3438_, 0, v___x_3513_);
v___x_3526_ = v___x_3438_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3526_);
lean_ctor_set(v___x_3434_, 0, v___x_3522_);
v___x_3528_ = v___x_3434_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3528_);
lean_ctor_set(v___x_3430_, 0, v___x_3521_);
v___x_3530_ = v___x_3430_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
size_t v___x_3531_; size_t v___x_3532_; 
v___x_3531_ = ((size_t)1ULL);
v___x_3532_ = lean_usize_add(v_i_3411_, v___x_3531_);
v_i_3411_ = v___x_3532_;
v_b_3412_ = v___x_3530_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v___x_3513_);
lean_dec_ref(v___x_3491_);
lean_dec_ref(v___x_3467_);
lean_del_object(v___x_3438_);
lean_del_object(v___x_3434_);
lean_del_object(v___x_3430_);
lean_dec(v_fst_3428_);
lean_dec(v_fst_3424_);
lean_dec_ref(v_xs_3408_);
v_a_3539_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3514_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3514_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3570_, lean_object* v_as_3571_, lean_object* v_sz_3572_, lean_object* v_i_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
size_t v_sz_boxed_3580_; size_t v_i_boxed_3581_; lean_object* v_res_3582_; 
v_sz_boxed_3580_ = lean_unbox_usize(v_sz_3572_);
lean_dec(v_sz_3572_);
v_i_boxed_3581_ = lean_unbox_usize(v_i_3573_);
lean_dec(v_i_3573_);
v_res_3582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3570_, v_as_3571_, v_sz_boxed_3580_, v_i_boxed_3581_, v_b_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v_as_3571_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
if (lean_obj_tag(v_a_3583_) == 0)
{
lean_object* v___x_3585_; 
v___x_3585_ = l_List_reverse___redArg(v_a_3584_);
return v___x_3585_;
}
else
{
lean_object* v_head_3586_; lean_object* v_tail_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3596_; 
v_head_3586_ = lean_ctor_get(v_a_3583_, 0);
v_tail_3587_ = lean_ctor_get(v_a_3583_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3589_ = v_a_3583_;
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_tail_3587_);
lean_inc(v_head_3586_);
lean_dec(v_a_3583_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3586_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v_a_3584_);
lean_ctor_set(v___x_3589_, 0, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_a_3584_);
v___x_3593_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
v_a_3583_ = v_tail_3587_;
v_a_3584_ = v___x_3593_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3597_, lean_object* v_j_3598_){
_start:
{
lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3599_ = lean_array_get_size(v_as_3597_);
v___x_3600_ = lean_nat_dec_lt(v_j_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; 
lean_dec(v_j_3598_);
v___x_3601_ = lean_box(0);
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3602_ = lean_array_fget_borrowed(v_as_3597_, v_j_3598_);
v___x_3603_ = lean_array_get_size(v___x_3602_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = lean_nat_dec_eq(v___x_3603_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_unsigned_to_nat(1u);
v___x_3607_ = lean_nat_add(v_j_3598_, v___x_3606_);
lean_dec(v_j_3598_);
v_j_3598_ = v___x_3607_;
goto _start;
}
else
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_j_3598_);
return v___x_3609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3610_, lean_object* v_j_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3610_, v_j_3611_);
lean_dec_ref(v_as_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3613_, lean_object* v_as_3614_, size_t v_sz_3615_, size_t v_i_3616_, lean_object* v_b_3617_){
_start:
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_usize_dec_lt(v_i_3616_, v_sz_3615_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref(v_a_3613_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v_b_3617_);
return v___x_3620_;
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; size_t v___x_3624_; size_t v___x_3625_; 
v_a_3621_ = lean_array_uget_borrowed(v_as_3614_, v_i_3616_);
lean_inc(v_a_3621_);
lean_inc_ref(v_a_3613_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v_a_3613_);
lean_ctor_set(v___x_3622_, 1, v_a_3621_);
v___x_3623_ = lean_array_push(v_b_3617_, v___x_3622_);
v___x_3624_ = ((size_t)1ULL);
v___x_3625_ = lean_usize_add(v_i_3616_, v___x_3624_);
v_i_3616_ = v___x_3625_;
v_b_3617_ = v___x_3623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3627_, lean_object* v_as_3628_, lean_object* v_sz_3629_, lean_object* v_i_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_){
_start:
{
size_t v_sz_boxed_3633_; size_t v_i_boxed_3634_; lean_object* v_res_3635_; 
v_sz_boxed_3633_ = lean_unbox_usize(v_sz_3629_);
lean_dec(v_sz_3629_);
v_i_boxed_3634_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3627_, v_as_3628_, v_sz_boxed_3633_, v_i_boxed_3634_, v_b_3631_);
lean_dec_ref(v_as_3628_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3636_, lean_object* v_xs_3637_, lean_object* v_as_3638_, size_t v_sz_3639_, size_t v_i_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_usize_dec_lt(v_i_3640_, v_sz_3639_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; 
lean_dec_ref(v_xs_3637_);
lean_dec_ref(v_a_3636_);
v___x_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_b_3641_);
return v___x_3648_;
}
else
{
lean_object* v_snd_3649_; lean_object* v_fst_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3693_; 
v_snd_3649_ = lean_ctor_get(v_b_3641_, 1);
v_fst_3650_ = lean_ctor_get(v_b_3641_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_b_3641_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3652_ = v_b_3641_;
v_isShared_3653_ = v_isSharedCheck_3693_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_snd_3649_);
lean_inc(v_fst_3650_);
lean_dec(v_b_3641_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3693_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_array_3654_; lean_object* v_start_3655_; lean_object* v_stop_3656_; uint8_t v___x_3657_; 
v_array_3654_ = lean_ctor_get(v_snd_3649_, 0);
v_start_3655_ = lean_ctor_get(v_snd_3649_, 1);
v_stop_3656_ = lean_ctor_get(v_snd_3649_, 2);
v___x_3657_ = lean_nat_dec_lt(v_start_3655_, v_stop_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3659_; 
lean_dec_ref(v_xs_3637_);
lean_dec_ref(v_a_3636_);
if (v_isShared_3653_ == 0)
{
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_fst_3650_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_snd_3649_);
v___x_3659_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
}
else
{
lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3689_; 
lean_inc(v_stop_3656_);
lean_inc(v_start_3655_);
lean_inc_ref(v_array_3654_);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_snd_3649_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; 
v_unused_3690_ = lean_ctor_get(v_snd_3649_, 2);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_snd_3649_, 1);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_snd_3649_, 0);
lean_dec(v_unused_3692_);
v___x_3663_ = v_snd_3649_;
v_isShared_3664_ = v_isSharedCheck_3689_;
goto v_resetjp_3662_;
}
else
{
lean_dec(v_snd_3649_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3689_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v_a_3665_ = lean_array_uget_borrowed(v_as_3638_, v_i_3640_);
v___x_3666_ = lean_array_fget(v_array_3654_, v_start_3655_);
v___x_3667_ = lean_unsigned_to_nat(1u);
v___x_3668_ = lean_nat_add(v_start_3655_, v___x_3667_);
lean_dec(v_start_3655_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3668_);
v___x_3670_ = v___x_3663_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_array_3654_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_stop_3656_);
v___x_3670_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; 
lean_inc(v_a_3665_);
lean_inc_ref(v_xs_3637_);
lean_inc_ref(v_a_3636_);
v___x_3671_ = l_Lean_Elab_Structural_argsInGroup(v_a_3636_, v_xs_3637_, v_a_3665_, v___x_3666_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___x_3666_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___x_3673_ = lean_array_push(v_fst_3650_, v_a_3672_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v___x_3670_);
lean_ctor_set(v___x_3652_, 0, v___x_3673_);
v___x_3675_ = v___x_3652_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3670_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
size_t v___x_3676_; size_t v___x_3677_; 
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_add(v_i_3640_, v___x_3676_);
v_i_3640_ = v___x_3677_;
v_b_3641_ = v___x_3675_;
goto _start;
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v___x_3670_);
lean_del_object(v___x_3652_);
lean_dec(v_fst_3650_);
lean_dec_ref(v_xs_3637_);
lean_dec_ref(v_a_3636_);
v_a_3680_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3694_, lean_object* v_xs_3695_, lean_object* v_as_3696_, lean_object* v_sz_3697_, lean_object* v_i_3698_, lean_object* v_b_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
size_t v_sz_boxed_3705_; size_t v_i_boxed_3706_; lean_object* v_res_3707_; 
v_sz_boxed_3705_ = lean_unbox_usize(v_sz_3697_);
lean_dec(v_sz_3697_);
v_i_boxed_3706_ = lean_unbox_usize(v_i_3698_);
lean_dec(v_i_3698_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3694_, v_xs_3695_, v_as_3696_, v_sz_boxed_3705_, v_i_boxed_3706_, v_b_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_as_3696_);
return v_res_3707_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3715_ = l_Lean_stringToMessageData(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3724_ = l_Lean_stringToMessageData(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3728_, lean_object* v_values_3729_, lean_object* v_xs_3730_, lean_object* v_fnNames_3731_, lean_object* v_as_3732_, size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_b_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_a_3742_; uint8_t v___x_3746_; 
v___x_3746_ = lean_usize_dec_lt(v_i_3734_, v_sz_3733_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v_xs_3730_);
lean_dec_ref(v___x_3728_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v_b_3735_);
return v___x_3747_;
}
else
{
lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3823_; 
v_fst_3748_ = lean_ctor_get(v_b_3735_, 0);
v_snd_3749_ = lean_ctor_get(v_b_3735_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_b_3735_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3751_ = v_b_3735_;
v_isShared_3752_ = v_isSharedCheck_3823_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_snd_3749_);
lean_inc(v_fst_3748_);
lean_dec(v_b_3735_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3823_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v_recArgInfoss_3754_; lean_object* v___x_3755_; lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3755_ = lean_box(0);
v_a_3756_ = lean_array_uget_borrowed(v_as_3732_, v_i_3734_);
v___x_3757_ = lean_array_get_size(v___x_3728_);
lean_inc_ref(v___x_3728_);
v___x_3758_ = l_Array_toSubarray___redArg(v___x_3728_, v___x_3753_, v___x_3757_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v___x_3758_);
lean_ctor_set(v___x_3751_, 0, v_recArgInfoss_3754_);
v___x_3760_ = v___x_3751_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_recArgInfoss_3754_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
size_t v_sz_3761_; size_t v___x_3762_; lean_object* v___x_3763_; 
v_sz_3761_ = lean_array_size(v_values_3729_);
v___x_3762_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3730_);
lean_inc(v_a_3756_);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3756_, v_xs_3730_, v_values_3729_, v_sz_3761_, v___x_3762_, v___x_3760_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v_fst_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3812_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v_fst_3765_ = lean_ctor_get(v_a_3764_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3764_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; 
v_unused_3813_ = lean_ctor_get(v_a_3764_, 1);
lean_dec(v_unused_3813_);
v___x_3767_ = v_a_3764_;
v_isShared_3768_ = v_isSharedCheck_3812_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_fst_3765_);
lean_dec(v_a_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3812_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3765_, v___x_3753_);
if (lean_obj_tag(v___x_3769_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
lean_dec(v_fst_3765_);
v_val_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3770_);
lean_dec_ref_known(v___x_3769_, 1);
v___x_3771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3756_);
v___x_3772_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3756_);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_array_get_borrowed(v___x_3755_, v_fnNames_3731_, v_val_3770_);
lean_dec(v_val_3770_);
lean_inc(v___x_3776_);
v___x_3777_ = l_Lean_MessageData_ofName(v___x_3776_);
v___x_3778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3775_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v_fst_3748_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_snd_3749_);
lean_ctor_set(v___x_3767_, 0, v___x_3781_);
v___x_3783_ = v___x_3767_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3749_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v_a_3742_ = v___x_3783_;
goto v___jp_3741_;
}
}
else
{
lean_object* v___x_3785_; 
lean_dec(v___x_3769_);
v___x_3785_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3765_);
lean_dec(v_fst_3765_);
if (lean_obj_tag(v___x_3785_) == 1)
{
lean_object* v_val_3786_; size_t v_sz_3787_; lean_object* v___x_3788_; 
v_val_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v_sz_3787_ = lean_array_size(v_val_3786_);
lean_inc(v_a_3756_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3756_, v_val_3786_, v_sz_3787_, v___x_3762_, v_snd_3749_);
lean_dec(v_val_3786_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_a_3789_);
lean_ctor_set(v___x_3767_, 0, v_fst_3748_);
v___x_3791_ = v___x_3767_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_fst_3748_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_a_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v_a_3742_ = v___x_3791_;
goto v___jp_3741_;
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_del_object(v___x_3767_);
lean_dec(v_fst_3748_);
lean_dec_ref(v_xs_3730_);
lean_dec_ref(v___x_3728_);
v_a_3793_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3788_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3788_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
lean_dec(v___x_3785_);
v___x_3801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3756_);
v___x_3802_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3756_);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v_fst_3748_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_snd_3749_);
lean_ctor_set(v___x_3767_, 0, v___x_3808_);
v___x_3810_ = v___x_3767_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_snd_3749_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v_a_3742_ = v___x_3810_;
goto v___jp_3741_;
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_snd_3749_);
lean_dec(v_fst_3748_);
lean_dec_ref(v_xs_3730_);
lean_dec_ref(v___x_3728_);
v_a_3814_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3763_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3763_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
}
v___jp_3741_:
{
size_t v___x_3743_; size_t v___x_3744_; 
v___x_3743_ = ((size_t)1ULL);
v___x_3744_ = lean_usize_add(v_i_3734_, v___x_3743_);
v_i_3734_ = v___x_3744_;
v_b_3735_ = v_a_3742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3824_, lean_object* v_values_3825_, lean_object* v_xs_3826_, lean_object* v_fnNames_3827_, lean_object* v_as_3828_, lean_object* v_sz_3829_, lean_object* v_i_3830_, lean_object* v_b_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
size_t v_sz_boxed_3837_; size_t v_i_boxed_3838_; lean_object* v_res_3839_; 
v_sz_boxed_3837_ = lean_unbox_usize(v_sz_3829_);
lean_dec(v_sz_3829_);
v_i_boxed_3838_ = lean_unbox_usize(v_i_3830_);
lean_dec(v_i_3830_);
v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3824_, v_values_3825_, v_xs_3826_, v_fnNames_3827_, v_as_3828_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_as_3828_);
lean_dec_ref(v_fnNames_3827_);
lean_dec_ref(v_values_3825_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3840_, lean_object* v___x_3841_, lean_object* v_values_3842_, lean_object* v_fnNames_3843_, lean_object* v_as_3844_, size_t v_sz_3845_, size_t v_i_3846_, lean_object* v_b_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_a_3854_; uint8_t v___x_3858_; 
v___x_3858_ = lean_usize_dec_lt(v_i_3846_, v_sz_3845_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
lean_dec_ref(v___x_3841_);
lean_dec_ref(v_xs_3840_);
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_b_3847_);
return v___x_3859_;
}
else
{
lean_object* v_fst_3860_; lean_object* v_snd_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3935_; 
v_fst_3860_ = lean_ctor_get(v_b_3847_, 0);
v_snd_3861_ = lean_ctor_get(v_b_3847_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_b_3847_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3863_ = v_b_3847_;
v_isShared_3864_ = v_isSharedCheck_3935_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_snd_3861_);
lean_inc(v_fst_3860_);
lean_dec(v_b_3847_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3935_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v_recArgInfoss_3866_; lean_object* v___x_3867_; lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3867_ = lean_box(0);
v_a_3868_ = lean_array_uget_borrowed(v_as_3844_, v_i_3846_);
v___x_3869_ = lean_array_get_size(v___x_3841_);
lean_inc_ref(v___x_3841_);
v___x_3870_ = l_Array_toSubarray___redArg(v___x_3841_, v___x_3865_, v___x_3869_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v___x_3870_);
lean_ctor_set(v___x_3863_, 0, v_recArgInfoss_3866_);
v___x_3872_ = v___x_3863_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_recArgInfoss_3866_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
size_t v_sz_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v_sz_3873_ = lean_array_size(v_values_3842_);
v___x_3874_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3840_);
lean_inc(v_a_3868_);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3868_, v_xs_3840_, v_values_3842_, v_sz_3873_, v___x_3874_, v___x_3872_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v_fst_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3924_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v_fst_3877_ = lean_ctor_get(v_a_3876_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_a_3876_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v_a_3876_, 1);
lean_dec(v_unused_3925_);
v___x_3879_ = v_a_3876_;
v_isShared_3880_ = v_isSharedCheck_3924_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_fst_3877_);
lean_dec(v_a_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3924_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3877_, v___x_3865_);
if (lean_obj_tag(v___x_3881_) == 1)
{
lean_object* v_val_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
lean_dec(v_fst_3877_);
v_val_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3868_);
v___x_3884_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3868_);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_array_get_borrowed(v___x_3867_, v_fnNames_3843_, v_val_3882_);
lean_dec(v_val_3882_);
lean_inc(v___x_3888_);
v___x_3889_ = l_Lean_MessageData_ofName(v___x_3888_);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3887_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_fst_3860_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_snd_3861_);
lean_ctor_set(v___x_3879_, 0, v___x_3893_);
v___x_3895_ = v___x_3879_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_snd_3861_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
v_a_3854_ = v___x_3895_;
goto v___jp_3853_;
}
}
else
{
lean_object* v___x_3897_; 
lean_dec(v___x_3881_);
v___x_3897_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3877_);
lean_dec(v_fst_3877_);
if (lean_obj_tag(v___x_3897_) == 1)
{
lean_object* v_val_3898_; size_t v_sz_3899_; lean_object* v___x_3900_; 
v_val_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v_sz_3899_ = lean_array_size(v_val_3898_);
lean_inc(v_a_3868_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3868_, v_val_3898_, v_sz_3899_, v___x_3874_, v_snd_3861_);
lean_dec(v_val_3898_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_a_3901_);
lean_ctor_set(v___x_3879_, 0, v_fst_3860_);
v___x_3903_ = v___x_3879_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_fst_3860_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_a_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
v_a_3854_ = v___x_3903_;
goto v___jp_3853_;
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3879_);
lean_dec(v_fst_3860_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v_xs_3840_);
v_a_3905_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3900_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3900_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec(v___x_3897_);
v___x_3913_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3868_);
v___x_3914_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3868_);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v_fst_3860_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_snd_3861_);
lean_ctor_set(v___x_3879_, 0, v___x_3920_);
v___x_3922_ = v___x_3879_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_snd_3861_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
v_a_3854_ = v___x_3922_;
goto v___jp_3853_;
}
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_snd_3861_);
lean_dec(v_fst_3860_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v_xs_3840_);
v_a_3926_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3875_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3875_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
v___jp_3853_:
{
size_t v___x_3855_; size_t v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = ((size_t)1ULL);
v___x_3856_ = lean_usize_add(v_i_3846_, v___x_3855_);
v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3841_, v_values_3842_, v_xs_3840_, v_fnNames_3843_, v_as_3844_, v_sz_3845_, v___x_3856_, v_a_3854_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3936_, lean_object* v___x_3937_, lean_object* v_values_3938_, lean_object* v_fnNames_3939_, lean_object* v_as_3940_, lean_object* v_sz_3941_, lean_object* v_i_3942_, lean_object* v_b_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
size_t v_sz_boxed_3949_; size_t v_i_boxed_3950_; lean_object* v_res_3951_; 
v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3941_);
lean_dec(v_sz_3941_);
v_i_boxed_3950_ = lean_unbox_usize(v_i_3942_);
lean_dec(v_i_3942_);
v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3936_, v___x_3937_, v_values_3938_, v_fnNames_3939_, v_as_3940_, v_sz_boxed_3949_, v_i_boxed_3950_, v_b_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v_as_3940_);
lean_dec_ref(v_fnNames_3939_);
lean_dec_ref(v_values_3938_);
return v_res_3951_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__2));
v___x_3958_ = l_Lean_MessageData_ofFormat(v___x_3957_);
return v___x_3958_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__4));
v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
return v___x_3961_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__7));
v___x_3966_ = l_Lean_stringToMessageData(v___x_3965_);
return v___x_3966_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_box(1);
v___x_3968_ = l_Lean_MessageData_ofFormat(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3969_, lean_object* v_fixedParamPerms_3970_, lean_object* v_xs_3971_, lean_object* v_values_3972_, lean_object* v_termMeasure_x3fs_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3979_; lean_object* v_candidates_3980_; lean_object* v___x_3981_; lean_object* v_perms_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v_report_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; size_t v_sz_3993_; size_t v___x_3994_; lean_object* v___x_3995_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v_candidates_3980_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__0));
v___x_3981_ = lean_array_get_size(v_values_3972_);
v_perms_3982_ = lean_ctor_get(v_fixedParamPerms_3970_, 1);
lean_inc_ref(v_perms_3982_);
lean_dec_ref(v_fixedParamPerms_3970_);
lean_inc_ref(v_values_3972_);
v___x_3983_ = l_Array_toSubarray___redArg(v_values_3972_, v___x_3979_, v___x_3981_);
v___x_3984_ = lean_array_get_size(v_termMeasure_x3fs_3973_);
v_report_3985_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3986_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3973_, v___x_3979_, v___x_3984_);
v___x_3987_ = lean_array_get_size(v_perms_3982_);
v___x_3988_ = l_Array_toSubarray___redArg(v_perms_3982_, v___x_3979_, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3986_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3983_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_candidates_3980_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v_report_3985_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v_sz_3993_ = lean_array_size(v_fnNames_3969_);
v___x_3994_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3971_);
v___x_3995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3971_, v_fnNames_3969_, v_sz_3993_, v___x_3994_, v___x_3992_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v_snd_3997_; lean_object* v_toCold_3998_; lean_object* v_options_3999_; lean_object* v_fst_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4138_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
v_snd_3997_ = lean_ctor_get(v_a_3996_, 1);
lean_inc(v_snd_3997_);
v_toCold_3998_ = lean_ctor_get(v_a_3976_, 0);
v_options_3999_ = lean_ctor_get(v_toCold_3998_, 2);
v_fst_4000_ = lean_ctor_get(v_a_3996_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_a_3996_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_a_3996_, 1);
lean_dec(v_unused_4139_);
v___x_4002_ = v_a_3996_;
v_isShared_4003_ = v_isSharedCheck_4138_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_fst_4000_);
lean_dec(v_a_3996_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4138_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v_fst_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4136_; 
v_fst_4004_ = lean_ctor_get(v_snd_3997_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_snd_3997_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v_snd_3997_, 1);
lean_dec(v_unused_4137_);
v___x_4006_ = v_snd_3997_;
v_isShared_4007_ = v_isSharedCheck_4136_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_fst_4004_);
lean_dec(v_snd_3997_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4136_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v_inheritedTraceOptions_4008_; uint8_t v_hasTrace_4009_; size_t v_sz_4010_; lean_object* v___x_4011_; lean_object* v___y_4013_; lean_object* v_report_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___x_4061_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; 
v_inheritedTraceOptions_4008_ = lean_ctor_get(v_toCold_3998_, 11);
v_hasTrace_4009_ = lean_ctor_get_uint8(v_options_3999_, sizeof(void*)*1);
v_sz_4010_ = lean_array_size(v_fst_4004_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4010_, v___x_3994_, v_fst_4004_);
v___x_4061_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4009_ == 0)
{
v___y_4101_ = v_a_3974_;
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4110_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4008_, v_options_3999_, v___x_4110_);
if (v___x_4111_ == 0)
{
v___y_4101_ = v_a_3974_;
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4112_; lean_object* v___y_4114_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4132_ = lean_array_get_size(v___x_4011_);
v___x_4133_ = lean_nat_dec_lt(v___x_3979_, v___x_4132_);
if (v___x_4133_ == 0)
{
v___y_4114_ = v___x_4131_;
goto v___jp_4113_;
}
else
{
size_t v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_usize_of_nat(v___x_4132_);
v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4011_, v___x_3994_, v___x_4134_, v___x_4131_);
v___y_4114_ = v___x_4135_;
goto v___jp_4113_;
}
v___jp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4115_ = lean_array_to_list(v___y_4114_);
v___x_4116_ = lean_box(0);
v___x_4117_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4115_, v___x_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__9, &l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9);
v___x_4119_ = l_Lean_MessageData_joinSep(v___x_4117_, v___x_4118_);
v___x_4120_ = l_Lean_indentD(v___x_4119_);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4112_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4061_, v___x_4121_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_dec_ref_known(v___x_4122_, 1);
v___y_4101_ = v_a_3974_;
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
goto v___jp_4100_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref(v___x_4011_);
lean_del_object(v___x_4006_);
lean_del_object(v___x_4002_);
lean_dec(v_fst_4000_);
lean_dec_ref(v_values_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
}
v___jp_4012_:
{
lean_object* v___x_4020_; 
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 1, v_candidates_3980_);
lean_ctor_set(v___x_4006_, 0, v_report_4014_);
v___x_4020_ = v___x_4006_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_report_4014_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v_candidates_3980_);
v___x_4020_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
size_t v_sz_4021_; lean_object* v___x_4022_; 
v_sz_4021_ = lean_array_size(v___y_4013_);
v___x_4022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3971_, v___x_4011_, v_values_3972_, v_fnNames_3969_, v___y_4013_, v_sz_4021_, v___x_3994_, v___x_4020_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v_values_3972_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4039_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4039_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4039_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v_fst_4027_; lean_object* v_snd_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4038_; 
v_fst_4027_ = lean_ctor_get(v_a_4023_, 0);
v_snd_4028_ = lean_ctor_get(v_a_4023_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_a_4023_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4030_ = v_a_4023_;
v_isShared_4031_ = v_isSharedCheck_4038_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_snd_4028_);
lean_inc(v_fst_4027_);
lean_dec(v_a_4023_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4038_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v_fst_4027_);
lean_ctor_set(v___x_4030_, 0, v_snd_4028_);
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_snd_4028_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_fst_4027_);
v___x_4033_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4035_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4033_);
v___x_4035_ = v___x_4025_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4022_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4022_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
v___jp_4049_:
{
lean_object* v___x_4055_; uint8_t v___x_4056_; 
v___x_4055_ = lean_array_get_size(v___y_4050_);
v___x_4056_ = lean_nat_dec_eq(v___x_4055_, v___x_3979_);
if (v___x_4056_ == 0)
{
lean_del_object(v___x_4002_);
v___y_4013_ = v___y_4050_;
v_report_4014_ = v_fst_4000_;
v___y_4015_ = v___y_4051_;
v___y_4016_ = v___y_4052_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__3, &l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3);
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 7);
lean_ctor_set(v___x_4002_, 1, v___x_4057_);
v___x_4059_ = v___x_4002_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_fst_4000_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
v___y_4013_ = v___y_4050_;
v_report_4014_ = v___x_4059_;
v___y_4015_ = v___y_4051_;
v___y_4016_ = v___y_4052_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
goto v___jp_4012_;
}
}
}
v___jp_4062_:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4067_, v___y_4064_, v___y_4063_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_toCold_4069_; lean_object* v_options_4070_; uint8_t v_hasTrace_4071_; 
v_toCold_4069_ = lean_ctor_get(v___y_4065_, 0);
v_options_4070_ = lean_ctor_get(v_toCold_4069_, 2);
v_hasTrace_4071_ = lean_ctor_get_uint8(v_options_4070_, sizeof(void*)*1);
if (v_hasTrace_4071_ == 0)
{
lean_object* v_a_4072_; 
v_a_4072_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4068_, 1);
v___y_4050_ = v_a_4072_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4063_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4073_; lean_object* v_inheritedTraceOptions_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v_a_4073_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4068_, 1);
v_inheritedTraceOptions_4074_ = lean_ctor_get(v_toCold_4069_, 11);
v___x_4075_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4074_, v_options_4070_, v___x_4075_);
if (v___x_4076_ == 0)
{
v___y_4050_ = v_a_4073_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4063_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__5, &l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5);
lean_inc(v_a_4073_);
v___x_4078_ = lean_array_to_list(v_a_4073_);
v___x_4079_ = lean_box(0);
v___x_4080_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4078_, v___x_4079_);
v___x_4081_ = l_Lean_MessageData_ofList(v___x_4080_);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4077_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4061_, v___x_4082_, v___y_4064_, v___y_4063_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_dec_ref_known(v___x_4083_, 1);
v___y_4050_ = v_a_4073_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4063_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_a_4073_);
lean_dec_ref(v___x_4011_);
lean_del_object(v___x_4006_);
lean_del_object(v___x_4002_);
lean_dec(v_fst_4000_);
lean_dec_ref(v_values_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4083_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4083_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v___x_4011_);
lean_del_object(v___x_4006_);
lean_del_object(v___x_4002_);
lean_dec(v_fst_4000_);
lean_dec_ref(v_values_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4092_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4068_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4068_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
v___jp_4100_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4105_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4106_ = lean_array_get_size(v___x_4011_);
v___x_4107_ = lean_nat_dec_lt(v___x_3979_, v___x_4106_);
if (v___x_4107_ == 0)
{
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4101_;
v___y_4065_ = v___y_4103_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___x_4105_;
goto v___jp_4062_;
}
else
{
size_t v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_usize_of_nat(v___x_4106_);
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4011_, v___x_3994_, v___x_4108_, v___x_4105_);
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4101_;
v___y_4065_ = v___y_4103_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___x_4109_;
goto v___jp_4062_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_values_3972_);
lean_dec_ref(v_xs_3971_);
v_a_4140_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_3995_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_3995_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4148_, lean_object* v_fixedParamPerms_4149_, lean_object* v_xs_4150_, lean_object* v_values_4151_, lean_object* v_termMeasure_x3fs_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4148_, v_fixedParamPerms_4149_, v_xs_4150_, v_values_4151_, v_termMeasure_x3fs_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
lean_dec_ref(v_fnNames_4148_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4159_, lean_object* v_as_4160_, size_t v_sz_4161_, size_t v_i_4162_, lean_object* v_b_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4159_, v_as_4160_, v_sz_4161_, v_i_4162_, v_b_4163_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4170_, lean_object* v_as_4171_, lean_object* v_sz_4172_, lean_object* v_i_4173_, lean_object* v_b_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
size_t v_sz_boxed_4180_; size_t v_i_boxed_4181_; lean_object* v_res_4182_; 
v_sz_boxed_4180_ = lean_unbox_usize(v_sz_4172_);
lean_dec(v_sz_4172_);
v_i_boxed_4181_ = lean_unbox_usize(v_i_4173_);
lean_dec(v_i_4173_);
v_res_4182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4170_, v_as_4171_, v_sz_boxed_4180_, v_i_boxed_4181_, v_b_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec_ref(v_as_4171_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4183_, uint8_t v_skipRealize_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v_env_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4187_ = lean_st_ref_get(v___y_4185_);
v_env_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc_ref(v_env_4188_);
lean_dec(v___x_4187_);
v___x_4189_ = l_Lean_Environment_contains(v_env_4188_, v_constName_4183_, v_skipRealize_4184_);
v___x_4190_ = lean_box(v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4192_, lean_object* v_skipRealize_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v_skipRealize_boxed_4196_; lean_object* v_res_4197_; 
v_skipRealize_boxed_4196_ = lean_unbox(v_skipRealize_4193_);
v_res_4197_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4192_, v_skipRealize_boxed_4196_, v___y_4194_);
lean_dec(v___y_4194_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4198_, uint8_t v_skipRealize_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4198_, v_skipRealize_4199_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4206_, lean_object* v_skipRealize_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
uint8_t v_skipRealize_boxed_4213_; lean_object* v_res_4214_; 
v_skipRealize_boxed_4213_ = lean_unbox(v_skipRealize_4207_);
v_res_4214_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4206_, v_skipRealize_boxed_4213_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_saveState___redArg(v___y_4217_, v___y_4219_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
lean_inc(v___y_4219_);
lean_inc_ref(v___y_4218_);
lean_inc(v___y_4217_);
lean_inc_ref(v___y_4216_);
v___x_4223_ = lean_apply_5(v_x_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, lean_box(0));
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_dec(v_a_4222_);
return v___x_4223_;
}
else
{
lean_object* v_a_4224_; uint8_t v___x_4225_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
v___x_4225_ = l_Lean_Exception_isInterrupt(v_a_4224_);
if (v___x_4225_ == 0)
{
uint8_t v___x_4226_; 
lean_inc(v_a_4224_);
v___x_4226_ = l_Lean_Exception_isRuntime(v_a_4224_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4223_, 1);
v___x_4227_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4222_, v___y_4217_, v___y_4219_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4234_ == 0)
{
lean_object* v_unused_4235_; 
v_unused_4235_ = lean_ctor_get(v___x_4227_, 0);
lean_dec(v_unused_4235_);
v___x_4229_ = v___x_4227_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_dec(v___x_4227_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
lean_ctor_set_tag(v___x_4229_, 1);
lean_ctor_set(v___x_4229_, 0, v_a_4224_);
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4224_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_a_4224_);
v_a_4236_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4227_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4227_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_dec(v_a_4224_);
lean_dec(v_a_4222_);
return v___x_4223_;
}
}
else
{
lean_dec(v_a_4224_);
lean_dec(v_a_4222_);
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v_x_4215_);
v_a_4244_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4221_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4221_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4259_, lean_object* v_x_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4267_, v_x_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
return v_res_4274_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4277_ = l_Lean_stringToMessageData(v___x_4276_);
return v___x_4277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4280_ = l_Lean_stringToMessageData(v___x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4281_, uint8_t v___x_4282_, lean_object* v_group_4283_, lean_object* v_k_4284_, lean_object* v_comb_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4281_, v___x_4282_, v___y_4289_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; uint8_t v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = lean_unbox(v_a_4292_);
lean_dec(v_a_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4294_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4295_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4283_);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4298_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v___x_4300_; 
lean_dec_ref_known(v___x_4299_, 1);
v___x_4300_ = lean_apply_6(v_k_4284_, v_comb_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, lean_box(0));
return v___x_4300_;
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v_comb_4285_);
lean_dec_ref(v_k_4284_);
v_a_4301_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4299_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4299_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v___x_4309_; 
lean_dec_ref(v_group_4283_);
v___x_4309_ = lean_apply_6(v_k_4284_, v_comb_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, lean_box(0));
return v___x_4309_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v_comb_4285_);
lean_dec_ref(v_k_4284_);
lean_dec_ref(v_group_4283_);
v_a_4310_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4291_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4291_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4318_, lean_object* v___x_4319_, lean_object* v_group_4320_, lean_object* v_k_4321_, lean_object* v_comb_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v___x_4295__boxed_4328_; lean_object* v_res_4329_; 
v___x_4295__boxed_4328_ = lean_unbox(v___x_4319_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4318_, v___x_4295__boxed_4328_, v_group_4320_, v_k_4321_, v_comb_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
return v_res_4329_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4332_ = l_Lean_stringToMessageData(v___x_4331_);
return v___x_4332_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4335_, lean_object* v_fnNames_4336_, lean_object* v_xs_4337_, lean_object* v_values_4338_, lean_object* v_as_4339_, size_t v_sz_4340_, size_t v_i_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_usize_dec_lt(v_i_4341_, v_sz_4340_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref(v_values_4338_);
lean_dec_ref(v_xs_4337_);
lean_dec_ref(v_k_4335_);
v___x_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4349_, 0, v_b_4342_);
return v___x_4349_;
}
else
{
lean_object* v_snd_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4421_; 
v_snd_4350_ = lean_ctor_get(v_b_4342_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_b_4342_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v_b_4342_, 0);
lean_dec(v_unused_4422_);
v___x_4352_ = v_b_4342_;
v_isShared_4353_ = v_isSharedCheck_4421_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_snd_4350_);
lean_dec(v_b_4342_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4421_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v_a_4354_; lean_object* v_group_4355_; lean_object* v_comb_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4420_; 
v_a_4354_ = lean_array_uget(v_as_4339_, v_i_4341_);
v_group_4355_ = lean_ctor_get(v_a_4354_, 0);
v_comb_4356_ = lean_ctor_get(v_a_4354_, 1);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_a_4354_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4358_ = v_a_4354_;
v_isShared_4359_ = v_isSharedCheck_4420_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_comb_4356_);
lean_inc(v_group_4355_);
lean_dec(v_a_4354_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4420_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_toIndGroupInfo_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; 
v_toIndGroupInfo_4360_ = lean_ctor_get(v_group_4355_, 0);
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4360_, v___x_4362_);
v___x_4364_ = lean_box(v___x_4348_);
lean_inc_ref(v_comb_4356_);
lean_inc_ref(v_k_4335_);
v___f_4365_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4365_, 0, v___x_4363_);
lean_closure_set(v___f_4365_, 1, v___x_4364_);
lean_closure_set(v___f_4365_, 2, v_group_4355_);
lean_closure_set(v___f_4365_, 3, v_k_4335_);
lean_closure_set(v___f_4365_, 4, v_comb_4356_);
v___x_4366_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4365_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4378_; 
lean_del_object(v___x_4358_);
lean_dec_ref(v_comb_4356_);
lean_dec_ref(v_values_4338_);
lean_dec_ref(v_xs_4337_);
lean_dec_ref(v_k_4335_);
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4378_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4378_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4371_, 0, v_a_4367_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4371_);
v___x_4373_ = v___x_4352_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4377_, 1, v_snd_4350_);
v___x_4373_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4375_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4373_);
v___x_4375_ = v___x_4369_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4419_; 
v_a_4379_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4381_ = v___x_4366_;
v_isShared_4382_ = v_isSharedCheck_4419_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4366_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4419_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
uint8_t v___x_4383_; 
v___x_4383_ = l_Lean_Exception_isInterrupt(v_a_4379_);
if (v___x_4383_ == 0)
{
uint8_t v___x_4384_; 
lean_inc(v_a_4379_);
v___x_4384_ = l_Lean_Exception_isRuntime(v_a_4379_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
lean_del_object(v___x_4381_);
lean_inc_ref(v_values_4338_);
lean_inc_ref(v_xs_4337_);
v___x_4385_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4336_, v_xs_4337_, v_values_4338_, v_comb_4356_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v___x_4387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4359_ == 0)
{
lean_ctor_set_tag(v___x_4358_, 7);
lean_ctor_set(v___x_4358_, 1, v_a_4386_);
lean_ctor_set(v___x_4358_, 0, v___x_4387_);
v___x_4389_ = v___x_4358_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_a_4386_);
v___x_4389_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4390_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_Exception_toMessageData(v_a_4379_);
v___x_4393_ = l_Lean_indentD(v___x_4392_);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4391_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v_snd_4350_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 1, v___x_4397_);
lean_ctor_set(v___x_4352_, 0, v___x_4361_);
v___x_4399_ = v___x_4352_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
size_t v___x_4400_; size_t v___x_4401_; 
v___x_4400_ = ((size_t)1ULL);
v___x_4401_ = lean_usize_add(v_i_4341_, v___x_4400_);
v_i_4341_ = v___x_4401_;
v_b_4342_ = v___x_4399_;
goto _start;
}
}
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
lean_dec(v_a_4379_);
lean_del_object(v___x_4358_);
lean_del_object(v___x_4352_);
lean_dec(v_snd_4350_);
lean_dec_ref(v_values_4338_);
lean_dec_ref(v_xs_4337_);
lean_dec_ref(v_k_4335_);
v_a_4405_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4385_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4385_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
else
{
lean_object* v___x_4414_; 
lean_del_object(v___x_4358_);
lean_dec_ref(v_comb_4356_);
lean_del_object(v___x_4352_);
lean_dec(v_snd_4350_);
lean_dec_ref(v_values_4338_);
lean_dec_ref(v_xs_4337_);
lean_dec_ref(v_k_4335_);
if (v_isShared_4382_ == 0)
{
v___x_4414_ = v___x_4381_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4379_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
else
{
lean_object* v___x_4417_; 
lean_del_object(v___x_4358_);
lean_dec_ref(v_comb_4356_);
lean_del_object(v___x_4352_);
lean_dec(v_snd_4350_);
lean_dec_ref(v_values_4338_);
lean_dec_ref(v_xs_4337_);
lean_dec_ref(v_k_4335_);
if (v_isShared_4382_ == 0)
{
v___x_4417_ = v___x_4381_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4379_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4423_, lean_object* v_fnNames_4424_, lean_object* v_xs_4425_, lean_object* v_values_4426_, lean_object* v_as_4427_, lean_object* v_sz_4428_, lean_object* v_i_4429_, lean_object* v_b_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
size_t v_sz_boxed_4436_; size_t v_i_boxed_4437_; lean_object* v_res_4438_; 
v_sz_boxed_4436_ = lean_unbox_usize(v_sz_4428_);
lean_dec(v_sz_4428_);
v_i_boxed_4437_ = lean_unbox_usize(v_i_4429_);
lean_dec(v_i_4429_);
v_res_4438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4423_, v_fnNames_4424_, v_xs_4425_, v_values_4426_, v_as_4427_, v_sz_boxed_4436_, v_i_boxed_4437_, v_b_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec_ref(v_as_4427_);
lean_dec_ref(v_fnNames_4424_);
return v_res_4438_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4441_ = l_Lean_stringToMessageData(v___x_4440_);
return v___x_4441_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4444_ = l_Lean_stringToMessageData(v___x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4445_, lean_object* v_xs_4446_, lean_object* v_values_4447_, lean_object* v_candidates_4448_, lean_object* v_k_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_candidates_4455_; lean_object* v_report_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4516_; 
v_candidates_4455_ = lean_ctor_get(v_candidates_4448_, 0);
v_report_4456_ = lean_ctor_get(v_candidates_4448_, 1);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_candidates_4448_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4458_ = v_candidates_4448_;
v_isShared_4459_ = v_isSharedCheck_4516_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_report_4456_);
lean_inc(v_candidates_4455_);
lean_dec(v_candidates_4448_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4516_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = lean_box(0);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_report_4456_);
v___x_4462_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
size_t v_sz_4463_; size_t v___x_4464_; lean_object* v___x_4465_; 
v_sz_4463_ = lean_array_size(v_candidates_4455_);
v___x_4464_ = ((size_t)0ULL);
v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4449_, v_fnNames_4445_, v_xs_4446_, v_values_4447_, v_candidates_4455_, v_sz_4463_, v___x_4464_, v___x_4462_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec_ref(v_candidates_4455_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4506_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4468_ = v___x_4465_;
v_isShared_4469_ = v_isSharedCheck_4506_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4465_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4506_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v_fst_4470_; 
v_fst_4470_ = lean_ctor_get(v_a_4466_, 0);
if (lean_obj_tag(v_fst_4470_) == 0)
{
lean_object* v_toCold_4471_; lean_object* v_options_4472_; lean_object* v_snd_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4500_; 
lean_del_object(v___x_4468_);
v_toCold_4471_ = lean_ctor_get(v_a_4452_, 0);
v_options_4472_ = lean_ctor_get(v_toCold_4471_, 2);
v_snd_4473_ = lean_ctor_get(v_a_4466_, 1);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_a_4466_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_a_4466_, 0);
lean_dec(v_unused_4501_);
v___x_4475_ = v_a_4466_;
v_isShared_4476_ = v_isSharedCheck_4500_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_snd_4473_);
lean_dec(v_a_4466_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4500_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_inheritedTraceOptions_4477_; uint8_t v_hasTrace_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
v_inheritedTraceOptions_4477_ = lean_ctor_get(v_toCold_4471_, 11);
v_hasTrace_4478_ = lean_ctor_get_uint8(v_options_4472_, sizeof(void*)*1);
v___x_4479_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4476_ == 0)
{
lean_ctor_set_tag(v___x_4475_, 7);
lean_ctor_set(v___x_4475_, 0, v___x_4479_);
v___x_4481_ = v___x_4475_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_snd_4473_);
v___x_4481_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
if (v_hasTrace_4478_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4482_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4477_, v_options_4472_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4486_;
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4487_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4481_);
v___x_4488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
lean_ctor_set(v___x_4488_, 1, v___x_4481_);
v___x_4489_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4483_, v___x_4488_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4490_; 
lean_dec_ref_known(v___x_4489_, 1);
v___x_4490_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec_ref(v___x_4481_);
v_a_4491_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4489_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4489_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
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
lean_object* v_val_4502_; lean_object* v___x_4504_; 
lean_inc_ref(v_fst_4470_);
lean_dec(v_a_4466_);
v_val_4502_ = lean_ctor_get(v_fst_4470_, 0);
lean_inc(v_val_4502_);
lean_dec_ref_known(v_fst_4470_, 1);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v_val_4502_);
v___x_4504_ = v___x_4468_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_val_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
v_a_4507_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4465_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4465_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4517_, lean_object* v_xs_4518_, lean_object* v_values_4519_, lean_object* v_candidates_4520_, lean_object* v_k_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4517_, v_xs_4518_, v_values_4519_, v_candidates_4520_, v_k_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec_ref(v_fnNames_4517_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4528_, lean_object* v_fnNames_4529_, lean_object* v_xs_4530_, lean_object* v_values_4531_, lean_object* v_candidates_4532_, lean_object* v_k_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4529_, v_xs_4530_, v_values_4531_, v_candidates_4532_, v_k_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4540_, lean_object* v_fnNames_4541_, lean_object* v_xs_4542_, lean_object* v_values_4543_, lean_object* v_candidates_4544_, lean_object* v_k_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4540_, v_fnNames_4541_, v_xs_4542_, v_values_4543_, v_candidates_4544_, v_k_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec_ref(v_fnNames_4541_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4552_, lean_object* v_k_4553_, lean_object* v_fnNames_4554_, lean_object* v_xs_4555_, lean_object* v_values_4556_, lean_object* v_as_4557_, size_t v_sz_4558_, size_t v_i_4559_, lean_object* v_b_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4553_, v_fnNames_4554_, v_xs_4555_, v_values_4556_, v_as_4557_, v_sz_4558_, v_i_4559_, v_b_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4567_, lean_object* v_k_4568_, lean_object* v_fnNames_4569_, lean_object* v_xs_4570_, lean_object* v_values_4571_, lean_object* v_as_4572_, lean_object* v_sz_4573_, lean_object* v_i_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
size_t v_sz_boxed_4581_; size_t v_i_boxed_4582_; lean_object* v_res_4583_; 
v_sz_boxed_4581_ = lean_unbox_usize(v_sz_4573_);
lean_dec(v_sz_4573_);
v_i_boxed_4582_ = lean_unbox_usize(v_i_4574_);
lean_dec(v_i_4574_);
v_res_4583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4567_, v_k_4568_, v_fnNames_4569_, v_xs_4570_, v_values_4571_, v_as_4572_, v_sz_boxed_4581_, v_i_boxed_4582_, v_b_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec_ref(v_as_4572_);
lean_dec_ref(v_fnNames_4569_);
return v_res_4583_;
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
