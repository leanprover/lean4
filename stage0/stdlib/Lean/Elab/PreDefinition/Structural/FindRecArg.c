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
lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParam___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParam___closed__0));
v___x_29_ = l_Lean_stringToMessageData(v___x_28_);
return v___x_29_;
}
}
lean_object* l_Lean_Elab_Structural_prettyParam(lean_object* v_xs_30_, lean_object* v_i_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v_x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = l_Lean_instInhabitedExpr;
v_x_38_ = lean_array_get_borrowed(v___x_37_, v_xs_30_, v_i_31_);
v___x_39_ = l_Lean_Expr_fvarId_x21(v_x_38_);
v___x_40_ = l_Lean_FVarId_getUserName___redArg(v___x_39_, v_a_32_, v_a_34_, v_a_35_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; uint8_t v___x_42_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_40_, 1);
v___x_42_ = l_Lean_Name_hasMacroScopes(v_a_41_);
lean_dec(v_a_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_x_38_);
v___x_43_ = l_Lean_MessageData_ofExpr(v_x_38_);
v___x_44_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_43_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_45_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParam___closed__1, &l_Lean_Elab_Structural_prettyParam___closed__1_once, _init_l_Lean_Elab_Structural_prettyParam___closed__1);
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_add(v_i_31_, v___x_46_);
v___x_48_ = l_Nat_reprFast(v___x_47_);
v___x_49_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
v___x_50_ = l_Lean_MessageData_ofFormat(v___x_49_);
v___x_51_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_45_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_51_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
return v___x_52_;
}
}
else
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_a_53_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_40_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_40_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_prettyParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_30_ = stack[0].m_obj;
lean_object* v_i_31_ = stack[1].m_obj;
lean_object* v_a_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Lean_Elab_Structural_prettyParam(v_xs_30_, v_i_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam___boxed(lean_object* v_xs_62_, lean_object* v_i_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Elab_Structural_prettyParam(v_xs_62_, v_i_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_i_63_);
lean_dec_ref(v_xs_62_);
return v_res_69_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object* v_k_70_, lean_object* v_b_71_, lean_object* v_c_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
lean_inc(v___y_76_);
lean_inc_ref(v___y_75_);
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
v___x_78_ = lean_apply_7(v_k_70_, v_b_71_, v_c_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, lean_box(0));
return v___x_78_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_70_ = stack[0].m_obj;
lean_object* v_b_71_ = stack[1].m_obj;
lean_object* v_c_72_ = stack[2].m_obj;
lean_object* v___y_73_ = stack[3].m_obj;
lean_object* v___y_74_ = stack[4].m_obj;
lean_object* v___y_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v_res_79_;
v_res_79_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_70_, v_b_71_, v_c_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object* v_k_80_, lean_object* v_b_81_, lean_object* v_c_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_80_, v_b_81_, v_c_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_88_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(lean_object* v_e_89_, lean_object* v_k_90_, uint8_t v_cleanupAnnotations_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___f_97_; uint8_t v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_97_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_97_, 0, v_k_90_);
v___x_98_ = 1;
v___x_99_ = 0;
v___x_100_ = lean_box(0);
v___x_101_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_89_, v___x_98_, v___x_99_, v___x_98_, v___x_99_, v___x_100_, v___f_97_, v_cleanupAnnotations_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_101_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_101_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_89_ = stack[0].m_obj;
lean_object* v_k_90_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_91_ = stack[2].m_num;
lean_object* v___y_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v___y_95_ = stack[6].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_89_, v_k_90_, v_cleanupAnnotations_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(lean_object* v_e_119_, lean_object* v_k_120_, lean_object* v_cleanupAnnotations_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_127_; lean_object* v_res_128_; 
v_cleanupAnnotations_boxed_127_ = lean_unbox(v_cleanupAnnotations_121_);
v_res_128_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_119_, v_k_120_, v_cleanupAnnotations_boxed_127_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_128_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_object* v_00_u03b1_129_, lean_object* v_e_130_, lean_object* v_k_131_, uint8_t v_cleanupAnnotations_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_130_, v_k_131_, v_cleanupAnnotations_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_130_ = stack[1].m_obj;
lean_object* v_k_131_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_132_ = stack[3].m_num;
lean_object* v___y_133_ = stack[4].m_obj;
lean_object* v___y_134_ = stack[5].m_obj;
lean_object* v___y_135_ = stack[6].m_obj;
lean_object* v___y_136_ = stack[7].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_box(0), v_e_130_, v_k_131_, v_cleanupAnnotations_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(lean_object* v_00_u03b1_140_, lean_object* v_e_141_, lean_object* v_k_142_, lean_object* v_cleanupAnnotations_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_149_; lean_object* v_res_150_; 
v_cleanupAnnotations_boxed_149_ = lean_unbox(v_cleanupAnnotations_143_);
v_res_150_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(v_00_u03b1_140_, v_e_141_, v_k_142_, v_cleanupAnnotations_boxed_149_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_150_;
}
}
lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0(lean_object* v_recArgInfo_151_, lean_object* v_xs_152_, lean_object* v_ys_153_, lean_object* v_x_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_fixedParamPerm_160_; lean_object* v_recArgPos_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_fixedParamPerm_160_ = lean_ctor_get(v_recArgInfo_151_, 1);
lean_inc_ref(v_fixedParamPerm_160_);
v_recArgPos_161_ = lean_ctor_get(v_recArgInfo_151_, 2);
lean_inc(v_recArgPos_161_);
lean_dec_ref(v_recArgInfo_151_);
v___x_162_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_160_, v_xs_152_, v_ys_153_);
v___x_163_ = l_Lean_Elab_Structural_prettyParam(v___x_162_, v_recArgPos_161_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v_recArgPos_161_);
lean_dec_ref(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_prettyRecArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfo_151_ = stack[0].m_obj;
lean_object* v_xs_152_ = stack[1].m_obj;
lean_object* v_ys_153_ = stack[2].m_obj;
lean_object* v_x_154_ = stack[3].m_obj;
lean_object* v___y_155_ = stack[4].m_obj;
lean_object* v___y_156_ = stack[5].m_obj;
lean_object* v___y_157_ = stack[6].m_obj;
lean_object* v___y_158_ = stack[7].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_151_, v_xs_152_, v_ys_153_, v_x_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object* v_recArgInfo_165_, lean_object* v_xs_166_, lean_object* v_ys_167_, lean_object* v_x_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_165_, v_xs_166_, v_ys_167_, v_x_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec_ref(v_x_168_);
lean_dec_ref(v_xs_166_);
return v_res_174_;
}
}
lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object* v_xs_175_, lean_object* v_value_176_, lean_object* v_recArgInfo_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___f_183_; uint8_t v___x_184_; lean_object* v___x_185_; 
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_183_, 0, v_recArgInfo_177_);
lean_closure_set(v___f_183_, 1, v_xs_175_);
v___x_184_ = 0;
v___x_185_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_176_, v___f_183_, v___x_184_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_prettyRecArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_175_ = stack[0].m_obj;
lean_object* v_value_176_ = stack[1].m_obj;
lean_object* v_recArgInfo_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_a_180_ = stack[5].m_obj;
lean_object* v_a_181_ = stack[6].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_175_, v_value_176_, v_recArgInfo_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object* v_xs_187_, lean_object* v_value_188_, lean_object* v_recArgInfo_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_187_, v_value_188_, v_recArgInfo_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_195_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object* v_xs_199_, lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_xs_199_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_b_203_);
return v___x_210_;
}
else
{
lean_object* v_snd_211_; lean_object* v_snd_212_; lean_object* v_fst_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_295_; 
v_snd_211_ = lean_ctor_get(v_b_203_, 1);
lean_inc(v_snd_211_);
v_snd_212_ = lean_ctor_get(v_snd_211_, 1);
lean_inc(v_snd_212_);
v_fst_213_ = lean_ctor_get(v_b_203_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_b_203_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_b_203_, 1);
lean_dec(v_unused_296_);
v___x_215_ = v_b_203_;
v_isShared_216_ = v_isSharedCheck_295_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_fst_213_);
lean_dec(v_b_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_295_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_293_; 
v_fst_217_ = lean_ctor_get(v_snd_211_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_snd_211_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_snd_211_, 1);
lean_dec(v_unused_294_);
v___x_219_ = v_snd_211_;
v_isShared_220_ = v_isSharedCheck_293_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_fst_217_);
lean_dec(v_snd_211_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_293_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; uint8_t v___x_224_; 
v_array_221_ = lean_ctor_get(v_snd_212_, 0);
v_start_222_ = lean_ctor_get(v_snd_212_, 1);
v_stop_223_ = lean_ctor_get(v_snd_212_, 2);
v___x_224_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; 
lean_dec_ref(v_xs_199_);
if (v_isShared_220_ == 0)
{
v___x_226_ = v___x_219_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_snd_212_);
v___x_226_ = v_reuseFailAlloc_231_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_226_);
v___x_228_ = v___x_215_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_fst_213_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
else
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_289_; 
lean_inc(v_stop_223_);
lean_inc(v_start_222_);
lean_inc_ref(v_array_221_);
v_isSharedCheck_289_ = !lean_is_exclusive(v_snd_212_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_290_ = lean_ctor_get(v_snd_212_, 2);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_snd_212_, 1);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_snd_212_, 0);
lean_dec(v_unused_292_);
v___x_233_ = v_snd_212_;
v_isShared_234_ = v_isSharedCheck_289_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_snd_212_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_289_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_array_235_; lean_object* v_start_236_; lean_object* v_stop_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v_array_235_ = lean_ctor_get(v_fst_217_, 0);
v_start_236_ = lean_ctor_get(v_fst_217_, 1);
v_stop_237_ = lean_ctor_get(v_fst_217_, 2);
v___x_238_ = lean_array_fget(v_array_221_, v_start_222_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_start_222_, v___x_239_);
lean_dec(v_start_222_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_240_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_array_221_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_stop_223_);
v___x_242_ = v_reuseFailAlloc_288_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_lt(v_start_236_, v_stop_237_);
if (v___x_243_ == 0)
{
lean_object* v___x_245_; 
lean_dec(v___x_238_);
lean_dec_ref(v_xs_199_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_242_);
v___x_245_ = v___x_219_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_242_);
v___x_245_ = v_reuseFailAlloc_250_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_245_);
v___x_247_ = v___x_215_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_fst_213_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
else
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_284_; 
lean_inc(v_stop_237_);
lean_inc(v_start_236_);
lean_inc_ref(v_array_235_);
v_isSharedCheck_284_ = !lean_is_exclusive(v_fst_217_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_fst_217_, 2);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_fst_217_, 1);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_fst_217_, 0);
lean_dec(v_unused_287_);
v___x_252_ = v_fst_217_;
v_isShared_253_ = v_isSharedCheck_284_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_fst_217_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_284_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_a_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v_a_254_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
v___x_255_ = lean_array_fget(v_array_235_, v_start_236_);
v___x_256_ = lean_nat_add(v_start_236_, v___x_239_);
lean_dec(v_start_236_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_256_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_array_235_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_stop_237_);
v___x_258_ = v_reuseFailAlloc_283_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
lean_inc_ref(v_xs_199_);
v___x_259_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_199_, v___x_255_, v___x_238_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc(v_a_254_);
v___x_263_ = l_Lean_MessageData_ofName(v_a_254_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_array_push(v_fst_213_, v___x_264_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_242_);
lean_ctor_set(v___x_219_, 0, v___x_258_);
v___x_267_ = v___x_219_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_242_);
v___x_267_ = v_reuseFailAlloc_274_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_269_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___x_267_);
lean_ctor_set(v___x_215_, 0, v___x_265_);
v___x_269_ = v___x_215_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
size_t v___x_270_; size_t v___x_271_; 
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_202_, v___x_270_);
v_i_202_ = v___x_271_;
v_b_203_ = v___x_269_;
goto _start;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v___x_258_);
lean_dec_ref(v___x_242_);
lean_del_object(v___x_219_);
lean_del_object(v___x_215_);
lean_dec(v_fst_213_);
lean_dec_ref(v_xs_199_);
v_a_275_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_259_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_259_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_199_ = stack[0].m_obj;
lean_object* v_as_200_ = stack[1].m_obj;
size_t v_sz_201_ = stack[2].m_num;
size_t v_i_202_ = stack[3].m_num;
lean_object* v_b_203_ = stack[4].m_obj;
lean_object* v___y_204_ = stack[5].m_obj;
lean_object* v___y_205_ = stack[6].m_obj;
lean_object* v___y_206_ = stack[7].m_obj;
lean_object* v___y_207_ = stack[8].m_obj;
lean_object* v_res_297_;
v_res_297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_199_, v_as_200_, v_sz_201_, v_i_202_, v_b_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object* v_xs_298_, lean_object* v_as_299_, lean_object* v_sz_300_, lean_object* v_i_301_, lean_object* v_b_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
size_t v_sz_boxed_308_; size_t v_i_boxed_309_; lean_object* v_res_310_; 
v_sz_boxed_308_ = lean_unbox_usize(v_sz_300_);
lean_dec(v_sz_300_);
v_i_boxed_309_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_298_, v_as_299_, v_sz_boxed_308_, v_i_boxed_309_, v_b_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec_ref(v_as_299_);
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__1));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__3));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object* v_fnNames_319_, lean_object* v_xs_320_, lean_object* v_values_321_, lean_object* v_recArgInfos_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_array_get_size(v_fnNames_319_);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_dec_eq(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v_l_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; size_t v_sz_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v_l_332_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_333_ = lean_array_get_size(v_values_321_);
v___x_334_ = l_Array_toSubarray___redArg(v_values_321_, v___x_331_, v___x_333_);
v___x_335_ = lean_array_get_size(v_recArgInfos_322_);
v___x_336_ = l_Array_toSubarray___redArg(v_recArgInfos_322_, v___x_331_, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_l_332_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v_sz_339_ = lean_array_size(v_fnNames_319_);
v___x_340_ = ((size_t)0ULL);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_320_, v_fnNames_319_, v_sz_339_, v___x_340_, v___x_338_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_361_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_361_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_fst_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_359_; 
v_fst_346_ = lean_ctor_get(v_a_342_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_a_342_, 1);
lean_dec(v_unused_360_);
v___x_348_ = v_a_342_;
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_fst_346_);
lean_dec(v_a_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_350_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__2, &l_Lean_Elab_Structural_prettyParameterSet___closed__2_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2);
v___x_351_ = lean_array_to_list(v_fst_346_);
v___x_352_ = l_Lean_MessageData_andList(v___x_351_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 7);
lean_ctor_set(v___x_348_, 1, v___x_352_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_354_ = v___x_348_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_354_);
v___x_356_ = v___x_344_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
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
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_341_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_341_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_370_ = l_Lean_instInhabitedExpr;
v___x_371_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_array_get(v___x_370_, v_values_321_, v___x_372_);
lean_dec_ref(v_values_321_);
v___x_374_ = lean_array_get(v___x_371_, v_recArgInfos_322_, v___x_372_);
lean_dec_ref(v_recArgInfos_322_);
v___x_375_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_320_, v___x_373_, v___x_374_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_385_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_385_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__4, &l_Lean_Elab_Structural_prettyParameterSet___closed__4_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_a_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
return v___x_375_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_prettyParameterSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_319_ = stack[0].m_obj;
lean_object* v_xs_320_ = stack[1].m_obj;
lean_object* v_values_321_ = stack[2].m_obj;
lean_object* v_recArgInfos_322_ = stack[3].m_obj;
lean_object* v_a_323_ = stack[4].m_obj;
lean_object* v_a_324_ = stack[5].m_obj;
lean_object* v_a_325_ = stack[6].m_obj;
lean_object* v_a_326_ = stack[7].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_319_, v_xs_320_, v_values_321_, v_recArgInfos_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object* v_fnNames_387_, lean_object* v_xs_388_, lean_object* v_values_389_, lean_object* v_recArgInfos_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_387_, v_xs_388_, v_values_389_, v_recArgInfos_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec_ref(v_fnNames_387_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object* v_xs_397_, lean_object* v_v_398_, lean_object* v_i_399_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_array_get_size(v_xs_397_);
v___x_401_ = lean_nat_dec_lt(v_i_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_i_399_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_array_fget_borrowed(v_xs_397_, v_i_399_);
v___x_404_ = lean_expr_eqv(v___x_403_, v_v_398_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_i_399_, v___x_405_);
lean_dec(v_i_399_);
v_i_399_ = v___x_406_;
goto _start;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_i_399_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_409_, lean_object* v_v_410_, lean_object* v_i_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_409_, v_v_410_, v_i_411_);
lean_dec_ref(v_v_410_);
lean_dec_ref(v_xs_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object* v_xs_413_, lean_object* v_v_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_413_, v_v_414_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object* v_xs_417_, lean_object* v_v_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_417_, v_v_418_);
lean_dec_ref(v_v_418_);
lean_dec_ref(v_xs_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object* v_xs_420_, lean_object* v_v_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_420_, v_v_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_val_424_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_val_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object* v_xs_432_, lean_object* v_v_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_432_, v_v_433_);
lean_dec_ref(v_v_433_);
lean_dec_ref(v_xs_432_);
return v_res_434_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object* v_xs_435_, lean_object* v_as_436_, size_t v_sz_437_, size_t v_i_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_a_441_; uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_445_ == 0)
{
return v_b_439_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_447_; 
v_a_446_ = lean_array_uget_borrowed(v_as_436_, v_i_438_);
v___x_447_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_435_, v_a_446_);
if (lean_obj_tag(v___x_447_) == 1)
{
lean_object* v_val_448_; uint8_t v___x_449_; 
v_val_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_nat_dec_lt(v_val_448_, v_b_439_);
if (v___x_449_ == 0)
{
lean_dec(v_val_448_);
v_a_441_ = v_b_439_;
goto v___jp_440_;
}
else
{
lean_dec(v_b_439_);
v_a_441_ = v_val_448_;
goto v___jp_440_;
}
}
else
{
lean_dec(v___x_447_);
v_a_441_ = v_b_439_;
goto v___jp_440_;
}
}
v___jp_440_:
{
size_t v___x_442_; size_t v___x_443_; 
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_438_, v___x_442_);
v_i_438_ = v___x_443_;
v_b_439_ = v_a_441_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_435_ = stack[0].m_obj;
lean_object* v_as_436_ = stack[1].m_obj;
size_t v_sz_437_ = stack[2].m_num;
size_t v_i_438_ = stack[3].m_num;
lean_object* v_b_439_ = stack[4].m_obj;
lean_object* v_res_450_;
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_435_, v_as_436_, v_sz_437_, v_i_438_, v_b_439_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object* v_xs_451_, lean_object* v_as_452_, lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_b_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_451_, v_as_452_, v_sz_boxed_456_, v_i_boxed_457_, v_b_455_);
lean_dec_ref(v_as_452_);
lean_dec_ref(v_xs_451_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object* v_xs_459_, lean_object* v_indices_460_){
_start:
{
lean_object* v_minPos_461_; size_t v_sz_462_; size_t v___x_463_; lean_object* v___x_464_; 
v_minPos_461_ = lean_array_get_size(v_xs_459_);
v_sz_462_ = lean_array_size(v_indices_460_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_459_, v_indices_460_, v_sz_462_, v___x_463_, v_minPos_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* v_xs_465_, lean_object* v_indices_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_465_, v_indices_466_);
lean_dec_ref(v_indices_466_);
lean_dec_ref(v_xs_465_);
return v_res_467_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object* v_x_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_468_ = stack[0].m_obj;
uint8_t v_res_470_;
v_res_470_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_468_);
stack->m_num = v_res_470_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_471_);
lean_dec(v_x_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object* v_fvarId_474_, lean_object* v_x_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = l_Lean_instBEqFVarId_beq(v_fvarId_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_474_ = stack[0].m_obj;
lean_object* v_x_475_ = stack[1].m_obj;
uint8_t v_res_477_;
v_res_477_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_474_, v_x_475_);
stack->m_num = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_fvarId_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_unsigned_to_nat(16u);
v___x_485_ = lean_mk_array(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_489_, lean_object* v_fvarId_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; uint8_t v_fst_497_; lean_object* v_mctx_498_; lean_object* v___y_516_; lean_object* v_mctx_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___f_493_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_494_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_494_, 0, v_fvarId_490_);
v___x_495_ = lean_st_ref_get(v___y_491_);
v_mctx_521_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref_n(v_mctx_521_, 2);
lean_dec(v___x_495_);
v___x_522_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_mctx_521_);
v___x_524_ = l_Lean_Expr_hasFVar(v_e_489_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_Expr_hasMVar(v_e_489_);
if (v___x_525_ == 0)
{
lean_dec_ref_known(v___x_523_, 2);
lean_dec_ref(v___f_494_);
lean_dec_ref(v_e_489_);
v_fst_497_ = v___x_525_;
v_mctx_498_ = v_mctx_521_;
goto v___jp_496_;
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v_mctx_521_);
v___x_526_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_494_, v___f_493_, v_e_489_, v___x_523_);
v___y_516_ = v___x_526_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_mctx_521_);
v___x_527_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_494_, v___f_493_, v_e_489_, v___x_523_);
v___y_516_ = v___x_527_;
goto v___jp_515_;
}
v___jp_496_:
{
lean_object* v___x_499_; lean_object* v_cache_500_; lean_object* v_zetaDeltaFVarIds_501_; lean_object* v_postponed_502_; lean_object* v_diag_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_513_; 
v___x_499_ = lean_st_ref_take(v___y_491_);
v_cache_500_ = lean_ctor_get(v___x_499_, 1);
v_zetaDeltaFVarIds_501_ = lean_ctor_get(v___x_499_, 2);
v_postponed_502_ = lean_ctor_get(v___x_499_, 3);
v_diag_503_ = lean_ctor_get(v___x_499_, 4);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___x_499_, 0);
lean_dec(v_unused_514_);
v___x_505_ = v___x_499_;
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_diag_503_);
lean_inc(v_postponed_502_);
lean_inc(v_zetaDeltaFVarIds_501_);
lean_inc(v_cache_500_);
lean_dec(v___x_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_mctx_498_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_mctx_498_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_cache_500_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_zetaDeltaFVarIds_501_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_postponed_502_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_diag_503_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_st_ref_put(v___y_491_, v___x_508_);
v___x_510_ = lean_box(v_fst_497_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
v___jp_515_:
{
lean_object* v_snd_517_; lean_object* v_fst_518_; lean_object* v_mctx_519_; uint8_t v___x_520_; 
v_snd_517_ = lean_ctor_get(v___y_516_, 1);
lean_inc(v_snd_517_);
v_fst_518_ = lean_ctor_get(v___y_516_, 0);
lean_inc(v_fst_518_);
lean_dec_ref(v___y_516_);
v_mctx_519_ = lean_ctor_get(v_snd_517_, 1);
lean_inc_ref(v_mctx_519_);
lean_dec(v_snd_517_);
v___x_520_ = lean_unbox(v_fst_518_);
lean_dec(v_fst_518_);
v_fst_497_ = v___x_520_;
v_mctx_498_ = v_mctx_519_;
goto v___jp_496_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_489_ = stack[0].m_obj;
lean_object* v_fvarId_490_ = stack[1].m_obj;
lean_object* v___y_491_ = stack[2].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_489_, v_fvarId_490_, v___y_491_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_529_, lean_object* v_fvarId_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_529_, v_fvarId_530_, v___y_531_);
lean_dec(v___y_531_);
return v_res_533_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_534_, lean_object* v_fvarId_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_534_, v_fvarId_535_, v___y_537_);
return v___x_541_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_534_ = stack[0].m_obj;
lean_object* v_fvarId_535_ = stack[1].m_obj;
lean_object* v___y_536_ = stack[2].m_obj;
lean_object* v___y_537_ = stack[3].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v_res_542_;
v_res_542_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_534_, v_fvarId_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_543_, lean_object* v_fvarId_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_543_, v_fvarId_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_551_, lean_object* v_as_552_, size_t v_i_553_, size_t v_stop_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_eq(v_i_553_, v_stop_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_uget_borrowed(v_as_552_, v_i_553_);
v___x_557_ = lean_expr_eqv(v_a_551_, v___x_556_);
if (v___x_557_ == 0)
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_553_, v___x_558_);
v_i_553_ = v___x_559_;
goto _start;
}
else
{
return v___x_557_;
}
}
else
{
uint8_t v___x_561_; 
v___x_561_ = 0;
return v___x_561_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_551_ = stack[0].m_obj;
lean_object* v_as_552_ = stack[1].m_obj;
size_t v_i_553_ = stack[2].m_num;
size_t v_stop_554_ = stack[3].m_num;
uint8_t v_res_562_;
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_551_, v_as_552_, v_i_553_, v_stop_554_);
stack->m_num = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_563_, lean_object* v_as_564_, lean_object* v_i_565_, lean_object* v_stop_566_){
_start:
{
size_t v_i_boxed_567_; size_t v_stop_boxed_568_; uint8_t v_res_569_; lean_object* v_r_570_; 
v_i_boxed_567_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_stop_boxed_568_ = lean_unbox_usize(v_stop_566_);
lean_dec(v_stop_566_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_563_, v_as_564_, v_i_boxed_567_, v_stop_boxed_568_);
lean_dec_ref(v_as_564_);
lean_dec_ref(v_a_563_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_array_get_size(v_as_571_);
v___x_575_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
return v___x_575_;
}
else
{
if (v___x_575_ == 0)
{
return v___x_575_;
}
else
{
size_t v___x_576_; size_t v___x_577_; uint8_t v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_574_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_572_, v_as_571_, v___x_576_, v___x_577_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_571_ = stack[0].m_obj;
lean_object* v_a_572_ = stack[1].m_obj;
uint8_t v_res_579_;
v_res_579_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_571_, v_a_572_);
stack->m_num = v_res_579_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_580_, lean_object* v_a_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_580_, v_a_581_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_as_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_587_, lean_object* v_indices_588_, lean_object* v_a_589_, lean_object* v_as_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_a_600_; uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_587_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_b_593_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_a_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_b_593_);
v___x_606_ = lean_box(0);
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_608_ = lean_array_uget_borrowed(v_as_590_, v_i_592_);
v___x_609_ = l_Lean_Expr_fvarId_x21(v_a_608_);
lean_inc_ref(v_a_587_);
v___x_610_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_587_, v___x_609_, v___y_595_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_624_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_624_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; 
v___x_615_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_588_, v_a_608_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = lean_unbox(v_a_611_);
lean_dec(v_a_611_);
if (v___x_616_ == 0)
{
lean_del_object(v___x_613_);
v_a_600_ = v___x_607_;
goto v___jp_599_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec_ref(v_a_587_);
lean_inc(v_a_608_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_a_589_);
lean_ctor_set(v___x_617_, 1, v_a_608_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_606_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_620_);
v___x_622_ = v___x_613_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_del_object(v___x_613_);
lean_dec(v_a_611_);
v_a_600_ = v___x_607_;
goto v___jp_599_;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_a_589_);
lean_dec_ref(v_a_587_);
v_a_625_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_610_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_610_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
v___jp_599_:
{
size_t v___x_601_; size_t v___x_602_; 
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_add(v_i_592_, v___x_601_);
lean_inc_ref(v_a_600_);
v_i_592_ = v___x_602_;
v_b_593_ = v_a_600_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_587_ = stack[0].m_obj;
lean_object* v_indices_588_ = stack[1].m_obj;
lean_object* v_a_589_ = stack[2].m_obj;
lean_object* v_as_590_ = stack[3].m_obj;
size_t v_sz_591_ = stack[4].m_num;
size_t v_i_592_ = stack[5].m_num;
lean_object* v_b_593_ = stack[6].m_obj;
lean_object* v___y_594_ = stack[7].m_obj;
lean_object* v___y_595_ = stack[8].m_obj;
lean_object* v___y_596_ = stack[9].m_obj;
lean_object* v___y_597_ = stack[10].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_587_, v_indices_588_, v_a_589_, v_as_590_, v_sz_591_, v_i_592_, v_b_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_634_, lean_object* v_indices_635_, lean_object* v_a_636_, lean_object* v_as_637_, lean_object* v_sz_638_, lean_object* v_i_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_638_);
lean_dec(v_sz_638_);
v_i_boxed_647_ = lean_unbox_usize(v_i_639_);
lean_dec(v_i_639_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_634_, v_indices_635_, v_a_636_, v_as_637_, v_sz_boxed_646_, v_i_boxed_647_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_as_637_);
lean_dec_ref(v_indices_635_);
return v_res_648_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_649_, lean_object* v_indices_650_, lean_object* v_as_651_, size_t v_sz_652_, size_t v_i_653_, lean_object* v_b_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_lt(v_i_653_, v_sz_652_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v_b_654_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_665_; 
lean_dec_ref(v_b_654_);
v___x_662_ = lean_box(0);
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_664_ = lean_array_uget_borrowed(v_as_651_, v_i_653_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v_a_664_);
v___x_665_ = lean_infer_type(v_a_664_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; size_t v_sz_667_; size_t v___x_668_; lean_object* v___x_669_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_sz_667_ = lean_array_size(v_ys_649_);
v___x_668_ = ((size_t)0ULL);
lean_inc(v_a_664_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_666_, v_indices_650_, v_a_664_, v_ys_649_, v_sz_667_, v___x_668_, v___x_663_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_689_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_fst_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_687_; 
v_fst_674_ = lean_ctor_get(v_a_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_a_670_, 1);
lean_dec(v_unused_688_);
v___x_676_ = v_a_670_;
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_fst_674_);
lean_dec(v_a_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_fst_674_) == 0)
{
size_t v___x_678_; size_t v___x_679_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_672_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_653_, v___x_678_);
v_i_653_ = v___x_679_;
v_b_654_ = v___x_663_;
goto _start;
}
else
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_662_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_662_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_682_);
v___x_684_ = v___x_672_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
else
{
return v___x_669_;
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_665_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_665_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_649_ = stack[0].m_obj;
lean_object* v_indices_650_ = stack[1].m_obj;
lean_object* v_as_651_ = stack[2].m_obj;
size_t v_sz_652_ = stack[3].m_num;
size_t v_i_653_ = stack[4].m_num;
lean_object* v_b_654_ = stack[5].m_obj;
lean_object* v___y_655_ = stack[6].m_obj;
lean_object* v___y_656_ = stack[7].m_obj;
lean_object* v___y_657_ = stack[8].m_obj;
lean_object* v___y_658_ = stack[9].m_obj;
lean_object* v_res_698_;
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_649_, v_indices_650_, v_as_651_, v_sz_652_, v_i_653_, v_b_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_699_, lean_object* v_indices_700_, lean_object* v_as_701_, lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
size_t v_sz_boxed_710_; size_t v_i_boxed_711_; lean_object* v_res_712_; 
v_sz_boxed_710_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_711_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_699_, v_indices_700_, v_as_701_, v_sz_boxed_710_, v_i_boxed_711_, v_b_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v_as_701_);
lean_dec_ref(v_indices_700_);
lean_dec_ref(v_ys_699_);
return v_res_712_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_713_, lean_object* v_ys_714_, lean_object* v_as_715_, size_t v_sz_716_, size_t v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_717_, v_sz_716_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_718_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_729_; 
lean_dec_ref(v_b_718_);
v___x_726_ = lean_box(0);
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_728_ = lean_array_uget_borrowed(v_as_715_, v_i_717_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v_a_728_);
v___x_729_ = lean_infer_type(v_a_728_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v_sz_731_ = lean_array_size(v_ys_714_);
v___x_732_ = ((size_t)0ULL);
lean_inc(v_a_728_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_730_, v_indices_713_, v_a_728_, v_ys_714_, v_sz_731_, v___x_732_, v___x_727_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_753_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_753_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_751_; 
v_fst_738_ = lean_ctor_get(v_a_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v_a_734_, 1);
lean_dec(v_unused_752_);
v___x_740_ = v_a_734_;
v_isShared_741_ = v_isSharedCheck_751_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_fst_738_);
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_751_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_fst_738_) == 0)
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_740_);
lean_del_object(v___x_736_);
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_717_, v___x_742_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_714_, v_indices_713_, v_as_715_, v_sz_716_, v___x_743_, v___x_727_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_744_;
}
else
{
lean_object* v___x_746_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_726_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_726_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_746_);
v___x_748_ = v___x_736_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
else
{
return v___x_733_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_729_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_729_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_indices_713_ = stack[0].m_obj;
lean_object* v_ys_714_ = stack[1].m_obj;
lean_object* v_as_715_ = stack[2].m_obj;
size_t v_sz_716_ = stack[3].m_num;
size_t v_i_717_ = stack[4].m_num;
lean_object* v_b_718_ = stack[5].m_obj;
lean_object* v___y_719_ = stack[6].m_obj;
lean_object* v___y_720_ = stack[7].m_obj;
lean_object* v___y_721_ = stack[8].m_obj;
lean_object* v___y_722_ = stack[9].m_obj;
lean_object* v_res_762_;
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_713_, v_ys_714_, v_as_715_, v_sz_716_, v_i_717_, v_b_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_763_, lean_object* v_ys_764_, lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
size_t v_sz_boxed_774_; size_t v_i_boxed_775_; lean_object* v_res_776_; 
v_sz_boxed_774_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_775_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_763_, v_ys_764_, v_as_765_, v_sz_boxed_774_, v_i_boxed_775_, v_b_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec_ref(v_as_765_);
lean_dec_ref(v_ys_764_);
lean_dec_ref(v_indices_763_);
return v_res_776_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_777_, lean_object* v_indices_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; size_t v_sz_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_784_ = lean_box(0);
v___x_785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_786_ = lean_array_size(v_indices_778_);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_778_, v_ys_777_, v_indices_778_, v_sz_786_, v___x_787_, v___x_785_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_801_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_801_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
if (lean_obj_tag(v_fst_793_) == 0)
{
lean_object* v___x_795_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_784_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_784_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v_fst_793_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_fst_793_, 1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_val_797_);
v___x_799_ = v___x_791_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_788_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_788_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_777_ = stack[0].m_obj;
lean_object* v_indices_778_ = stack[1].m_obj;
lean_object* v_a_779_ = stack[2].m_obj;
lean_object* v_a_780_ = stack[3].m_obj;
lean_object* v_a_781_ = stack[4].m_obj;
lean_object* v_a_782_ = stack[5].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_777_, v_indices_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_811_, lean_object* v_indices_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_811_, v_indices_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec_ref(v_indices_812_);
lean_dec_ref(v_ys_811_);
return v_res_818_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_819_, lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec_ref(v_a_819_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v_b_823_);
return v___x_827_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_b_823_);
v___x_828_ = lean_box(0);
v___x_829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_830_ = lean_array_uget_borrowed(v_as_820_, v_i_822_);
v___x_831_ = l_Lean_Expr_fvarId_x21(v_a_830_);
lean_inc_ref(v_a_819_);
v___x_832_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_819_, v___x_831_, v___y_824_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_848_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_848_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
uint8_t v___x_837_; 
v___x_837_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
if (v___x_837_ == 0)
{
size_t v___x_838_; size_t v___x_839_; 
lean_del_object(v___x_835_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_i_822_, v___x_838_);
v_i_822_ = v___x_839_;
v_b_823_ = v___x_829_;
goto _start;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
lean_inc(v_a_830_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_819_);
lean_ctor_set(v___x_841_, 1, v_a_830_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___x_828_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_844_);
v___x_846_ = v___x_835_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_a_819_);
v_a_849_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_832_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_832_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_819_ = stack[0].m_obj;
lean_object* v_as_820_ = stack[1].m_obj;
size_t v_sz_821_ = stack[2].m_num;
size_t v_i_822_ = stack[3].m_num;
lean_object* v_b_823_ = stack[4].m_obj;
lean_object* v___y_824_ = stack[5].m_obj;
lean_object* v_res_857_;
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_819_, v_as_820_, v_sz_821_, v_i_822_, v_b_823_, v___y_824_);
stack->m_obj
 = v_res_857_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_858_, lean_object* v_as_859_, lean_object* v_sz_860_, lean_object* v_i_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
size_t v_sz_boxed_865_; size_t v_i_boxed_866_; lean_object* v_res_867_; 
v_sz_boxed_865_ = lean_unbox_usize(v_sz_860_);
lean_dec(v_sz_860_);
v_i_boxed_866_ = lean_unbox_usize(v_i_861_);
lean_dec(v_i_861_);
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_858_, v_as_859_, v_sz_boxed_865_, v_i_boxed_866_, v_b_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v_as_859_);
return v_res_867_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_868_, lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_878_; 
v___x_878_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_b_872_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_b_872_);
v___x_880_ = lean_box(0);
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_882_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
v_sz_883_ = lean_array_size(v_ys_868_);
v___x_884_ = ((size_t)0ULL);
lean_inc(v_a_882_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_882_, v_ys_868_, v_sz_883_, v___x_884_, v___x_881_, v___y_874_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_905_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_905_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_905_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_905_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_fst_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_903_; 
v_fst_890_ = lean_ctor_get(v_a_886_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_886_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_a_886_, 1);
lean_dec(v_unused_904_);
v___x_892_ = v_a_886_;
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_fst_890_);
lean_dec(v_a_886_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
if (lean_obj_tag(v_fst_890_) == 0)
{
size_t v___x_894_; size_t v___x_895_; 
lean_del_object(v___x_892_);
lean_del_object(v___x_888_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_871_, v___x_894_);
v_i_871_ = v___x_895_;
v_b_872_ = v___x_881_;
goto _start;
}
else
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_880_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_880_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_898_);
v___x_900_ = v___x_888_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
return v___x_885_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_868_ = stack[0].m_obj;
lean_object* v_as_869_ = stack[1].m_obj;
size_t v_sz_870_ = stack[2].m_num;
size_t v_i_871_ = stack[3].m_num;
lean_object* v_b_872_ = stack[4].m_obj;
lean_object* v___y_873_ = stack[5].m_obj;
lean_object* v___y_874_ = stack[6].m_obj;
lean_object* v___y_875_ = stack[7].m_obj;
lean_object* v___y_876_ = stack[8].m_obj;
lean_object* v_res_906_;
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_868_, v_as_869_, v_sz_870_, v_i_871_, v_b_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_907_, lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_918_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_907_, v_as_908_, v_sz_boxed_917_, v_i_boxed_918_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_as_908_);
lean_dec_ref(v_ys_907_);
return v_res_919_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_920_, lean_object* v_indParams_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; size_t v_sz_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___x_927_ = lean_box(0);
v___x_928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_929_ = lean_array_size(v_indParams_921_);
v___x_930_ = ((size_t)0ULL);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_920_, v_indParams_921_, v_sz_929_, v___x_930_, v___x_928_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_944_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_944_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_fst_936_; 
v_fst_936_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_fst_936_);
lean_dec(v_a_932_);
if (lean_obj_tag(v_fst_936_) == 0)
{
lean_object* v___x_938_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_927_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_927_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; 
v_val_940_ = lean_ctor_get(v_fst_936_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v_fst_936_, 1);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_val_940_);
v___x_942_ = v___x_934_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_val_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_931_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_931_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_920_ = stack[0].m_obj;
lean_object* v_indParams_921_ = stack[1].m_obj;
lean_object* v_a_922_ = stack[2].m_obj;
lean_object* v_a_923_ = stack[3].m_obj;
lean_object* v_a_924_ = stack[4].m_obj;
lean_object* v_a_925_ = stack[5].m_obj;
lean_object* v_res_953_;
v_res_953_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_920_, v_indParams_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_954_, lean_object* v_indParams_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_954_, v_indParams_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec_ref(v_indParams_955_);
lean_dec_ref(v_ys_954_);
return v_res_961_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_962_, lean_object* v_as_963_, size_t v_sz_964_, size_t v_i_965_, lean_object* v_b_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_962_, v_as_963_, v_sz_964_, v_i_965_, v_b_966_, v___y_968_);
return v___x_972_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_962_ = stack[0].m_obj;
lean_object* v_as_963_ = stack[1].m_obj;
size_t v_sz_964_ = stack[2].m_num;
size_t v_i_965_ = stack[3].m_num;
lean_object* v_b_966_ = stack[4].m_obj;
lean_object* v___y_967_ = stack[5].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v___y_969_ = stack[7].m_obj;
lean_object* v___y_970_ = stack[8].m_obj;
lean_object* v_res_973_;
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_962_, v_as_963_, v_sz_964_, v_i_965_, v_b_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_974_, lean_object* v_as_975_, lean_object* v_sz_976_, lean_object* v_i_977_, lean_object* v_b_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
size_t v_sz_boxed_984_; size_t v_i_boxed_985_; lean_object* v_res_986_; 
v_sz_boxed_984_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_985_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_974_, v_as_975_, v_sz_boxed_984_, v_i_boxed_985_, v_b_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec_ref(v_as_975_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_panic_fn_borrowed(v___x_988_, v_msg_987_);
return v___x_989_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___f_997_; lean_object* v___x_4718__overap_998_; lean_object* v___x_999_; 
v___f_997_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4718__overap_998_ = lean_panic_fn_borrowed(v___f_997_, v_msg_991_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
v___x_999_ = lean_apply_5(v___x_4718__overap_998_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, lean_box(0));
return v___x_999_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_991_ = stack[0].m_obj;
lean_object* v___y_992_ = stack[1].m_obj;
lean_object* v___y_993_ = stack[2].m_obj;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_msg_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_1012_ = lean_unsigned_to_nat(107u);
v___x_1013_ = lean_unsigned_to_nat(97u);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1016_ = l_mkPanicMessageWithDecl(v___x_1015_, v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_);
return v___x_1016_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_xs_1017_, size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1021_ == 0)
{
return v_bs_1020_;
}
else
{
lean_object* v_v_1022_; lean_object* v___x_1023_; lean_object* v_bs_x27_1024_; lean_object* v___y_1026_; lean_object* v___x_1031_; 
v_v_1022_ = lean_array_uget(v_bs_1020_, v_i_1019_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v_bs_x27_1024_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1023_);
v___x_1031_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_1017_, v_v_1022_);
lean_dec(v_v_1022_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3);
v___x_1033_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1032_);
v___y_1026_ = v___x_1033_;
goto v___jp_1025_;
}
else
{
lean_object* v_val_1034_; 
v_val_1034_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1034_);
lean_dec_ref_known(v___x_1031_, 1);
v___y_1026_ = v_val_1034_;
goto v___jp_1025_;
}
v___jp_1025_:
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1019_, v___x_1027_);
v___x_1029_ = lean_array_uset(v_bs_x27_1024_, v_i_1019_, v___y_1026_);
v_i_1019_ = v___x_1028_;
v_bs_1020_ = v___x_1029_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1017_ = stack[0].m_obj;
size_t v_sz_1018_ = stack[1].m_num;
size_t v_i_1019_ = stack[2].m_num;
lean_object* v_bs_1020_ = stack[3].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1017_, v_sz_1018_, v_i_1019_, v_bs_1020_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_xs_1036_, lean_object* v_sz_1037_, lean_object* v_i_1038_, lean_object* v_bs_1039_){
_start:
{
size_t v_sz_boxed_1040_; size_t v_i_boxed_1041_; lean_object* v_res_1042_; 
v_sz_boxed_1040_ = lean_unbox_usize(v_sz_1037_);
lean_dec(v_sz_1037_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1036_, v_sz_boxed_1040_, v_i_boxed_1041_, v_bs_1039_);
lean_dec_ref(v_xs_1036_);
return v_res_1042_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_ref_1049_; lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_ref_1049_ = lean_ctor_get(v___y_1046_, 2);
v___x_1050_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc(v_ref_1049_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ref_1049_);
lean_ctor_set(v___x_1055_, 1, v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1043_ = stack[0].m_obj;
lean_object* v___y_1044_ = stack[1].m_obj;
lean_object* v___y_1045_ = stack[2].m_obj;
lean_object* v___y_1046_ = stack[3].m_obj;
lean_object* v___y_1047_ = stack[4].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(lean_object* v_xs_1068_, lean_object* v_v_1069_, lean_object* v_i_1070_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_array_get_size(v_xs_1068_);
v___x_1072_ = lean_nat_dec_lt(v_i_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_i_1070_);
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_array_fget_borrowed(v_xs_1068_, v_i_1070_);
v___x_1075_ = lean_name_eq(v___x_1074_, v_v_1069_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_i_1070_, v___x_1076_);
lean_dec(v_i_1070_);
v_i_1070_ = v___x_1077_;
goto _start;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_i_1070_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7___boxed(lean_object* v_xs_1080_, lean_object* v_v_1081_, lean_object* v_i_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1080_, v_v_1081_, v_i_1082_);
lean_dec(v_v_1081_);
lean_dec_ref(v_xs_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(lean_object* v_xs_1084_, lean_object* v_v_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1084_, v_v_1085_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5___boxed(lean_object* v_xs_1088_, lean_object* v_v_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1088_, v_v_1089_);
lean_dec(v_v_1089_);
lean_dec_ref(v_xs_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1091_, lean_object* v_v_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1091_, v_v_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_val_1095_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1093_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_val_1095_);
lean_dec(v___x_1093_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_val_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1103_, lean_object* v_v_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1103_, v_v_1104_);
lean_dec(v_v_1104_);
lean_dec_ref(v_xs_1103_);
return v_res_1105_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_i_1106_, lean_object* v___x_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v___x_1117_ = l_Lean_Expr_isFVar(v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_lt(v_i_1106_, v___x_1107_);
if (v___x_1118_ == 0)
{
goto v___jp_1111_;
}
else
{
return v___x_1118_;
}
}
else
{
goto v___jp_1111_;
}
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = 0;
return v___x_1119_;
}
v___jp_1111_:
{
size_t v___x_1112_; size_t v___x_1113_; 
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_add(v_i_1109_, v___x_1112_);
v_i_1109_ = v___x_1113_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1106_ = stack[0].m_obj;
lean_object* v___x_1107_ = stack[1].m_obj;
lean_object* v_as_1108_ = stack[2].m_obj;
size_t v_i_1109_ = stack[3].m_num;
size_t v_stop_1110_ = stack[4].m_num;
uint8_t v_res_1120_;
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1106_, v___x_1107_, v_as_1108_, v_i_1109_, v_stop_1110_);
stack->m_num = v_res_1120_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_i_1121_, lean_object* v___x_1122_, lean_object* v_as_1123_, lean_object* v_i_1124_, lean_object* v_stop_1125_){
_start:
{
size_t v_i_boxed_1126_; size_t v_stop_boxed_1127_; uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_i_boxed_1126_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_stop_boxed_1127_ = lean_unbox_usize(v_stop_1125_);
lean_dec(v_stop_1125_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1121_, v___x_1122_, v_as_1123_, v_i_boxed_1126_, v_stop_boxed_1127_);
lean_dec_ref(v_as_1123_);
lean_dec(v___x_1122_);
lean_dec(v_i_1121_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(lean_object* v_as_1130_, lean_object* v_a_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_zero_1133_; uint8_t v_isZero_1134_; 
v_zero_1133_ = lean_unsigned_to_nat(0u);
v_isZero_1134_ = lean_nat_dec_eq(v_x_1132_, v_zero_1133_);
if (v_isZero_1134_ == 1)
{
lean_dec(v_x_1132_);
return v_isZero_1134_;
}
else
{
lean_object* v_one_1135_; lean_object* v_n_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_one_1135_ = lean_unsigned_to_nat(1u);
v_n_1136_ = lean_nat_sub(v_x_1132_, v_one_1135_);
lean_dec(v_x_1132_);
v___x_1137_ = lean_array_fget_borrowed(v_as_1130_, v_n_1136_);
v___x_1138_ = lean_expr_eqv(v_a_1131_, v___x_1137_);
if (v___x_1138_ == 0)
{
v_x_1132_ = v_n_1136_;
goto _start;
}
else
{
lean_dec(v_n_1136_);
return v_isZero_1134_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1130_ = stack[0].m_obj;
lean_object* v_a_1131_ = stack[1].m_obj;
lean_object* v_x_1132_ = stack[2].m_obj;
uint8_t v_res_1140_;
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1130_, v_a_1131_, v_x_1132_);
stack->m_num = v_res_1140_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_as_1141_, lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1141_, v_a_1142_, v_x_1143_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_as_1141_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(lean_object* v_as_1146_, lean_object* v_i_1147_){
_start:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_array_get_size(v_as_1146_);
v___x_1149_ = lean_nat_dec_lt(v_i_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint8_t v___x_1150_; 
lean_dec(v_i_1147_);
v___x_1150_ = 1;
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_fget_borrowed(v_as_1146_, v_i_1147_);
lean_inc(v_i_1147_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1146_, v___x_1151_, v_i_1147_);
if (v___x_1152_ == 0)
{
lean_dec(v_i_1147_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_i_1147_, v___x_1153_);
lean_dec(v_i_1147_);
v_i_1147_ = v___x_1154_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1146_ = stack[0].m_obj;
lean_object* v_i_1147_ = stack[1].m_obj;
uint8_t v_res_1156_;
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1146_, v_i_1147_);
stack->m_num = v_res_1156_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3___boxed(lean_object* v_as_1157_, lean_object* v_i_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1157_, v_i_1158_);
lean_dec_ref(v_as_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_as_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT void l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1161_ = stack[0].m_obj;
uint8_t v_res_1164_;
v_res_1164_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_as_1161_);
stack->m_num = v_res_1164_;
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_as_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_as_1165_);
lean_dec_ref(v_as_1165_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1176_ = l_Lean_stringToMessageData(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1179_ = lean_unsigned_to_nat(59u);
v___x_1180_ = lean_unsigned_to_nat(96u);
v___x_1181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1204_ = l_Lean_stringToMessageData(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1208_; lean_object* v_dummy_1209_; 
v___x_1208_ = lean_box(0);
v_dummy_1209_ = l_Lean_Expr_sort___override(v___x_1208_);
return v_dummy_1209_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1215_ = lean_unsigned_to_nat(2u);
v___x_1216_ = lean_unsigned_to_nat(68u);
v___x_1217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1219_ = l_mkPanicMessageWithDecl(v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1232_, lean_object* v_fixedParamPerm_1233_, lean_object* v_xs_1234_, lean_object* v_i_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v_lower_1382_; lean_object* v_upper_1383_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; uint8_t v___x_1468_; 
v___x_1367_ = lean_array_get_size(v_fixedParamPerm_1233_);
v___x_1368_ = lean_array_get_size(v_xs_1234_);
v___x_1468_ = lean_nat_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1470_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1469_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_nat_dec_lt(v_i_1235_, v___x_1368_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___x_1472_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_i_1235_, v___x_1473_);
lean_dec(v_i_1235_);
v___x_1475_ = l_Nat_reprFast(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = l_Lean_MessageData_ofFormat(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1472_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Nat_reprFast(v___x_1368_);
v___x_1482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
v___x_1483_ = l_Lean_MessageData_ofFormat(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1480_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1486_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1487_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1233_, v_i_1235_);
if (v___x_1488_ == 0)
{
v___y_1441_ = v_a_1236_;
v___y_1442_ = v_a_1237_;
v___y_1443_ = v_a_1238_;
v___y_1444_ = v_a_1239_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___x_1489_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1490_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1489_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
v___jp_1241_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1247_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1246_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1247_;
}
v___jp_1248_:
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1254_);
if (v___x_1260_ == 0)
{
lean_object* v_name_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_name_1261_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_name_1261_);
lean_dec_ref(v___y_1259_);
v___x_1262_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1263_ = l_Lean_MessageData_ofName(v_name_1261_);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_indentExpr(v___y_1256_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1268_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1233_, v_xs_1234_);
v___x_1271_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1270_, v___y_1254_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
if (lean_obj_tag(v_a_1272_) == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1270_, v___y_1255_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
lean_dec_ref(v___x_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1324_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1324_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1324_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_a_1274_) == 0)
{
lean_object* v_name_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___y_1256_);
v_name_1278_ = lean_ctor_get(v___y_1259_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1259_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; lean_object* v_unused_1300_; 
v_unused_1299_ = lean_ctor_get(v___y_1259_, 2);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v___y_1259_, 1);
lean_dec(v_unused_1300_);
v___x_1280_ = v___y_1259_;
v_isShared_1281_ = v_isSharedCheck_1298_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_name_1278_);
lean_dec(v___y_1259_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1298_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_array_mk(v___y_1257_);
v___x_1283_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1282_, v_name_1278_);
lean_dec(v_name_1278_);
lean_dec_ref(v___x_1282_);
if (lean_obj_tag(v___x_1283_) == 1)
{
lean_object* v_val_1284_; size_t v_sz_1285_; size_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v_val_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_val_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_sz_1285_ = lean_array_size(v___y_1254_);
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1234_, v_sz_1285_, v___x_1286_, v___y_1254_);
v___x_1288_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1253_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 2, v___y_1255_);
lean_ctor_set(v___x_1280_, 1, v___y_1249_);
lean_ctor_set(v___x_1280_, 0, v___x_1288_);
v___x_1290_ = v___x_1280_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___y_1249_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v___y_1255_);
v___x_1290_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1291_, 0, v_fnName_1232_);
lean_ctor_set(v___x_1291_, 1, v_fixedParamPerm_1233_);
lean_ctor_set(v___x_1291_, 2, v_i_1235_);
lean_ctor_set(v___x_1291_, 3, v___x_1287_);
lean_ctor_set(v___x_1291_, 4, v___x_1290_);
lean_ctor_set(v___x_1291_, 5, v_val_1284_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1291_);
v___x_1293_ = v___x_1276_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v___x_1283_);
lean_del_object(v___x_1280_);
lean_del_object(v___x_1276_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___x_1296_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1297_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1296_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
return v___x_1297_;
}
}
}
else
{
lean_object* v_val_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1323_; 
lean_del_object(v___x_1276_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_val_1301_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v_a_1274_, 1);
v_fst_1302_ = lean_ctor_get(v_val_1301_, 0);
v_snd_1303_ = lean_ctor_get(v_val_1301_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_val_1301_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1305_ = v_val_1301_;
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_inc(v_fst_1302_);
lean_dec(v_val_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1307_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1308_ = l_Lean_indentExpr(v___y_1256_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 7);
lean_ctor_set(v___x_1305_, 1, v___x_1308_);
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1310_ = v___x_1305_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_indentExpr(v_fst_1302_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_indentExpr(v_snd_1303_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1320_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_a_1325_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1273_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1273_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_val_1333_; lean_object* v_fst_1334_; lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v___x_1270_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_val_1333_ = lean_ctor_get(v_a_1272_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_a_1272_, 1);
v_fst_1334_ = lean_ctor_get(v_val_1333_, 0);
v_snd_1335_ = lean_ctor_get(v_val_1333_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_val_1333_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1337_ = v_val_1333_;
v_isShared_1338_ = v_isSharedCheck_1358_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_inc(v_fst_1334_);
lean_dec(v_val_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1358_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_name_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_name_1339_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_name_1339_);
lean_dec_ref(v___y_1259_);
v___x_1340_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1341_ = l_Lean_MessageData_ofName(v_name_1339_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 7);
lean_ctor_set(v___x_1337_, 1, v___x_1341_);
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1344_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_indentExpr(v___y_1256_);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_indentExpr(v_fst_1334_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_indentExpr(v_snd_1335_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1355_, v___y_1251_, v___y_1252_, v___y_1250_, v___y_1258_);
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1249_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_a_1359_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1271_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1271_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1384_ = l_Array_toSubarray___redArg(v___y_1375_, v_lower_1382_, v_upper_1383_);
v___x_1385_ = l_Subarray_copy___redArg(v___x_1384_);
v___x_1386_ = lean_array_get_size(v___x_1385_);
v___x_1387_ = lean_nat_dec_lt(v___y_1374_, v___x_1386_);
lean_dec(v___y_1374_);
if (v___x_1387_ == 0)
{
v___y_1249_ = v___y_1370_;
v___y_1250_ = v___y_1371_;
v___y_1251_ = v___y_1372_;
v___y_1252_ = v___y_1379_;
v___y_1253_ = v___y_1373_;
v___y_1254_ = v___x_1385_;
v___y_1255_ = v___y_1376_;
v___y_1256_ = v___y_1380_;
v___y_1257_ = v___y_1381_;
v___y_1258_ = v___y_1377_;
v___y_1259_ = v___y_1378_;
goto v___jp_1248_;
}
else
{
if (v___x_1387_ == 0)
{
v___y_1249_ = v___y_1370_;
v___y_1250_ = v___y_1371_;
v___y_1251_ = v___y_1372_;
v___y_1252_ = v___y_1379_;
v___y_1253_ = v___y_1373_;
v___y_1254_ = v___x_1385_;
v___y_1255_ = v___y_1376_;
v___y_1256_ = v___y_1380_;
v___y_1257_ = v___y_1381_;
v___y_1258_ = v___y_1377_;
v___y_1259_ = v___y_1378_;
goto v___jp_1248_;
}
else
{
size_t v___x_1388_; size_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1386_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1235_, v___x_1368_, v___x_1385_, v___x_1388_, v___x_1389_);
if (v___x_1390_ == 0)
{
v___y_1249_ = v___y_1370_;
v___y_1250_ = v___y_1371_;
v___y_1251_ = v___y_1372_;
v___y_1252_ = v___y_1379_;
v___y_1253_ = v___y_1373_;
v___y_1254_ = v___x_1385_;
v___y_1255_ = v___y_1376_;
v___y_1256_ = v___y_1380_;
v___y_1257_ = v___y_1381_;
v___y_1258_ = v___y_1377_;
v___y_1259_ = v___y_1378_;
goto v___jp_1248_;
}
else
{
lean_object* v_name_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v___x_1385_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1370_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_name_1391_ = lean_ctor_get(v___y_1378_, 0);
lean_inc(v_name_1391_);
lean_dec_ref(v___y_1378_);
v___x_1392_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1393_ = l_Lean_MessageData_ofName(v_name_1391_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_indentExpr(v___y_1380_);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1398_, v___y_1372_, v___y_1379_, v___y_1371_, v___y_1377_);
return v___x_1399_;
}
}
}
}
v___jp_1400_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = l_Lean_LocalDecl_type(v___y_1401_);
lean_dec_ref(v___y_1401_);
v___x_1407_ = l_Lean_Meta_whnfD(v___x_1406_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = l_Lean_Expr_getAppFn(v_a_1408_);
if (lean_obj_tag(v___x_1409_) == 4)
{
lean_object* v_declName_1410_; lean_object* v_us_1411_; lean_object* v___x_1412_; lean_object* v_env_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v_declName_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_declName_1410_);
v_us_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_us_1411_);
lean_dec_ref_known(v___x_1409_, 2);
v___x_1412_ = lean_st_ref_get(v___y_1405_);
v_env_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc_ref(v_env_1413_);
lean_dec(v___x_1412_);
v___x_1414_ = 0;
v___x_1415_ = l_Lean_Environment_find_x3f(v_env_1413_, v_declName_1410_, v___x_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec(v_us_1411_);
lean_dec(v_a_1408_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___y_1242_ = v___y_1402_;
v___y_1243_ = v___y_1403_;
v___y_1244_ = v___y_1404_;
v___y_1245_ = v___y_1405_;
goto v___jp_1241_;
}
else
{
lean_object* v_val_1416_; 
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v___x_1415_, 1);
if (lean_obj_tag(v_val_1416_) == 5)
{
lean_object* v_val_1417_; lean_object* v_toConstantVal_1418_; lean_object* v_numParams_1419_; lean_object* v_all_1420_; lean_object* v_nargs_1421_; lean_object* v_dummy_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_val_1417_ = lean_ctor_get(v_val_1416_, 0);
lean_inc_ref(v_val_1417_);
lean_dec_ref_known(v_val_1416_, 1);
v_toConstantVal_1418_ = lean_ctor_get(v_val_1417_, 0);
lean_inc_ref(v_toConstantVal_1418_);
v_numParams_1419_ = lean_ctor_get(v_val_1417_, 1);
v_all_1420_ = lean_ctor_get(v_val_1417_, 3);
lean_inc(v_all_1420_);
v_nargs_1421_ = l_Lean_Expr_getAppNumArgs(v_a_1408_);
v_dummy_1422_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1421_);
v___x_1423_ = lean_mk_array(v_nargs_1421_, v_dummy_1422_);
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_sub(v_nargs_1421_, v___x_1424_);
lean_dec(v_nargs_1421_);
lean_inc(v_a_1408_);
v___x_1426_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1408_, v___x_1423_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1419_);
lean_inc_ref(v___x_1426_);
v___x_1428_ = l_Array_toSubarray___redArg(v___x_1426_, v___x_1427_, v_numParams_1419_);
v___x_1429_ = l_Subarray_copy___redArg(v___x_1428_);
v___x_1430_ = lean_array_get_size(v___x_1426_);
v___x_1431_ = lean_nat_dec_le(v_numParams_1419_, v___x_1427_);
if (v___x_1431_ == 0)
{
lean_inc(v_numParams_1419_);
v___y_1370_ = v_us_1411_;
v___y_1371_ = v___y_1404_;
v___y_1372_ = v___y_1402_;
v___y_1373_ = v_val_1417_;
v___y_1374_ = v___x_1427_;
v___y_1375_ = v___x_1426_;
v___y_1376_ = v___x_1429_;
v___y_1377_ = v___y_1405_;
v___y_1378_ = v_toConstantVal_1418_;
v___y_1379_ = v___y_1403_;
v___y_1380_ = v_a_1408_;
v___y_1381_ = v_all_1420_;
v_lower_1382_ = v_numParams_1419_;
v_upper_1383_ = v___x_1430_;
goto v___jp_1369_;
}
else
{
v___y_1370_ = v_us_1411_;
v___y_1371_ = v___y_1404_;
v___y_1372_ = v___y_1402_;
v___y_1373_ = v_val_1417_;
v___y_1374_ = v___x_1427_;
v___y_1375_ = v___x_1426_;
v___y_1376_ = v___x_1429_;
v___y_1377_ = v___y_1405_;
v___y_1378_ = v_toConstantVal_1418_;
v___y_1379_ = v___y_1403_;
v___y_1380_ = v_a_1408_;
v___y_1381_ = v_all_1420_;
v_lower_1382_ = v___x_1427_;
v_upper_1383_ = v___x_1430_;
goto v___jp_1369_;
}
}
else
{
lean_dec(v_val_1416_);
lean_dec(v_us_1411_);
lean_dec(v_a_1408_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___y_1242_ = v___y_1402_;
v___y_1243_ = v___y_1403_;
v___y_1244_ = v___y_1404_;
v___y_1245_ = v___y_1405_;
goto v___jp_1241_;
}
}
}
else
{
lean_dec_ref(v___x_1409_);
lean_dec(v_a_1408_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___y_1242_ = v___y_1402_;
v___y_1243_ = v___y_1403_;
v___y_1244_ = v___y_1404_;
v___y_1245_ = v___y_1405_;
goto v___jp_1241_;
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_a_1432_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1407_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1407_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
v___jp_1440_:
{
lean_object* v_x_1445_; lean_object* v___x_1446_; 
v_x_1445_ = lean_array_fget_borrowed(v_xs_1234_, v_i_1235_);
v___x_1446_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1445_, v___y_1441_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; uint8_t v___x_1448_; uint8_t v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = 0;
v___x_1449_ = l_Lean_LocalDecl_isLet(v_a_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
v___y_1401_ = v_a_1447_;
v___y_1402_ = v___y_1441_;
v___y_1403_ = v___y_1442_;
v___y_1404_ = v___y_1443_;
v___y_1405_ = v___y_1444_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1447_);
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v___x_1450_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1451_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1450_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_i_1235_);
lean_dec_ref(v_fixedParamPerm_1233_);
lean_dec(v_fnName_1232_);
v_a_1460_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1446_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1446_);
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
}
LEAN_EXPORT void l_Lean_Elab_Structural_getRecArgInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnName_1232_ = stack[0].m_obj;
lean_object* v_fixedParamPerm_1233_ = stack[1].m_obj;
lean_object* v_xs_1234_ = stack[2].m_obj;
lean_object* v_i_1235_ = stack[3].m_obj;
lean_object* v_a_1236_ = stack[4].m_obj;
lean_object* v_a_1237_ = stack[5].m_obj;
lean_object* v_a_1238_ = stack[6].m_obj;
lean_object* v_a_1239_ = stack[7].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1232_, v_fixedParamPerm_1233_, v_xs_1234_, v_i_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1500_, lean_object* v_fixedParamPerm_1501_, lean_object* v_xs_1502_, lean_object* v_i_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1500_, v_fixedParamPerm_1501_, v_xs_1502_, v_i_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec_ref(v_xs_1502_);
return v_res_1509_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1511_ = stack[1].m_obj;
lean_object* v___y_1512_ = stack[2].m_obj;
lean_object* v___y_1513_ = stack[3].m_obj;
lean_object* v___y_1514_ = stack[4].m_obj;
lean_object* v___y_1515_ = stack[5].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_box(0), v_msg_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_msg_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1519_, v_msg_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1526_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(lean_object* v_as_1527_, lean_object* v_a_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1527_, v_a_1528_, v_x_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1527_ = stack[0].m_obj;
lean_object* v_a_1528_ = stack[1].m_obj;
lean_object* v_x_1529_ = stack[2].m_obj;
uint8_t v_res_1532_;
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(v_as_1527_, v_a_1528_, v_x_1529_, lean_box(0));
stack->m_num = v_res_1532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___boxed(lean_object* v_as_1533_, lean_object* v_a_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(v_as_1533_, v_a_1534_, v_x_1535_, v_x_1536_);
lean_dec_ref(v_a_1534_);
lean_dec_ref(v_as_1533_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1539_, lean_object* v_e_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l_Lean_indentD(v_e_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1539_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1543_, lean_object* v_fnName_1544_, lean_object* v_fixedParamPerm_1545_, lean_object* v_args_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1543_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1544_, v_fixedParamPerm_1545_, v_args_1546_, v_a_1553_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1554_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_fixedParamPerm_1545_);
lean_dec(v_fnName_1544_);
v_a_1555_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1552_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1552_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_getRecArgInfos___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1543_ = stack[0].m_obj;
lean_object* v_fnName_1544_ = stack[1].m_obj;
lean_object* v_fixedParamPerm_1545_ = stack[2].m_obj;
lean_object* v_args_1546_ = stack[3].m_obj;
lean_object* v___y_1547_ = stack[4].m_obj;
lean_object* v___y_1548_ = stack[5].m_obj;
lean_object* v___y_1549_ = stack[6].m_obj;
lean_object* v___y_1550_ = stack[7].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1543_, v_fnName_1544_, v_fixedParamPerm_1545_, v_args_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1564_, lean_object* v_fnName_1565_, lean_object* v_fixedParamPerm_1566_, lean_object* v_args_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1564_, v_fnName_1565_, v_fixedParamPerm_1566_, v_args_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_args_1567_);
return v_res_1573_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1584_ = l_Lean_MessageData_ofFormat(v___x_1583_);
return v___x_1584_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1585_, lean_object* v_fnName_1586_, lean_object* v_fixedParamPerm_1587_, lean_object* v_args_1588_, lean_object* v_a_1589_, lean_object* v_b_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_fst_1597_; lean_object* v_snd_1598_; uint8_t v___x_1603_; 
v___x_1603_ = lean_nat_dec_lt(v_a_1589_, v_upperBound_1585_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v_a_1589_);
lean_dec_ref(v_fixedParamPerm_1587_);
lean_dec(v_fnName_1586_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_b_1590_);
return v___x_1604_;
}
else
{
lean_object* v_fst_1605_; lean_object* v_snd_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1651_; 
v_fst_1605_ = lean_ctor_get(v_b_1590_, 0);
v_snd_1606_ = lean_ctor_get(v_b_1590_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_b_1590_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1608_ = v_b_1590_;
v_isShared_1609_ = v_isSharedCheck_1651_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snd_1606_);
lean_inc(v_fst_1605_);
lean_dec(v_b_1590_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1651_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; 
lean_inc(v_a_1589_);
lean_inc_ref(v_fixedParamPerm_1587_);
lean_inc(v_fnName_1586_);
v___x_1610_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1586_, v_fixedParamPerm_1587_, v_args_1588_, v_a_1589_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
lean_del_object(v___x_1608_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = lean_array_push(v_fst_1605_, v_a_1611_);
v_fst_1597_ = v___x_1612_;
v_snd_1598_ = v_snd_1606_;
goto v___jp_1596_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1650_; 
v_a_1613_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1615_ = v___x_1610_;
v_isShared_1616_ = v_isSharedCheck_1650_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1610_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1650_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint8_t v___y_1618_; uint8_t v___x_1648_; 
v___x_1648_ = l_Lean_Exception_isInterrupt(v_a_1613_);
if (v___x_1648_ == 0)
{
uint8_t v___x_1649_; 
lean_inc(v_a_1613_);
v___x_1649_ = l_Lean_Exception_isRuntime(v_a_1613_);
v___y_1618_ = v___x_1649_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___x_1648_;
goto v___jp_1617_;
}
v___jp_1617_:
{
if (v___y_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_del_object(v___x_1615_);
v___x_1619_ = l_Lean_Elab_Structural_prettyParam(v_args_1588_, v_a_1589_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 7);
lean_ctor_set(v___x_1608_, 1, v_a_1620_);
lean_ctor_set(v___x_1608_, 0, v___x_1621_);
v___x_1623_ = v___x_1608_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_a_1620_);
v___x_1623_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
lean_inc(v_fnName_1586_);
v___x_1626_ = l_Lean_MessageData_ofName(v_fnName_1586_);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l_Lean_Exception_toMessageData(v_a_1613_);
v___x_1631_ = l_Lean_indentD(v___x_1630_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_snd_1606_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v_fst_1597_ = v_fst_1605_;
v_snd_1598_ = v___x_1635_;
goto v___jp_1596_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_a_1613_);
lean_del_object(v___x_1608_);
lean_dec(v_snd_1606_);
lean_dec(v_fst_1605_);
lean_dec(v_a_1589_);
lean_dec_ref(v_fixedParamPerm_1587_);
lean_dec(v_fnName_1586_);
v_a_1637_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1619_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1619_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v___x_1646_; 
lean_del_object(v___x_1608_);
lean_dec(v_snd_1606_);
lean_dec(v_fst_1605_);
lean_dec(v_a_1589_);
lean_dec_ref(v_fixedParamPerm_1587_);
lean_dec(v_fnName_1586_);
if (v_isShared_1616_ == 0)
{
v___x_1646_ = v___x_1615_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1613_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
v___jp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_fst_1597_);
lean_ctor_set(v___x_1599_, 1, v_snd_1598_);
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_nat_add(v_a_1589_, v___x_1600_);
lean_dec(v_a_1589_);
v_a_1589_ = v___x_1601_;
v_b_1590_ = v___x_1599_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1585_ = stack[0].m_obj;
lean_object* v_fnName_1586_ = stack[1].m_obj;
lean_object* v_fixedParamPerm_1587_ = stack[2].m_obj;
lean_object* v_args_1588_ = stack[3].m_obj;
lean_object* v_a_1589_ = stack[4].m_obj;
lean_object* v_b_1590_ = stack[5].m_obj;
lean_object* v___y_1591_ = stack[6].m_obj;
lean_object* v___y_1592_ = stack[7].m_obj;
lean_object* v___y_1593_ = stack[8].m_obj;
lean_object* v___y_1594_ = stack[9].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1585_, v_fnName_1586_, v_fixedParamPerm_1587_, v_args_1588_, v_a_1589_, v_b_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1653_, lean_object* v_fnName_1654_, lean_object* v_fixedParamPerm_1655_, lean_object* v_args_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1653_, v_fnName_1654_, v_fixedParamPerm_1655_, v_args_1656_, v_a_1657_, v_b_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_args_1656_);
lean_dec(v_upperBound_1653_);
return v_res_1664_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1665_; double v___x_1666_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_float_of_nat(v___x_1665_);
return v___x_1666_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_ref_1675_; lean_object* v___x_1676_; lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1722_; 
v_ref_1675_ = lean_ctor_get(v___y_1672_, 2);
v___x_1676_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1722_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1722_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v_traceState_1682_; lean_object* v_env_1683_; lean_object* v_nextMacroScope_1684_; lean_object* v_ngen_1685_; lean_object* v_auxDeclNGen_1686_; lean_object* v_cache_1687_; lean_object* v_recordedDeps_1688_; lean_object* v_messages_1689_; lean_object* v_infoState_1690_; lean_object* v_snapshotTasks_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1721_; 
v___x_1681_ = lean_st_ref_take(v___y_1673_);
v_traceState_1682_ = lean_ctor_get(v___x_1681_, 4);
v_env_1683_ = lean_ctor_get(v___x_1681_, 0);
v_nextMacroScope_1684_ = lean_ctor_get(v___x_1681_, 1);
v_ngen_1685_ = lean_ctor_get(v___x_1681_, 2);
v_auxDeclNGen_1686_ = lean_ctor_get(v___x_1681_, 3);
v_cache_1687_ = lean_ctor_get(v___x_1681_, 5);
v_recordedDeps_1688_ = lean_ctor_get(v___x_1681_, 6);
v_messages_1689_ = lean_ctor_get(v___x_1681_, 7);
v_infoState_1690_ = lean_ctor_get(v___x_1681_, 8);
v_snapshotTasks_1691_ = lean_ctor_get(v___x_1681_, 9);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1693_ = v___x_1681_;
v_isShared_1694_ = v_isSharedCheck_1721_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_snapshotTasks_1691_);
lean_inc(v_infoState_1690_);
lean_inc(v_messages_1689_);
lean_inc(v_recordedDeps_1688_);
lean_inc(v_cache_1687_);
lean_inc(v_traceState_1682_);
lean_inc(v_auxDeclNGen_1686_);
lean_inc(v_ngen_1685_);
lean_inc(v_nextMacroScope_1684_);
lean_inc(v_env_1683_);
lean_dec(v___x_1681_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1721_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
uint64_t v_tid_1695_; lean_object* v_traces_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1720_; 
v_tid_1695_ = lean_ctor_get_uint64(v_traceState_1682_, sizeof(void*)*1);
v_traces_1696_ = lean_ctor_get(v_traceState_1682_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_traceState_1682_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1698_ = v_traceState_1682_;
v_isShared_1699_ = v_isSharedCheck_1720_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_traces_1696_);
lean_dec(v_traceState_1682_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1720_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; double v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1703_ = 0;
v___x_1704_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1705_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1705_, 0, v_cls_1668_);
lean_ctor_set(v___x_1705_, 1, v___x_1701_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
lean_ctor_set_float(v___x_1705_, sizeof(void*)*3, v___x_1702_);
lean_ctor_set_float(v___x_1705_, sizeof(void*)*3 + 8, v___x_1702_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*3 + 16, v___x_1703_);
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1707_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v_a_1677_);
lean_ctor_set(v___x_1707_, 2, v___x_1706_);
lean_inc(v_ref_1675_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_ref_1675_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_PersistentArray_push___redArg(v_traces_1696_, v___x_1708_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1709_);
v___x_1711_ = v___x_1698_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1709_);
lean_ctor_set_uint64(v_reuseFailAlloc_1719_, sizeof(void*)*1, v_tid_1695_);
v___x_1711_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 4, v___x_1711_);
v___x_1713_ = v___x_1693_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_env_1683_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_nextMacroScope_1684_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_ngen_1685_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_auxDeclNGen_1686_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1718_, 5, v_cache_1687_);
lean_ctor_set(v_reuseFailAlloc_1718_, 6, v_recordedDeps_1688_);
lean_ctor_set(v_reuseFailAlloc_1718_, 7, v_messages_1689_);
lean_ctor_set(v_reuseFailAlloc_1718_, 8, v_infoState_1690_);
lean_ctor_set(v_reuseFailAlloc_1718_, 9, v_snapshotTasks_1691_);
v___x_1713_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = lean_st_ref_put(v___y_1673_, v___x_1713_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1700_);
v___x_1716_ = v___x_1679_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1700_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1668_ = stack[0].m_obj;
lean_object* v_msg_1669_ = stack[1].m_obj;
lean_object* v___y_1670_ = stack[2].m_obj;
lean_object* v___y_1671_ = stack[3].m_obj;
lean_object* v___y_1672_ = stack[4].m_obj;
lean_object* v___y_1673_ = stack[5].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1668_, v_msg_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1724_, lean_object* v_msg_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1724_, v_msg_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1731_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
return v___x_1734_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___f_1736_; 
v___x_1735_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1736_, 0, v___x_1735_);
return v___f_1736_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1738_ = l_Lean_stringToMessageData(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1741_; lean_object* v_recArgInfos_1742_; lean_object* v___x_1743_; 
v_report_1741_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1742_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_recArgInfos_1742_);
lean_ctor_set(v___x_1743_, 1, v_report_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1755_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1756_ = l_Lean_Name_append(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1760_, lean_object* v_fixedParamPerm_1761_, lean_object* v_xs_1762_, lean_object* v_fnName_1763_, lean_object* v_ys_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1760_) == 1)
{
lean_object* v_val_1771_; lean_object* v_ref_1772_; lean_object* v_toCold_1773_; lean_object* v_currRecDepth_1774_; lean_object* v_ref_1775_; uint16_t v_optionFlags_1776_; uint8_t v_suppressElabErrors_1777_; uint8_t v_isRecordingDeps_1778_; lean_object* v___f_1779_; lean_object* v_args_1780_; lean_object* v___f_1781_; lean_object* v_ref_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_val_1771_ = lean_ctor_get(v_termMeasure_x3f_1760_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v_termMeasure_x3f_1760_, 1);
v_ref_1772_ = lean_ctor_get(v_val_1771_, 0);
lean_inc(v_ref_1772_);
v_toCold_1773_ = lean_ctor_get(v___y_1768_, 0);
v_currRecDepth_1774_ = lean_ctor_get(v___y_1768_, 1);
v_ref_1775_ = lean_ctor_get(v___y_1768_, 2);
v_optionFlags_1776_ = lean_ctor_get_uint16(v___y_1768_, sizeof(void*)*3);
v_suppressElabErrors_1777_ = lean_ctor_get_uint8(v___y_1768_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1778_ = lean_ctor_get_uint8(v___y_1768_, sizeof(void*)*3 + 3);
v___f_1779_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1761_);
v_args_1780_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1761_, v_xs_1762_, v_ys_1764_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1781_, 0, v_val_1771_);
lean_closure_set(v___f_1781_, 1, v_fnName_1763_);
lean_closure_set(v___f_1781_, 2, v_fixedParamPerm_1761_);
lean_closure_set(v___f_1781_, 3, v_args_1780_);
v_ref_1782_ = l_Lean_replaceRef(v_ref_1772_, v_ref_1775_);
lean_dec(v_ref_1772_);
lean_inc(v_currRecDepth_1774_);
lean_inc_ref(v_toCold_1773_);
v___x_1783_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1783_, 0, v_toCold_1773_);
lean_ctor_set(v___x_1783_, 1, v_currRecDepth_1774_);
lean_ctor_set(v___x_1783_, 2, v_ref_1782_);
lean_ctor_set_uint16(v___x_1783_, sizeof(void*)*3, v_optionFlags_1776_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*3 + 2, v_suppressElabErrors_1777_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*3 + 3, v_isRecordingDeps_1778_);
v___x_1784_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1781_, v___f_1779_, v___y_1766_, v___y_1767_, v___x_1783_, v___y_1769_);
lean_dec_ref_known(v___x_1783_, 3);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1797_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1797_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1797_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_mk_empty_array_with_capacity(v___x_1789_);
v___x_1791_ = lean_array_push(v___x_1790_, v_a_1785_);
v___x_1792_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1793_);
v___x_1795_ = v___x_1787_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_a_1798_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1784_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1784_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_args_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v_termMeasure_x3f_1760_);
lean_inc_ref(v_fixedParamPerm_1761_);
v_args_1806_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1761_, v_xs_1762_, v_ys_1764_);
v___x_1807_ = lean_array_get_size(v_args_1806_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1807_, v_fnName_1763_, v_fixedParamPerm_1761_, v_args_1806_, v___x_1808_, v___x_1809_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec_ref(v_args_1806_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1846_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1846_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1846_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1845_; 
v_fst_1815_ = lean_ctor_get(v_a_1811_, 0);
v_snd_1816_ = lean_ctor_get(v_a_1811_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_a_1811_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1818_ = v_a_1811_;
v_isShared_1819_ = v_isSharedCheck_1845_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_inc(v_fst_1815_);
lean_dec(v_a_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1845_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_toCold_1827_; lean_object* v_options_1828_; uint8_t v_hasTrace_1829_; 
v_toCold_1827_ = lean_ctor_get(v___y_1768_, 0);
v_options_1828_ = lean_ctor_get(v_toCold_1827_, 2);
v_hasTrace_1829_ = lean_ctor_get_uint8(v_options_1828_, sizeof(void*)*1);
if (v_hasTrace_1829_ == 0)
{
goto v___jp_1820_;
}
else
{
lean_object* v_inheritedTraceOptions_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_inheritedTraceOptions_1830_ = lean_ctor_get(v_toCold_1827_, 11);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1832_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1830_, v_options_1828_, v___x_1832_);
if (v___x_1833_ == 0)
{
goto v___jp_1820_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1816_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v_snd_1816_);
v___x_1836_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1831_, v___x_1835_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec_ref_known(v___x_1836_, 1);
goto v___jp_1820_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_fst_1815_);
lean_del_object(v___x_1813_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; 
if (v_isShared_1819_ == 0)
{
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_snd_1816_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1822_);
v___x_1824_ = v___x_1813_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
}
else
{
return v___x_1810_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_getRecArgInfos___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_termMeasure_x3f_1760_ = stack[0].m_obj;
lean_object* v_fixedParamPerm_1761_ = stack[1].m_obj;
lean_object* v_xs_1762_ = stack[2].m_obj;
lean_object* v_fnName_1763_ = stack[3].m_obj;
lean_object* v_ys_1764_ = stack[4].m_obj;
lean_object* v_x_1765_ = stack[5].m_obj;
lean_object* v___y_1766_ = stack[6].m_obj;
lean_object* v___y_1767_ = stack[7].m_obj;
lean_object* v___y_1768_ = stack[8].m_obj;
lean_object* v___y_1769_ = stack[9].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1760_, v_fixedParamPerm_1761_, v_xs_1762_, v_fnName_1763_, v_ys_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1848_, lean_object* v_fixedParamPerm_1849_, lean_object* v_xs_1850_, lean_object* v_fnName_1851_, lean_object* v_ys_1852_, lean_object* v_x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1848_, v_fixedParamPerm_1849_, v_xs_1850_, v_fnName_1851_, v_ys_1852_, v_x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v_x_1853_);
lean_dec_ref(v_xs_1850_);
return v_res_1859_;
}
}
lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1860_, lean_object* v_fixedParamPerm_1861_, lean_object* v_xs_1862_, lean_object* v_value_1863_, lean_object* v_termMeasure_x3f_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___f_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; 
v___f_1870_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1870_, 0, v_termMeasure_x3f_1864_);
lean_closure_set(v___f_1870_, 1, v_fixedParamPerm_1861_);
lean_closure_set(v___f_1870_, 2, v_xs_1862_);
lean_closure_set(v___f_1870_, 3, v_fnName_1860_);
v___x_1871_ = 0;
v___x_1872_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1863_, v___f_1870_, v___x_1871_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1872_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_getRecArgInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnName_1860_ = stack[0].m_obj;
lean_object* v_fixedParamPerm_1861_ = stack[1].m_obj;
lean_object* v_xs_1862_ = stack[2].m_obj;
lean_object* v_value_1863_ = stack[3].m_obj;
lean_object* v_termMeasure_x3f_1864_ = stack[4].m_obj;
lean_object* v_a_1865_ = stack[5].m_obj;
lean_object* v_a_1866_ = stack[6].m_obj;
lean_object* v_a_1867_ = stack[7].m_obj;
lean_object* v_a_1868_ = stack[8].m_obj;
lean_object* v_res_1873_;
v_res_1873_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1860_, v_fixedParamPerm_1861_, v_xs_1862_, v_value_1863_, v_termMeasure_x3f_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
stack->m_obj
 = v_res_1873_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1874_, lean_object* v_fixedParamPerm_1875_, lean_object* v_xs_1876_, lean_object* v_value_1877_, lean_object* v_termMeasure_x3f_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1874_, v_fixedParamPerm_1875_, v_xs_1876_, v_value_1877_, v_termMeasure_x3f_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
return v_res_1884_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1885_, lean_object* v_fnName_1886_, lean_object* v_fixedParamPerm_1887_, lean_object* v_args_1888_, lean_object* v_inst_1889_, lean_object* v_R_1890_, lean_object* v_a_1891_, lean_object* v_b_1892_, lean_object* v_c_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1885_, v_fnName_1886_, v_fixedParamPerm_1887_, v_args_1888_, v_a_1891_, v_b_1892_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1885_ = stack[0].m_obj;
lean_object* v_fnName_1886_ = stack[1].m_obj;
lean_object* v_fixedParamPerm_1887_ = stack[2].m_obj;
lean_object* v_args_1888_ = stack[3].m_obj;
lean_object* v_a_1891_ = stack[6].m_obj;
lean_object* v_b_1892_ = stack[7].m_obj;
lean_object* v___y_1894_ = stack[9].m_obj;
lean_object* v___y_1895_ = stack[10].m_obj;
lean_object* v___y_1896_ = stack[11].m_obj;
lean_object* v___y_1897_ = stack[12].m_obj;
lean_object* v_res_1900_;
v_res_1900_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1885_, v_fnName_1886_, v_fixedParamPerm_1887_, v_args_1888_, lean_box(0), lean_box(0), v_a_1891_, v_b_1892_, lean_box(0), v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
stack->m_obj
 = v_res_1900_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1901_, lean_object* v_fnName_1902_, lean_object* v_fixedParamPerm_1903_, lean_object* v_args_1904_, lean_object* v_inst_1905_, lean_object* v_R_1906_, lean_object* v_a_1907_, lean_object* v_b_1908_, lean_object* v_c_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1901_, v_fnName_1902_, v_fixedParamPerm_1903_, v_args_1904_, v_inst_1905_, v_R_1906_, v_a_1907_, v_b_1908_, v_c_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_args_1904_);
lean_dec(v_upperBound_1901_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
return v_x_1916_;
}
else
{
lean_object* v_key_1918_; lean_object* v_value_1919_; lean_object* v_tail_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1943_; 
v_key_1918_ = lean_ctor_get(v_x_1917_, 0);
v_value_1919_ = lean_ctor_get(v_x_1917_, 1);
v_tail_1920_ = lean_ctor_get(v_x_1917_, 2);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1922_ = v_x_1917_;
v_isShared_1923_ = v_isSharedCheck_1943_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_tail_1920_);
lean_inc(v_value_1919_);
lean_inc(v_key_1918_);
lean_dec(v_x_1917_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1943_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; uint64_t v_fold_1928_; uint64_t v___x_1929_; uint64_t v___x_1930_; uint64_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1924_ = lean_array_get_size(v_x_1916_);
v___x_1925_ = lean_uint64_of_nat(v_key_1918_);
v___x_1926_ = 32ULL;
v___x_1927_ = lean_uint64_shift_right(v___x_1925_, v___x_1926_);
v_fold_1928_ = lean_uint64_xor(v___x_1925_, v___x_1927_);
v___x_1929_ = 16ULL;
v___x_1930_ = lean_uint64_shift_right(v_fold_1928_, v___x_1929_);
v___x_1931_ = lean_uint64_xor(v_fold_1928_, v___x_1930_);
v___x_1932_ = lean_uint64_to_usize(v___x_1931_);
v___x_1933_ = lean_usize_of_nat(v___x_1924_);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_sub(v___x_1933_, v___x_1934_);
v___x_1936_ = lean_usize_land(v___x_1932_, v___x_1935_);
v___x_1937_ = lean_array_uget_borrowed(v_x_1916_, v___x_1936_);
lean_inc(v___x_1937_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 2, v___x_1937_);
v___x_1939_ = v___x_1922_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_key_1918_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_value_1919_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_array_uset(v_x_1916_, v___x_1936_, v___x_1939_);
v_x_1916_ = v___x_1940_;
v_x_1917_ = v_tail_1920_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1944_, lean_object* v_source_1945_, lean_object* v_target_1946_){
_start:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = lean_array_get_size(v_source_1945_);
v___x_1948_ = lean_nat_dec_lt(v_i_1944_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_dec_ref(v_source_1945_);
lean_dec(v_i_1944_);
return v_target_1946_;
}
else
{
lean_object* v_es_1949_; lean_object* v___x_1950_; lean_object* v_source_1951_; lean_object* v_target_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_es_1949_ = lean_array_fget(v_source_1945_, v_i_1944_);
v___x_1950_ = lean_box(0);
v_source_1951_ = lean_array_fset(v_source_1945_, v_i_1944_, v___x_1950_);
v_target_1952_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1946_, v_es_1949_);
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_add(v_i_1944_, v___x_1953_);
lean_dec(v_i_1944_);
v_i_1944_ = v___x_1954_;
v_source_1945_ = v_source_1951_;
v_target_1946_ = v_target_1952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v_nbuckets_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1957_ = lean_array_get_size(v_data_1956_);
v___x_1958_ = lean_unsigned_to_nat(2u);
v_nbuckets_1959_ = lean_nat_mul(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_mk_array(v_nbuckets_1959_, v___x_1961_);
v___x_1963_ = lean_array_propagate_mark(v_data_1956_, v___x_1962_);
v___x_1964_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1960_, v_data_1956_, v___x_1963_);
return v___x_1964_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
uint8_t v___x_1967_; 
v___x_1967_ = 0;
return v___x_1967_;
}
else
{
lean_object* v_key_1968_; lean_object* v_tail_1969_; uint8_t v___x_1970_; 
v_key_1968_ = lean_ctor_get(v_x_1966_, 0);
v_tail_1969_ = lean_ctor_get(v_x_1966_, 2);
v___x_1970_ = lean_nat_dec_eq(v_key_1968_, v_a_1965_);
if (v___x_1970_ == 0)
{
v_x_1966_ = v_tail_1969_;
goto _start;
}
else
{
return v___x_1970_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1965_ = stack[0].m_obj;
lean_object* v_x_1966_ = stack[1].m_obj;
uint8_t v_res_1972_;
v_res_1972_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1965_, v_x_1966_);
stack->m_num = v_res_1972_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1973_, lean_object* v_x_1974_){
_start:
{
uint8_t v_res_1975_; lean_object* v_r_1976_; 
v_res_1975_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1973_, v_x_1974_);
lean_dec(v_x_1974_);
lean_dec(v_a_1973_);
v_r_1976_ = lean_box(v_res_1975_);
return v_r_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1977_, lean_object* v_a_1978_, lean_object* v_b_1979_){
_start:
{
lean_object* v_size_1980_; lean_object* v_buckets_1981_; lean_object* v___x_1982_; uint64_t v___x_1983_; uint64_t v___x_1984_; uint64_t v___x_1985_; uint64_t v_fold_1986_; uint64_t v___x_1987_; uint64_t v___x_1988_; uint64_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; lean_object* v_bkt_1995_; uint8_t v___x_1996_; 
v_size_1980_ = lean_ctor_get(v_m_1977_, 0);
v_buckets_1981_ = lean_ctor_get(v_m_1977_, 1);
v___x_1982_ = lean_array_get_size(v_buckets_1981_);
v___x_1983_ = lean_uint64_of_nat(v_a_1978_);
v___x_1984_ = 32ULL;
v___x_1985_ = lean_uint64_shift_right(v___x_1983_, v___x_1984_);
v_fold_1986_ = lean_uint64_xor(v___x_1983_, v___x_1985_);
v___x_1987_ = 16ULL;
v___x_1988_ = lean_uint64_shift_right(v_fold_1986_, v___x_1987_);
v___x_1989_ = lean_uint64_xor(v_fold_1986_, v___x_1988_);
v___x_1990_ = lean_uint64_to_usize(v___x_1989_);
v___x_1991_ = lean_usize_of_nat(v___x_1982_);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_sub(v___x_1991_, v___x_1992_);
v___x_1994_ = lean_usize_land(v___x_1990_, v___x_1993_);
v_bkt_1995_ = lean_array_uget_borrowed(v_buckets_1981_, v___x_1994_);
v___x_1996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1978_, v_bkt_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2017_; 
lean_inc_ref(v_buckets_1981_);
lean_inc(v_size_1980_);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_m_1977_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; 
v_unused_2018_ = lean_ctor_get(v_m_1977_, 1);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_m_1977_, 0);
lean_dec(v_unused_2019_);
v___x_1998_ = v_m_1977_;
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_m_1977_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2017_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v_size_x27_2001_; lean_object* v___x_2002_; lean_object* v_buckets_x27_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2000_ = lean_unsigned_to_nat(1u);
v_size_x27_2001_ = lean_nat_add(v_size_1980_, v___x_2000_);
lean_dec(v_size_1980_);
lean_inc(v_bkt_1995_);
v___x_2002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1978_);
lean_ctor_set(v___x_2002_, 1, v_b_1979_);
lean_ctor_set(v___x_2002_, 2, v_bkt_1995_);
v_buckets_x27_2003_ = lean_array_uset(v_buckets_1981_, v___x_1994_, v___x_2002_);
v___x_2004_ = lean_unsigned_to_nat(4u);
v___x_2005_ = lean_nat_mul(v_size_x27_2001_, v___x_2004_);
v___x_2006_ = lean_unsigned_to_nat(3u);
v___x_2007_ = lean_nat_div(v___x_2005_, v___x_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_array_get_size(v_buckets_x27_2003_);
v___x_2009_ = lean_nat_dec_le(v___x_2007_, v___x_2008_);
lean_dec(v___x_2007_);
if (v___x_2009_ == 0)
{
lean_object* v_val_2010_; lean_object* v___x_2012_; 
v_val_2010_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_2003_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v_val_2010_);
lean_ctor_set(v___x_1998_, 0, v_size_x27_2001_);
v___x_2012_ = v___x_1998_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_size_x27_2001_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_val_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
lean_object* v___x_2015_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v_buckets_x27_2003_);
lean_ctor_set(v___x_1998_, 0, v_size_x27_2001_);
v___x_2015_ = v___x_1998_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_size_x27_2001_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_buckets_x27_2003_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_dec(v_b_1979_);
lean_dec(v_a_1978_);
return v_m_1977_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_lt(v_i_2022_, v_sz_2021_);
if (v___x_2024_ == 0)
{
return v_b_2023_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; 
v_a_2025_ = lean_array_uget_borrowed(v_as_2020_, v_i_2022_);
v___x_2026_ = lean_box(0);
lean_inc(v_a_2025_);
v___x_2027_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_2023_, v_a_2025_, v___x_2026_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2022_, v___x_2028_);
v_i_2022_ = v___x_2029_;
v_b_2023_ = v___x_2027_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2020_ = stack[0].m_obj;
size_t v_sz_2021_ = stack[1].m_num;
size_t v_i_2022_ = stack[2].m_num;
lean_object* v_b_2023_ = stack[3].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_2020_, v_sz_2021_, v_i_2022_, v_b_2023_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_){
_start:
{
size_t v_sz_boxed_2036_; size_t v_i_boxed_2037_; lean_object* v_res_2038_; 
v_sz_boxed_2036_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2037_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_2032_, v_sz_boxed_2036_, v_i_boxed_2037_, v_b_2035_);
lean_dec_ref(v_as_2032_);
return v_res_2038_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2039_, size_t v_sz_2040_, size_t v_i_2041_, lean_object* v_b_2042_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_usize_dec_lt(v_i_2041_, v_sz_2040_);
if (v___x_2043_ == 0)
{
return v_b_2042_;
}
else
{
lean_object* v_a_2044_; lean_object* v_indicesPos_2045_; size_t v_sz_2046_; size_t v___x_2047_; lean_object* v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; 
v_a_2044_ = lean_array_uget_borrowed(v_as_2039_, v_i_2041_);
v_indicesPos_2045_ = lean_ctor_get(v_a_2044_, 3);
v_sz_2046_ = lean_array_size(v_indicesPos_2045_);
v___x_2047_ = ((size_t)0ULL);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2045_, v_sz_2046_, v___x_2047_, v_b_2042_);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2041_, v___x_2049_);
v_i_2041_ = v___x_2050_;
v_b_2042_ = v___x_2048_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2039_ = stack[0].m_obj;
size_t v_sz_2040_ = stack[1].m_num;
size_t v_i_2041_ = stack[2].m_num;
lean_object* v_b_2042_ = stack[3].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2039_, v_sz_2040_, v_i_2041_, v_b_2042_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_){
_start:
{
size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2053_, v_sz_boxed_2057_, v_i_boxed_2058_, v_b_2056_);
lean_dec_ref(v_as_2053_);
return v_res_2059_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_buckets_2062_; lean_object* v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v_fold_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_buckets_2062_ = lean_ctor_get(v_m_2060_, 1);
v___x_2063_ = lean_array_get_size(v_buckets_2062_);
v___x_2064_ = lean_uint64_of_nat(v_a_2061_);
v___x_2065_ = 32ULL;
v___x_2066_ = lean_uint64_shift_right(v___x_2064_, v___x_2065_);
v_fold_2067_ = lean_uint64_xor(v___x_2064_, v___x_2066_);
v___x_2068_ = 16ULL;
v___x_2069_ = lean_uint64_shift_right(v_fold_2067_, v___x_2068_);
v___x_2070_ = lean_uint64_xor(v_fold_2067_, v___x_2069_);
v___x_2071_ = lean_uint64_to_usize(v___x_2070_);
v___x_2072_ = lean_usize_of_nat(v___x_2063_);
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_sub(v___x_2072_, v___x_2073_);
v___x_2075_ = lean_usize_land(v___x_2071_, v___x_2074_);
v___x_2076_ = lean_array_uget_borrowed(v_buckets_2062_, v___x_2075_);
v___x_2077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2061_, v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2060_ = stack[0].m_obj;
lean_object* v_a_2061_ = stack[1].m_obj;
uint8_t v_res_2078_;
v_res_2078_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2060_, v_a_2061_);
stack->m_num = v_res_2078_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2079_, lean_object* v_a_2080_){
_start:
{
uint8_t v_res_2081_; lean_object* v_r_2082_; 
v_res_2081_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_m_2079_);
v_r_2082_ = lean_box(v_res_2081_);
return v_r_2082_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2083_, lean_object* v_as_2084_, size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_b_2087_){
_start:
{
lean_object* v_a_2089_; uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2093_ == 0)
{
return v_b_2087_;
}
else
{
lean_object* v_fst_2094_; lean_object* v_snd_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2110_; 
v_fst_2094_ = lean_ctor_get(v_b_2087_, 0);
v_snd_2095_ = lean_ctor_get(v_b_2087_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_b_2087_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2097_ = v_b_2087_;
v_isShared_2098_ = v_isSharedCheck_2110_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snd_2095_);
lean_inc(v_fst_2094_);
lean_dec(v_b_2087_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2110_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_a_2099_; lean_object* v_recArgPos_2100_; uint8_t v___x_2101_; 
v_a_2099_ = lean_array_uget_borrowed(v_as_2084_, v_i_2086_);
v_recArgPos_2100_ = lean_ctor_get(v_a_2099_, 2);
v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2083_, v_recArgPos_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_inc(v_a_2099_);
v___x_2102_ = lean_array_push(v_snd_2095_, v_a_2099_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2102_);
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fst_2094_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v_a_2089_ = v___x_2104_;
goto v___jp_2088_;
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_inc(v_a_2099_);
v___x_2106_ = lean_array_push(v_fst_2094_, v_a_2099_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2106_);
v___x_2108_ = v___x_2097_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_snd_2095_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
v_a_2089_ = v___x_2108_;
goto v___jp_2088_;
}
}
}
}
v___jp_2088_:
{
size_t v___x_2090_; size_t v___x_2091_; 
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_add(v_i_2086_, v___x_2090_);
v_i_2086_ = v___x_2091_;
v_b_2087_ = v_a_2089_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2083_ = stack[0].m_obj;
lean_object* v_as_2084_ = stack[1].m_obj;
size_t v_sz_2085_ = stack[2].m_num;
size_t v_i_2086_ = stack[3].m_num;
lean_object* v_b_2087_ = stack[4].m_obj;
lean_object* v_res_2111_;
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2083_, v_as_2084_, v_sz_2085_, v_i_2086_, v_b_2087_);
stack->m_obj
 = v_res_2111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2112_, lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_){
_start:
{
size_t v_sz_boxed_2117_; size_t v_i_boxed_2118_; lean_object* v_res_2119_; 
v_sz_boxed_2117_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2118_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2112_, v_as_2113_, v_sz_boxed_2117_, v_i_boxed_2118_, v_b_2116_);
lean_dec_ref(v_as_2113_);
lean_dec_ref(v___x_2112_);
return v_res_2119_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_unsigned_to_nat(16u);
v___x_2122_ = lean_mk_array(v___x_2121_, v___x_2120_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_indicesPos_2125_; 
v___x_2123_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2124_ = lean_unsigned_to_nat(0u);
v_indicesPos_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2125_, 0, v___x_2124_);
lean_ctor_set(v_indicesPos_2125_, 1, v___x_2123_);
return v_indicesPos_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2128_){
_start:
{
lean_object* v_indicesPos_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v___x_2137_; 
v_indicesPos_2129_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2130_ = lean_array_size(v_recArgInfos_2128_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2128_, v_sz_2130_, v___x_2131_, v_indicesPos_2129_);
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2132_, v_recArgInfos_2128_, v_sz_2130_, v___x_2131_, v___x_2133_);
lean_dec_ref(v___x_2132_);
v_fst_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_fst_2135_);
v_snd_2136_ = lean_ctor_get(v___x_2134_, 1);
lean_inc(v_snd_2136_);
lean_dec_ref(v___x_2134_);
v___x_2137_ = l_Array_append___redArg(v_snd_2136_, v_fst_2135_);
lean_dec(v_fst_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2138_);
lean_dec_ref(v_recArgInfos_2138_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2140_, lean_object* v_m_2141_, lean_object* v_a_2142_, lean_object* v_b_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2141_, v_a_2142_, v_b_2143_);
return v___x_2144_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2145_, lean_object* v_m_2146_, lean_object* v_a_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2146_, v_a_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2146_ = stack[1].m_obj;
lean_object* v_a_2147_ = stack[2].m_obj;
uint8_t v_res_2149_;
v_res_2149_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_box(0), v_m_2146_, v_a_2147_);
stack->m_num = v_res_2149_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2150_, lean_object* v_m_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2150_, v_m_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_m_2151_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2155_, lean_object* v_a_2156_, lean_object* v_x_2157_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2156_ = stack[1].m_obj;
lean_object* v_x_2157_ = stack[2].m_obj;
uint8_t v_res_2159_;
v_res_2159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_box(0), v_a_2156_, v_x_2157_);
stack->m_num = v_res_2159_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2160_, lean_object* v_a_2161_, lean_object* v_x_2162_){
_start:
{
uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_res_2163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2160_, v_a_2161_, v_x_2162_);
lean_dec(v_x_2162_);
lean_dec(v_a_2161_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2165_, lean_object* v_data_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2168_, lean_object* v_i_2169_, lean_object* v_source_2170_, lean_object* v_target_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2169_, v_source_2170_, v_target_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2174_, v_x_2175_);
return v___x_2176_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2177_, lean_object* v_a_2178_, lean_object* v_toPure_2179_, uint8_t v_____do__lift_2180_){
_start:
{
if (v_____do__lift_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_array_push(v___y_2177_, v_a_2178_);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
v___x_2183_ = lean_apply_2(v_toPure_2179_, lean_box(0), v___x_2182_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_a_2178_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___y_2177_);
v___x_2185_ = lean_apply_2(v_toPure_2179_, lean_box(0), v___x_2184_);
return v___x_2185_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2177_ = stack[0].m_obj;
lean_object* v_a_2178_ = stack[1].m_obj;
lean_object* v_toPure_2179_ = stack[2].m_obj;
uint8_t v_____do__lift_2180_ = stack[3].m_num;
lean_object* v_res_2186_;
v_res_2186_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2177_, v_a_2178_, v_toPure_2179_, v_____do__lift_2180_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2187_, lean_object* v_a_2188_, lean_object* v_toPure_2189_, lean_object* v_____do__lift_2190_){
_start:
{
uint8_t v_____do__lift_159__boxed_2191_; lean_object* v_res_2192_; 
v_____do__lift_159__boxed_2191_ = lean_unbox(v_____do__lift_2190_);
v_res_2192_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2187_, v_a_2188_, v_toPure_2189_, v_____do__lift_159__boxed_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2193_, lean_object* v_a_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_apply_2(v_eq_2193_, v_x_2195_, v_a_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2197_, lean_object* v___x_2198_, lean_object* v_toBind_2199_, lean_object* v_eq_2200_, lean_object* v_inst_2201_, lean_object* v_a_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___f_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
lean_inc(v_toPure_2197_);
lean_inc(v_a_2202_);
lean_inc_ref(v___y_2204_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2205_, 0, v___y_2204_);
lean_closure_set(v___f_2205_, 1, v_a_2202_);
lean_closure_set(v___f_2205_, 2, v_toPure_2197_);
v___x_2206_ = lean_array_get_size(v___y_2204_);
v___x_2207_ = lean_nat_dec_lt(v___x_2198_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref(v___y_2204_);
lean_dec(v_a_2202_);
lean_dec_ref(v_inst_2201_);
lean_dec(v_eq_2200_);
v___x_2208_ = lean_box(v___x_2207_);
v___x_2209_ = lean_apply_2(v_toPure_2197_, lean_box(0), v___x_2208_);
v___x_2210_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2209_, v___f_2205_);
return v___x_2210_;
}
else
{
if (v___x_2207_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v___y_2204_);
lean_dec(v_a_2202_);
lean_dec_ref(v_inst_2201_);
lean_dec(v_eq_2200_);
v___x_2211_ = lean_box(v___x_2207_);
v___x_2212_ = lean_apply_2(v_toPure_2197_, lean_box(0), v___x_2211_);
v___x_2213_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2212_, v___f_2205_);
return v___x_2213_;
}
else
{
lean_object* v___f_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_toPure_2197_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2214_, 0, v_eq_2200_);
lean_closure_set(v___f_2214_, 1, v_a_2202_);
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2206_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2201_, v___f_2214_, v___y_2204_, v___x_2215_, v___x_2216_);
v___x_2218_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2217_, v___f_2205_);
return v___x_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2219_, lean_object* v___x_2220_, lean_object* v_toBind_2221_, lean_object* v_eq_2222_, lean_object* v_inst_2223_, lean_object* v_a_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2219_, v___x_2220_, v_toBind_2221_, v_eq_2222_, v_inst_2223_, v_a_2224_, v_x_2225_, v___y_2226_);
lean_dec(v___x_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2228_, lean_object* v_____s_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_apply_2(v_toPure_2228_, lean_box(0), v_____s_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2233_, lean_object* v_eq_2234_, lean_object* v_xs_2235_){
_start:
{
lean_object* v_toApplicative_2236_; lean_object* v_toBind_2237_; lean_object* v_toPure_2238_; lean_object* v___x_2239_; lean_object* v_ret_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_toApplicative_2236_ = lean_ctor_get(v_inst_2233_, 0);
v_toBind_2237_ = lean_ctor_get(v_inst_2233_, 1);
lean_inc_n(v_toBind_2237_, 2);
v_toPure_2238_ = lean_ctor_get(v_toApplicative_2236_, 1);
v___x_2239_ = lean_unsigned_to_nat(0u);
v_ret_2240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2233_);
lean_inc_n(v_toPure_2238_, 2);
v___f_2241_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2241_, 0, v_toPure_2238_);
lean_closure_set(v___f_2241_, 1, v___x_2239_);
lean_closure_set(v___f_2241_, 2, v_toBind_2237_);
lean_closure_set(v___f_2241_, 3, v_eq_2234_);
lean_closure_set(v___f_2241_, 4, v_inst_2233_);
v___f_2242_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2242_, 0, v_toPure_2238_);
v_sz_2243_ = lean_array_size(v_xs_2235_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2233_, v_xs_2235_, v___f_2241_, v_sz_2243_, v___x_2244_, v_ret_2240_);
v___x_2246_ = lean_apply_4(v_toBind_2237_, lean_box(0), lean_box(0), v___x_2245_, v___f_2242_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2247_, lean_object* v_00_u03b1_2248_, lean_object* v_inst_2249_, lean_object* v_eq_2250_, lean_object* v_xs_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2249_, v_eq_2250_, v_xs_2251_);
return v___x_2252_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_bs_2255_){
_start:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
if (v___x_2256_ == 0)
{
return v_bs_2255_;
}
else
{
lean_object* v_v_2257_; lean_object* v_indGroupInst_2258_; lean_object* v___x_2259_; lean_object* v_bs_x27_2260_; size_t v___x_2261_; size_t v___x_2262_; lean_object* v___x_2263_; 
v_v_2257_ = lean_array_uget_borrowed(v_bs_2255_, v_i_2254_);
v_indGroupInst_2258_ = lean_ctor_get(v_v_2257_, 4);
lean_inc_ref(v_indGroupInst_2258_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v_bs_x27_2260_ = lean_array_uset(v_bs_2255_, v_i_2254_, v___x_2259_);
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2254_, v___x_2261_);
v___x_2263_ = lean_array_uset(v_bs_x27_2260_, v_i_2254_, v_indGroupInst_2258_);
v_i_2254_ = v___x_2262_;
v_bs_2255_ = v___x_2263_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2253_ = stack[0].m_num;
size_t v_i_2254_ = stack[1].m_num;
lean_object* v_bs_2255_ = stack[2].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2253_, v_i_2254_, v_bs_2255_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_bs_2268_){
_start:
{
size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2269_, v_i_boxed_2270_, v_bs_2268_);
return v_res_2271_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2272_, lean_object* v_a_2273_, lean_object* v_as_2274_, size_t v_i_2275_, size_t v_stop_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_usize_dec_eq(v_i_2275_, v_stop_2276_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = 1;
v___x_2284_ = lean_array_uget_borrowed(v_as_2274_, v_i_2275_);
lean_inc_ref(v_eq_2272_);
lean_inc(v___y_2280_);
lean_inc_ref(v___y_2279_);
lean_inc(v___y_2278_);
lean_inc_ref(v___y_2277_);
lean_inc(v_a_2273_);
lean_inc(v___x_2284_);
v___x_2285_ = lean_apply_7(v_eq_2272_, v___x_2284_, v_a_2273_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, lean_box(0));
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2298_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2298_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2298_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_unbox(v_a_2286_);
lean_dec(v_a_2286_);
if (v___x_2290_ == 0)
{
size_t v___x_2291_; size_t v___x_2292_; 
lean_del_object(v___x_2288_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2275_, v___x_2291_);
v_i_2275_ = v___x_2292_;
goto _start;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_a_2273_);
lean_dec_ref(v_eq_2272_);
v___x_2294_ = lean_box(v___x_2283_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2294_);
v___x_2296_ = v___x_2288_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_dec(v_a_2273_);
lean_dec_ref(v_eq_2272_);
return v___x_2285_;
}
}
else
{
uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v_a_2273_);
lean_dec_ref(v_eq_2272_);
v___x_2299_ = 0;
v___x_2300_ = lean_box(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2272_ = stack[0].m_obj;
lean_object* v_a_2273_ = stack[1].m_obj;
lean_object* v_as_2274_ = stack[2].m_obj;
size_t v_i_2275_ = stack[3].m_num;
size_t v_stop_2276_ = stack[4].m_num;
lean_object* v___y_2277_ = stack[5].m_obj;
lean_object* v___y_2278_ = stack[6].m_obj;
lean_object* v___y_2279_ = stack[7].m_obj;
lean_object* v___y_2280_ = stack[8].m_obj;
lean_object* v_res_2302_;
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2272_, v_a_2273_, v_as_2274_, v_i_2275_, v_stop_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
stack->m_obj
 = v_res_2302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2303_, lean_object* v_a_2304_, lean_object* v_as_2305_, lean_object* v_i_2306_, lean_object* v_stop_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
size_t v_i_boxed_2313_; size_t v_stop_boxed_2314_; lean_object* v_res_2315_; 
v_i_boxed_2313_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_stop_boxed_2314_ = lean_unbox_usize(v_stop_2307_);
lean_dec(v_stop_2307_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2303_, v_a_2304_, v_as_2305_, v_i_boxed_2313_, v_stop_boxed_2314_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_as_2305_);
return v_res_2315_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2316_, lean_object* v_a_2317_, uint8_t v_____do__lift_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
if (v_____do__lift_2318_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_array_push(v_b_2316_, v_a_2317_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v_a_2317_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_b_2316_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_2316_ = stack[0].m_obj;
lean_object* v_a_2317_ = stack[1].m_obj;
uint8_t v_____do__lift_2318_ = stack[2].m_num;
lean_object* v___y_2319_ = stack[3].m_obj;
lean_object* v___y_2320_ = stack[4].m_obj;
lean_object* v___y_2321_ = stack[5].m_obj;
lean_object* v___y_2322_ = stack[6].m_obj;
lean_object* v_res_2329_;
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2316_, v_a_2317_, v_____do__lift_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
stack->m_obj
 = v_res_2329_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2330_, lean_object* v_a_2331_, lean_object* v_____do__lift_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v_____do__lift_1309__boxed_2338_; lean_object* v_res_2339_; 
v_____do__lift_1309__boxed_2338_ = lean_unbox(v_____do__lift_2332_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2330_, v_a_2331_, v_____do__lift_1309__boxed_2338_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2339_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2340_, lean_object* v_as_2341_, size_t v_sz_2342_, size_t v_i_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_a_2351_; lean_object* v___y_2356_; uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2343_, v_sz_2342_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec_ref(v_eq_2340_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_b_2344_);
return v___x_2376_;
}
else
{
lean_object* v___x_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2377_ = lean_unsigned_to_nat(0u);
v_a_2378_ = lean_array_uget_borrowed(v_as_2341_, v_i_2343_);
v___x_2379_ = lean_array_get_size(v_b_2344_);
v___x_2380_ = lean_nat_dec_lt(v___x_2377_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_inc(v_a_2378_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2344_, v_a_2378_, v___x_2380_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
v___y_2356_ = v___x_2381_;
goto v___jp_2355_;
}
else
{
if (v___x_2380_ == 0)
{
lean_object* v___x_2382_; 
lean_inc(v_a_2378_);
v___x_2382_ = lean_array_push(v_b_2344_, v_a_2378_);
v_a_2351_ = v___x_2382_;
goto v___jp_2350_;
}
else
{
size_t v___x_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((size_t)0ULL);
v___x_2384_ = lean_usize_of_nat(v___x_2379_);
lean_inc(v_a_2378_);
lean_inc_ref(v_eq_2340_);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2340_, v_a_2378_, v_b_2344_, v___x_2383_, v___x_2384_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = lean_unbox(v_a_2386_);
lean_dec(v_a_2386_);
lean_inc(v_a_2378_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2344_, v_a_2378_, v___x_2387_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
v___y_2356_ = v___x_2388_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_b_2344_);
lean_dec_ref(v_eq_2340_);
v_a_2389_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2385_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2385_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
}
v___jp_2350_:
{
size_t v___x_2352_; size_t v___x_2353_; 
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = lean_usize_add(v_i_2343_, v___x_2352_);
v_i_2343_ = v___x_2353_;
v_b_2344_ = v_a_2351_;
goto _start;
}
v___jp_2355_:
{
if (lean_obj_tag(v___y_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2366_; 
v_a_2357_ = lean_ctor_get(v___y_2356_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___y_2356_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2359_ = v___y_2356_;
v_isShared_2360_ = v_isSharedCheck_2366_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___y_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2366_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
if (lean_obj_tag(v_a_2357_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; 
lean_dec_ref(v_eq_2340_);
v_a_2361_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v_a_2357_, 1);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v_a_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v_a_2365_; 
lean_del_object(v___x_2359_);
v_a_2365_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v_a_2357_, 1);
v_a_2351_ = v_a_2365_;
goto v___jp_2350_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_eq_2340_);
v_a_2367_ = lean_ctor_get(v___y_2356_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___y_2356_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___y_2356_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___y_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2340_ = stack[0].m_obj;
lean_object* v_as_2341_ = stack[1].m_obj;
size_t v_sz_2342_ = stack[2].m_num;
size_t v_i_2343_ = stack[3].m_num;
lean_object* v_b_2344_ = stack[4].m_obj;
lean_object* v___y_2345_ = stack[5].m_obj;
lean_object* v___y_2346_ = stack[6].m_obj;
lean_object* v___y_2347_ = stack[7].m_obj;
lean_object* v___y_2348_ = stack[8].m_obj;
lean_object* v_res_2397_;
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2340_, v_as_2341_, v_sz_2342_, v_i_2343_, v_b_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
stack->m_obj
 = v_res_2397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2398_, lean_object* v_as_2399_, lean_object* v_sz_2400_, lean_object* v_i_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2398_, v_as_2399_, v_sz_boxed_2408_, v_i_boxed_2409_, v_b_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_as_2399_);
return v_res_2410_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2411_, lean_object* v_xs_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_ret_2418_; size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v_ret_2418_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2419_ = lean_array_size(v_xs_2412_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2411_, v_xs_2412_, v_sz_2419_, v___x_2420_, v_ret_2418_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2421_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2411_ = stack[0].m_obj;
lean_object* v_xs_2412_ = stack[1].m_obj;
lean_object* v___y_2413_ = stack[2].m_obj;
lean_object* v___y_2414_ = stack[3].m_obj;
lean_object* v___y_2415_ = stack[4].m_obj;
lean_object* v___y_2416_ = stack[5].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2411_, v_xs_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2423_, lean_object* v_xs_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2423_, v_xs_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec_ref(v_xs_2424_);
return v_res_2430_;
}
}
lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; size_t v_sz_2439_; size_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2438_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2439_ = lean_array_size(v_recArgInfos_2432_);
v___x_2440_ = ((size_t)0ULL);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2439_, v___x_2440_, v_recArgInfos_2432_);
v___x_2442_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2438_, v___x_2441_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec_ref(v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_inductiveGroups_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_2432_ = stack[0].m_obj;
lean_object* v_a_2433_ = stack[1].m_obj;
lean_object* v_a_2434_ = stack[2].m_obj;
lean_object* v_a_2435_ = stack[3].m_obj;
lean_object* v_a_2436_ = stack[4].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2450_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2451_, lean_object* v_eq_2452_, lean_object* v_xs_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2452_, v_xs_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2459_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2452_ = stack[1].m_obj;
lean_object* v_xs_2453_ = stack[2].m_obj;
lean_object* v___y_2454_ = stack[3].m_obj;
lean_object* v___y_2455_ = stack[4].m_obj;
lean_object* v___y_2456_ = stack[5].m_obj;
lean_object* v___y_2457_ = stack[6].m_obj;
lean_object* v_res_2460_;
v_res_2460_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_box(0), v_eq_2452_, v_xs_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_eq_2462_, lean_object* v_xs_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2461_, v_eq_2462_, v_xs_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_xs_2463_);
return v_res_2469_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2470_, lean_object* v_eq_2471_, lean_object* v_a_2472_, lean_object* v_as_2473_, size_t v_i_2474_, size_t v_stop_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2471_, v_a_2472_, v_as_2473_, v_i_2474_, v_stop_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2471_ = stack[1].m_obj;
lean_object* v_a_2472_ = stack[2].m_obj;
lean_object* v_as_2473_ = stack[3].m_obj;
size_t v_i_2474_ = stack[4].m_num;
size_t v_stop_2475_ = stack[5].m_num;
lean_object* v___y_2476_ = stack[6].m_obj;
lean_object* v___y_2477_ = stack[7].m_obj;
lean_object* v___y_2478_ = stack[8].m_obj;
lean_object* v___y_2479_ = stack[9].m_obj;
lean_object* v_res_2482_;
v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_box(0), v_eq_2471_, v_a_2472_, v_as_2473_, v_i_2474_, v_stop_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
stack->m_obj
 = v_res_2482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2483_, lean_object* v_eq_2484_, lean_object* v_a_2485_, lean_object* v_as_2486_, lean_object* v_i_2487_, lean_object* v_stop_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
size_t v_i_boxed_2494_; size_t v_stop_boxed_2495_; lean_object* v_res_2496_; 
v_i_boxed_2494_ = lean_unbox_usize(v_i_2487_);
lean_dec(v_i_2487_);
v_stop_boxed_2495_ = lean_unbox_usize(v_stop_2488_);
lean_dec(v_stop_2488_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2483_, v_eq_2484_, v_a_2485_, v_as_2486_, v_i_boxed_2494_, v_stop_boxed_2495_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v_as_2486_);
return v_res_2496_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2497_, lean_object* v_eq_2498_, lean_object* v_as_2499_, size_t v_sz_2500_, size_t v_i_2501_, lean_object* v_b_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2498_, v_as_2499_, v_sz_2500_, v_i_2501_, v_b_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2498_ = stack[1].m_obj;
lean_object* v_as_2499_ = stack[2].m_obj;
size_t v_sz_2500_ = stack[3].m_num;
size_t v_i_2501_ = stack[4].m_num;
lean_object* v_b_2502_ = stack[5].m_obj;
lean_object* v___y_2503_ = stack[6].m_obj;
lean_object* v___y_2504_ = stack[7].m_obj;
lean_object* v___y_2505_ = stack[8].m_obj;
lean_object* v___y_2506_ = stack[9].m_obj;
lean_object* v_res_2509_;
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_box(0), v_eq_2498_, v_as_2499_, v_sz_2500_, v_i_2501_, v_b_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
stack->m_obj
 = v_res_2509_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2510_, lean_object* v_eq_2511_, lean_object* v_as_2512_, lean_object* v_sz_2513_, lean_object* v_i_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2513_);
lean_dec(v_sz_2513_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2510_, v_eq_2511_, v_as_2512_, v_sz_boxed_2521_, v_i_boxed_2522_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_as_2512_);
return v_res_2523_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = l_Lean_Expr_hasMVar(v_e_2524_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_e_2524_);
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; lean_object* v_mctx_2530_; lean_object* v___x_2531_; lean_object* v_fst_2532_; lean_object* v_snd_2533_; lean_object* v___x_2534_; lean_object* v_cache_2535_; lean_object* v_zetaDeltaFVarIds_2536_; lean_object* v_postponed_2537_; lean_object* v_diag_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2547_; 
v___x_2529_ = lean_st_ref_get(v___y_2525_);
v_mctx_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_ref(v_mctx_2530_);
lean_dec(v___x_2529_);
v___x_2531_ = l_Lean_instantiateMVarsCore(v_mctx_2530_, v_e_2524_);
v_fst_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_fst_2532_);
v_snd_2533_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2533_);
lean_dec_ref(v___x_2531_);
v___x_2534_ = lean_st_ref_take(v___y_2525_);
v_cache_2535_ = lean_ctor_get(v___x_2534_, 1);
v_zetaDeltaFVarIds_2536_ = lean_ctor_get(v___x_2534_, 2);
v_postponed_2537_ = lean_ctor_get(v___x_2534_, 3);
v_diag_2538_ = lean_ctor_get(v___x_2534_, 4);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2534_, 0);
lean_dec(v_unused_2548_);
v___x_2540_ = v___x_2534_;
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_diag_2538_);
lean_inc(v_postponed_2537_);
lean_inc(v_zetaDeltaFVarIds_2536_);
lean_inc(v_cache_2535_);
lean_dec(v___x_2534_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v_snd_2533_);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_snd_2533_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_cache_2535_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_zetaDeltaFVarIds_2536_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_postponed_2537_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_diag_2538_);
v___x_2543_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_st_ref_put(v___y_2525_, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_fst_2532_);
return v___x_2545_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2524_ = stack[0].m_obj;
lean_object* v___y_2525_ = stack[1].m_obj;
lean_object* v_res_2549_;
v_res_2549_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2524_, v___y_2525_);
stack->m_obj
 = v_res_2549_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2550_, v___y_2551_);
lean_dec(v___y_2551_);
return v_res_2553_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2554_, v___y_2556_);
return v___x_2560_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2554_ = stack[0].m_obj;
lean_object* v___y_2555_ = stack[1].m_obj;
lean_object* v___y_2556_ = stack[2].m_obj;
lean_object* v___y_2557_ = stack[3].m_obj;
lean_object* v___y_2558_ = stack[4].m_obj;
lean_object* v_res_2561_;
v_res_2561_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
stack->m_obj
 = v_res_2561_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2571_ = lean_unsigned_to_nat(109u);
v___x_2572_ = lean_unsigned_to_nat(216u);
v___x_2573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2575_ = l_mkPanicMessageWithDecl(v___x_2574_, v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_);
return v___x_2575_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2576_, size_t v_sz_2577_, size_t v_i_2578_, lean_object* v_bs_2579_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_usize_dec_lt(v_i_2578_, v_sz_2577_);
if (v___x_2580_ == 0)
{
return v_bs_2579_;
}
else
{
lean_object* v_v_2581_; lean_object* v___x_2582_; lean_object* v_bs_x27_2583_; lean_object* v___y_2585_; lean_object* v___x_2590_; 
v_v_2581_ = lean_array_uget(v_bs_2579_, v_i_2578_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v_bs_x27_2583_ = lean_array_uset(v_bs_2579_, v_i_2578_, v___x_2582_);
v___x_2590_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2576_, v_v_2581_);
lean_dec(v_v_2581_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2592_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2591_);
v___y_2585_ = v___x_2592_;
goto v___jp_2584_;
}
else
{
lean_object* v_val_2593_; 
v_val_2593_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v___x_2590_, 1);
v___y_2585_ = v_val_2593_;
goto v___jp_2584_;
}
v___jp_2584_:
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2578_, v___x_2586_);
v___x_2588_ = lean_array_uset(v_bs_x27_2583_, v_i_2578_, v___y_2585_);
v_i_2578_ = v___x_2587_;
v_bs_2579_ = v___x_2588_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2576_ = stack[0].m_obj;
size_t v_sz_2577_ = stack[1].m_num;
size_t v_i_2578_ = stack[2].m_num;
lean_object* v_bs_2579_ = stack[3].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2576_, v_sz_2577_, v_i_2578_, v_bs_2579_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2595_, lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_bs_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2595_, v_sz_boxed_2599_, v_i_boxed_2600_, v_bs_2598_);
lean_dec_ref(v___x_2595_);
return v_res_2601_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2602_, size_t v_i_2603_, lean_object* v_bs_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_usize_dec_lt(v_i_2603_, v_sz_2602_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_bs_2604_);
return v___x_2611_;
}
else
{
lean_object* v_v_2612_; lean_object* v___x_2613_; lean_object* v_bs_x27_2614_; lean_object* v___x_2615_; 
v_v_2612_ = lean_array_uget(v_bs_2604_, v_i_2603_);
v___x_2613_ = lean_unsigned_to_nat(0u);
v_bs_x27_2614_ = lean_array_uset(v_bs_2604_, v_i_2603_, v___x_2613_);
v___x_2615_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2612_, v___y_2606_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = ((size_t)1ULL);
v___x_2618_ = lean_usize_add(v_i_2603_, v___x_2617_);
v___x_2619_ = lean_array_uset(v_bs_x27_2614_, v_i_2603_, v_a_2616_);
v_i_2603_ = v___x_2618_;
v_bs_2604_ = v___x_2619_;
goto _start;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_bs_x27_2614_);
v_a_2621_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2615_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2615_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2602_ = stack[0].m_num;
size_t v_i_2603_ = stack[1].m_num;
lean_object* v_bs_2604_ = stack[2].m_obj;
lean_object* v___y_2605_ = stack[3].m_obj;
lean_object* v___y_2606_ = stack[4].m_obj;
lean_object* v___y_2607_ = stack[5].m_obj;
lean_object* v___y_2608_ = stack[6].m_obj;
lean_object* v_res_2629_;
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2602_, v_i_2603_, v_bs_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
stack->m_obj
 = v_res_2629_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2630_, lean_object* v_i_2631_, lean_object* v_bs_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2630_);
lean_dec(v_sz_2630_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2638_, v_i_boxed_2639_, v_bs_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2640_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2641_, lean_object* v___x_2642_, lean_object* v_as_2643_, size_t v_i_2644_, size_t v_stop_2645_){
_start:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_usize_dec_eq(v_i_2644_, v_stop_2645_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; uint8_t v___y_2649_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2647_ = 1;
v___x_2653_ = lean_array_uget_borrowed(v_as_2643_, v_i_2644_);
v___x_2654_ = l_Lean_Expr_isFVar(v___x_2653_);
if (v___x_2654_ == 0)
{
v___y_2649_ = v_a_2641_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_nat_dec_eq(v___x_2642_, v___x_2655_);
v___y_2649_ = v___x_2656_;
goto v___jp_2648_;
}
v___jp_2648_:
{
if (v___y_2649_ == 0)
{
size_t v___x_2650_; size_t v___x_2651_; 
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2644_, v___x_2650_);
v_i_2644_ = v___x_2651_;
goto _start;
}
else
{
return v___x_2647_;
}
}
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = 0;
return v___x_2657_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2641_ = stack[0].m_num;
lean_object* v___x_2642_ = stack[1].m_obj;
lean_object* v_as_2643_ = stack[2].m_obj;
size_t v_i_2644_ = stack[3].m_num;
size_t v_stop_2645_ = stack[4].m_num;
uint8_t v_res_2658_;
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_2641_, v___x_2642_, v_as_2643_, v_i_2644_, v_stop_2645_);
stack->m_num = v_res_2658_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2659_, lean_object* v___x_2660_, lean_object* v_as_2661_, lean_object* v_i_2662_, lean_object* v_stop_2663_){
_start:
{
uint8_t v_a_7864__boxed_2664_; size_t v_i_boxed_2665_; size_t v_stop_boxed_2666_; uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_a_7864__boxed_2664_ = lean_unbox(v_a_2659_);
v_i_boxed_2665_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_stop_boxed_2666_ = lean_unbox_usize(v_stop_2663_);
lean_dec(v_stop_2663_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7864__boxed_2664_, v___x_2660_, v_as_2661_, v_i_boxed_2665_, v_stop_boxed_2666_);
lean_dec_ref(v_as_2661_);
lean_dec(v___x_2660_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2669_, lean_object* v_ys_2670_, lean_object* v___x_2671_, lean_object* v_recArgInfo_2672_, lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v_group_2675_, lean_object* v___x_2676_, lean_object* v_as_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_b_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_a_2687_; uint8_t v___x_2691_; 
v___x_2691_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_b_2680_);
return v___x_2692_;
}
else
{
lean_object* v_snd_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2849_; 
v_snd_2693_ = lean_ctor_get(v_b_2680_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_b_2680_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_b_2680_, 0);
lean_dec(v_unused_2850_);
v___x_2695_ = v_b_2680_;
v_isShared_2696_ = v_isSharedCheck_2849_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_snd_2693_);
lean_dec(v_b_2680_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2849_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_next_2697_; lean_object* v_upperBound_2698_; lean_object* v___x_2699_; 
v_next_2697_ = lean_ctor_get(v_snd_2693_, 0);
lean_inc(v_next_2697_);
v_upperBound_2698_ = lean_ctor_get(v_snd_2693_, 1);
v___x_2699_ = lean_box(0);
if (lean_obj_tag(v_next_2697_) == 0)
{
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
goto v___jp_2700_;
}
else
{
lean_object* v_val_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2848_; 
v_val_2705_ = lean_ctor_get(v_next_2697_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_next_2697_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2707_ = v_next_2697_;
v_isShared_2708_ = v_isSharedCheck_2848_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_val_2705_);
lean_dec(v_next_2697_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2848_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_lt(v_val_2705_, v_upperBound_2698_);
if (v___x_2709_ == 0)
{
lean_del_object(v___x_2707_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
goto v___jp_2700_;
}
else
{
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2845_; 
lean_inc(v_upperBound_2698_);
lean_del_object(v___x_2695_);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_snd_2693_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; lean_object* v_unused_2847_; 
v_unused_2846_ = lean_ctor_get(v_snd_2693_, 1);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_snd_2693_, 0);
lean_dec(v_unused_2847_);
v___x_2711_ = v_snd_2693_;
v_isShared_2712_ = v_isSharedCheck_2845_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v_snd_2693_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2845_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v_a_2713_ = lean_array_uget_borrowed(v_as_2677_, v_i_2679_);
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_nat_add(v_val_2705_, v___x_2714_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2715_);
v___x_2717_ = v___x_2707_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2717_);
v___x_2719_ = v___x_2711_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_upperBound_2698_);
v___x_2719_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; 
lean_inc(v___y_2684_);
lean_inc_ref(v___y_2683_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
lean_inc_ref(v___x_2669_);
v___x_2720_ = lean_infer_type(v___x_2669_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = l_Lean_Meta_whnfD(v_a_2721_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = 0;
lean_inc(v_a_2713_);
v___x_2725_ = l_Lean_Meta_forallMetaTelescope(v_a_2713_, v___x_2724_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2818_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v_snd_2727_ = lean_ctor_get(v_a_2726_, 1);
v_fst_2728_ = lean_ctor_get(v_a_2726_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2730_ = v_a_2726_;
v_isShared_2731_ = v_isSharedCheck_2818_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snd_2727_);
lean_inc(v_fst_2728_);
lean_dec(v_a_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2818_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_snd_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2816_; 
v_snd_2732_ = lean_ctor_get(v_snd_2727_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_snd_2727_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v_snd_2727_, 0);
lean_dec(v_unused_2817_);
v___x_2734_ = v_snd_2727_;
v_isShared_2735_ = v_isSharedCheck_2816_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_snd_2732_);
lean_dec(v_snd_2727_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2816_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2732_, v_a_2723_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_unbox(v_a_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2740_; 
lean_dec(v_a_2737_);
lean_del_object(v___x_2730_);
lean_dec(v_fst_2728_);
lean_dec(v_val_2705_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2719_);
lean_ctor_set(v___x_2734_, 0, v___x_2699_);
v___x_2740_ = v___x_2734_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2719_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
v_a_2687_ = v___x_2740_;
goto v___jp_2686_;
}
}
else
{
size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v_sz_2742_ = lean_array_size(v_fst_2728_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2742_, v___x_2743_, v_fst_2728_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_array_get_size(v_a_2745_);
v___x_2793_ = lean_nat_dec_lt(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_dec(v_a_2737_);
lean_del_object(v___x_2730_);
goto v___jp_2746_;
}
else
{
if (v___x_2793_ == 0)
{
lean_dec(v_a_2737_);
lean_del_object(v___x_2730_);
goto v___jp_2746_;
}
else
{
size_t v___x_2794_; uint8_t v___x_2795_; uint8_t v___x_2796_; 
v___x_2794_ = lean_usize_of_nat(v___x_2792_);
v___x_2795_ = lean_unbox(v_a_2737_);
lean_dec(v_a_2737_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2795_, v___x_2676_, v_a_2745_, v___x_2743_, v___x_2794_);
if (v___x_2796_ == 0)
{
lean_del_object(v___x_2730_);
goto v___jp_2746_;
}
else
{
lean_object* v___x_2798_; 
lean_dec(v_a_2745_);
lean_del_object(v___x_2734_);
lean_dec(v_val_2705_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v___x_2719_);
lean_ctor_set(v___x_2730_, 0, v___x_2699_);
v___x_2798_ = v___x_2730_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2719_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
v_a_2687_ = v___x_2798_;
goto v___jp_2686_;
}
}
}
}
v___jp_2746_:
{
uint8_t v___x_2747_; 
v___x_2747_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2745_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v_a_2745_);
lean_dec(v_val_2705_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2719_);
lean_ctor_set(v___x_2734_, 0, v___x_2699_);
v___x_2749_ = v___x_2734_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2719_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
v_a_2687_ = v___x_2749_;
goto v___jp_2686_;
}
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2670_, v_a_2745_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2782_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2782_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
if (lean_obj_tag(v_a_2752_) == 1)
{
lean_object* v___x_2757_; 
lean_dec_ref_known(v_a_2752_, 1);
lean_del_object(v___x_2754_);
lean_dec(v_a_2745_);
lean_dec(v_val_2705_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2719_);
lean_ctor_set(v___x_2734_, 0, v___x_2699_);
v___x_2757_ = v___x_2734_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2719_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
v_a_2687_ = v___x_2757_;
goto v___jp_2686_;
}
}
else
{
lean_object* v_fnName_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2752_);
lean_dec_ref(v___x_2669_);
v_fnName_2759_ = lean_ctor_get(v_recArgInfo_2672_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_recArgInfo_2672_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; lean_object* v_unused_2779_; lean_object* v_unused_2780_; lean_object* v_unused_2781_; 
v_unused_2777_ = lean_ctor_get(v_recArgInfo_2672_, 5);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_recArgInfo_2672_, 4);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_recArgInfo_2672_, 3);
lean_dec(v_unused_2779_);
v_unused_2780_ = lean_ctor_get(v_recArgInfo_2672_, 2);
lean_dec(v_unused_2780_);
v_unused_2781_ = lean_ctor_get(v_recArgInfo_2672_, 1);
lean_dec(v_unused_2781_);
v___x_2761_ = v_recArgInfo_2672_;
v_isShared_2762_ = v_isSharedCheck_2776_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_fnName_2759_);
lean_dec(v_recArgInfo_2672_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2776_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
size_t v_sz_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v_sz_2763_ = lean_array_size(v_a_2745_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2671_, v_sz_2763_, v___x_2743_, v_a_2745_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 5, v_val_2705_);
lean_ctor_set(v___x_2761_, 4, v_group_2675_);
lean_ctor_set(v___x_2761_, 3, v___x_2764_);
lean_ctor_set(v___x_2761_, 2, v___x_2674_);
lean_ctor_set(v___x_2761_, 1, v___x_2673_);
v___x_2766_ = v___x_2761_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_fnName_2759_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_group_2675_);
lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_val_2705_);
v___x_2766_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2719_);
lean_ctor_set(v___x_2734_, 0, v___x_2768_);
v___x_2770_ = v___x_2734_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2719_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2770_);
v___x_2772_ = v___x_2754_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2745_);
lean_del_object(v___x_2734_);
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2783_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2751_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2751_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2737_);
lean_del_object(v___x_2734_);
lean_del_object(v___x_2730_);
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2800_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2744_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2744_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_del_object(v___x_2734_);
lean_del_object(v___x_2730_);
lean_dec(v_fst_2728_);
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2808_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2736_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2736_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2723_);
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2819_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2725_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2725_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2827_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2722_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2722_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref(v___x_2719_);
lean_dec(v_val_2705_);
lean_dec_ref(v_group_2675_);
lean_dec(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_recArgInfo_2672_);
lean_dec_ref(v___x_2669_);
v_a_2835_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2720_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2720_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2702_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2699_);
v___x_2702_ = v___x_2695_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_snd_2693_);
v___x_2702_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
}
}
v___jp_2686_:
{
size_t v___x_2688_; size_t v___x_2689_; 
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2679_, v___x_2688_);
v_i_2679_ = v___x_2689_;
v_b_2680_ = v_a_2687_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2669_ = stack[0].m_obj;
lean_object* v_ys_2670_ = stack[1].m_obj;
lean_object* v___x_2671_ = stack[2].m_obj;
lean_object* v_recArgInfo_2672_ = stack[3].m_obj;
lean_object* v___x_2673_ = stack[4].m_obj;
lean_object* v___x_2674_ = stack[5].m_obj;
lean_object* v_group_2675_ = stack[6].m_obj;
lean_object* v___x_2676_ = stack[7].m_obj;
lean_object* v_as_2677_ = stack[8].m_obj;
size_t v_sz_2678_ = stack[9].m_num;
size_t v_i_2679_ = stack[10].m_num;
lean_object* v_b_2680_ = stack[11].m_obj;
lean_object* v___y_2681_ = stack[12].m_obj;
lean_object* v___y_2682_ = stack[13].m_obj;
lean_object* v___y_2683_ = stack[14].m_obj;
lean_object* v___y_2684_ = stack[15].m_obj;
lean_object* v_res_2851_;
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2669_, v_ys_2670_, v___x_2671_, v_recArgInfo_2672_, v___x_2673_, v___x_2674_, v_group_2675_, v___x_2676_, v_as_2677_, v_sz_2678_, v_i_2679_, v_b_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
stack->m_obj
 = v_res_2851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2852_ = _args[0];
lean_object* v_ys_2853_ = _args[1];
lean_object* v___x_2854_ = _args[2];
lean_object* v_recArgInfo_2855_ = _args[3];
lean_object* v___x_2856_ = _args[4];
lean_object* v___x_2857_ = _args[5];
lean_object* v_group_2858_ = _args[6];
lean_object* v___x_2859_ = _args[7];
lean_object* v_as_2860_ = _args[8];
lean_object* v_sz_2861_ = _args[9];
lean_object* v_i_2862_ = _args[10];
lean_object* v_b_2863_ = _args[11];
lean_object* v___y_2864_ = _args[12];
lean_object* v___y_2865_ = _args[13];
lean_object* v___y_2866_ = _args[14];
lean_object* v___y_2867_ = _args[15];
lean_object* v___y_2868_ = _args[16];
_start:
{
size_t v_sz_boxed_2869_; size_t v_i_boxed_2870_; lean_object* v_res_2871_; 
v_sz_boxed_2869_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2870_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2852_, v_ys_2853_, v___x_2854_, v_recArgInfo_2855_, v___x_2856_, v___x_2857_, v_group_2858_, v___x_2859_, v_as_2860_, v_sz_boxed_2869_, v_i_boxed_2870_, v_b_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_as_2860_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v_ys_2853_);
return v_res_2871_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_ys_2874_, lean_object* v___x_2875_, lean_object* v_recArgInfo_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v_group_2879_, lean_object* v_as_2880_, size_t v_sz_2881_, size_t v_i_2882_, lean_object* v_b_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_a_2890_; uint8_t v___x_2894_; 
v___x_2894_ = lean_usize_dec_lt(v_i_2882_, v_sz_2881_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_b_2883_);
return v___x_2895_;
}
else
{
lean_object* v_snd_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_3052_; 
v_snd_2896_ = lean_ctor_get(v_b_2883_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_b_2883_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v_b_2883_, 0);
lean_dec(v_unused_3053_);
v___x_2898_ = v_b_2883_;
v_isShared_2899_ = v_isSharedCheck_3052_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snd_2896_);
lean_dec(v_b_2883_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_3052_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_next_2900_; lean_object* v_upperBound_2901_; lean_object* v___x_2902_; 
v_next_2900_ = lean_ctor_get(v_snd_2896_, 0);
lean_inc(v_next_2900_);
v_upperBound_2901_ = lean_ctor_get(v_snd_2896_, 1);
v___x_2902_ = lean_box(0);
if (lean_obj_tag(v_next_2900_) == 0)
{
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
goto v___jp_2903_;
}
else
{
lean_object* v_val_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_3051_; 
v_val_2908_ = lean_ctor_get(v_next_2900_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_next_2900_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_2910_ = v_next_2900_;
v_isShared_2911_ = v_isSharedCheck_3051_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_val_2908_);
lean_dec(v_next_2900_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_3051_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_nat_dec_lt(v_val_2908_, v_upperBound_2901_);
if (v___x_2912_ == 0)
{
lean_del_object(v___x_2910_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
goto v___jp_2903_;
}
else
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3048_; 
lean_inc(v_upperBound_2901_);
lean_del_object(v___x_2898_);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_snd_2896_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; lean_object* v_unused_3050_; 
v_unused_3049_ = lean_ctor_get(v_snd_2896_, 1);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v_snd_2896_, 0);
lean_dec(v_unused_3050_);
v___x_2914_ = v_snd_2896_;
v_isShared_2915_ = v_isSharedCheck_3048_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v_snd_2896_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3048_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v_a_2916_ = lean_array_uget_borrowed(v_as_2880_, v_i_2882_);
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_nat_add(v_val_2908_, v___x_2917_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2918_);
v___x_2920_ = v___x_2910_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_3047_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2920_);
v___x_2922_ = v___x_2914_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_upperBound_2901_);
v___x_2922_ = v_reuseFailAlloc_3046_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc(v___y_2885_);
lean_inc_ref(v___y_2884_);
lean_inc_ref(v___x_2872_);
v___x_2923_ = lean_infer_type(v___x_2872_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_whnfD(v_a_2924_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = 0;
lean_inc(v_a_2916_);
v___x_2928_ = l_Lean_Meta_forallMetaTelescope(v_a_2916_, v___x_2927_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v_snd_2930_; lean_object* v_fst_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3021_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
v_snd_2930_ = lean_ctor_get(v_a_2929_, 1);
v_fst_2931_ = lean_ctor_get(v_a_2929_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_a_2929_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2933_ = v_a_2929_;
v_isShared_2934_ = v_isSharedCheck_3021_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snd_2930_);
lean_inc(v_fst_2931_);
lean_dec(v_a_2929_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3021_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_snd_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3019_; 
v_snd_2935_ = lean_ctor_get(v_snd_2930_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_snd_2930_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_snd_2930_, 0);
lean_dec(v_unused_3020_);
v___x_2937_ = v_snd_2930_;
v_isShared_2938_ = v_isSharedCheck_3019_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_snd_2935_);
lean_dec(v_snd_2930_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3019_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2935_, v_a_2926_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; uint8_t v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_unbox(v_a_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_a_2940_);
lean_del_object(v___x_2933_);
lean_dec(v_fst_2931_);
lean_dec(v_val_2908_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2922_);
lean_ctor_set(v___x_2937_, 0, v___x_2902_);
v___x_2943_ = v___x_2937_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2922_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
v_a_2890_ = v___x_2943_;
goto v___jp_2889_;
}
}
else
{
size_t v_sz_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v_sz_2945_ = lean_array_size(v_fst_2931_);
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2945_, v___x_2946_, v_fst_2931_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_array_get_size(v_a_2948_);
v___x_2996_ = lean_nat_dec_lt(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_dec(v_a_2940_);
lean_del_object(v___x_2933_);
goto v___jp_2949_;
}
else
{
if (v___x_2996_ == 0)
{
lean_dec(v_a_2940_);
lean_del_object(v___x_2933_);
goto v___jp_2949_;
}
else
{
size_t v___x_2997_; uint8_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = lean_usize_of_nat(v___x_2995_);
v___x_2998_ = lean_unbox(v_a_2940_);
lean_dec(v_a_2940_);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2998_, v___x_2873_, v_a_2948_, v___x_2946_, v___x_2997_);
if (v___x_2999_ == 0)
{
lean_del_object(v___x_2933_);
goto v___jp_2949_;
}
else
{
lean_object* v___x_3001_; 
lean_dec(v_a_2948_);
lean_del_object(v___x_2937_);
lean_dec(v_val_2908_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2922_);
lean_ctor_set(v___x_2933_, 0, v___x_2902_);
v___x_3001_ = v___x_2933_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2922_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
v_a_2890_ = v___x_3001_;
goto v___jp_2889_;
}
}
}
}
v___jp_2949_:
{
uint8_t v___x_2950_; 
v___x_2950_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2948_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v_a_2948_);
lean_dec(v_val_2908_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2922_);
lean_ctor_set(v___x_2937_, 0, v___x_2902_);
v___x_2952_ = v___x_2937_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2922_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
v_a_2890_ = v___x_2952_;
goto v___jp_2889_;
}
}
else
{
lean_object* v___x_2954_; 
v___x_2954_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2874_, v_a_2948_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2985_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2985_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2985_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
if (lean_obj_tag(v_a_2955_) == 1)
{
lean_object* v___x_2960_; 
lean_dec_ref_known(v_a_2955_, 1);
lean_del_object(v___x_2957_);
lean_dec(v_a_2948_);
lean_dec(v_val_2908_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2922_);
lean_ctor_set(v___x_2937_, 0, v___x_2902_);
v___x_2960_ = v___x_2937_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2922_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v_a_2890_ = v___x_2960_;
goto v___jp_2889_;
}
}
else
{
lean_object* v_fnName_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_a_2955_);
lean_dec_ref(v___x_2872_);
v_fnName_2962_ = lean_ctor_get(v_recArgInfo_2876_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_recArgInfo_2876_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; lean_object* v_unused_2984_; 
v_unused_2980_ = lean_ctor_get(v_recArgInfo_2876_, 5);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_recArgInfo_2876_, 4);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_recArgInfo_2876_, 3);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_recArgInfo_2876_, 2);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_recArgInfo_2876_, 1);
lean_dec(v_unused_2984_);
v___x_2964_ = v_recArgInfo_2876_;
v_isShared_2965_ = v_isSharedCheck_2979_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_fnName_2962_);
lean_dec(v_recArgInfo_2876_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2979_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
size_t v_sz_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v_sz_2966_ = lean_array_size(v_a_2948_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2875_, v_sz_2966_, v___x_2946_, v_a_2948_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 5, v_val_2908_);
lean_ctor_set(v___x_2964_, 4, v_group_2879_);
lean_ctor_set(v___x_2964_, 3, v___x_2967_);
lean_ctor_set(v___x_2964_, 2, v___x_2878_);
lean_ctor_set(v___x_2964_, 1, v___x_2877_);
v___x_2969_ = v___x_2964_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_fnName_2962_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2978_, 3, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2978_, 4, v_group_2879_);
lean_ctor_set(v_reuseFailAlloc_2978_, 5, v_val_2908_);
v___x_2969_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2922_);
lean_ctor_set(v___x_2937_, 0, v___x_2971_);
v___x_2973_ = v___x_2937_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2922_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2973_);
v___x_2975_ = v___x_2957_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_a_2948_);
lean_del_object(v___x_2937_);
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_2986_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2954_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2954_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2940_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2933_);
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_3003_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2947_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2947_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2937_);
lean_del_object(v___x_2933_);
lean_dec(v_fst_2931_);
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_3011_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2939_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2939_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2926_);
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_3022_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2928_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2928_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_3030_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2925_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2925_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_2922_);
lean_dec(v_val_2908_);
lean_dec_ref(v_group_2879_);
lean_dec(v___x_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_recArgInfo_2876_);
lean_dec_ref(v___x_2872_);
v_a_3038_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2923_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2923_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
}
}
}
v___jp_2903_:
{
lean_object* v___x_2905_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2902_);
v___x_2905_ = v___x_2898_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_snd_2896_);
v___x_2905_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
return v___x_2906_;
}
}
}
}
v___jp_2889_:
{
size_t v___x_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_add(v_i_2882_, v___x_2891_);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2872_, v_ys_2874_, v___x_2875_, v_recArgInfo_2876_, v___x_2877_, v___x_2878_, v_group_2879_, v___x_2873_, v_as_2880_, v_sz_2881_, v___x_2892_, v_a_2890_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v___x_2893_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2872_ = stack[0].m_obj;
lean_object* v___x_2873_ = stack[1].m_obj;
lean_object* v_ys_2874_ = stack[2].m_obj;
lean_object* v___x_2875_ = stack[3].m_obj;
lean_object* v_recArgInfo_2876_ = stack[4].m_obj;
lean_object* v___x_2877_ = stack[5].m_obj;
lean_object* v___x_2878_ = stack[6].m_obj;
lean_object* v_group_2879_ = stack[7].m_obj;
lean_object* v_as_2880_ = stack[8].m_obj;
size_t v_sz_2881_ = stack[9].m_num;
size_t v_i_2882_ = stack[10].m_num;
lean_object* v_b_2883_ = stack[11].m_obj;
lean_object* v___y_2884_ = stack[12].m_obj;
lean_object* v___y_2885_ = stack[13].m_obj;
lean_object* v___y_2886_ = stack[14].m_obj;
lean_object* v___y_2887_ = stack[15].m_obj;
lean_object* v_res_3054_;
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2872_, v___x_2873_, v_ys_2874_, v___x_2875_, v_recArgInfo_2876_, v___x_2877_, v___x_2878_, v_group_2879_, v_as_2880_, v_sz_2881_, v_i_2882_, v_b_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
stack->m_obj
 = v_res_3054_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_3055_ = _args[0];
lean_object* v___x_3056_ = _args[1];
lean_object* v_ys_3057_ = _args[2];
lean_object* v___x_3058_ = _args[3];
lean_object* v_recArgInfo_3059_ = _args[4];
lean_object* v___x_3060_ = _args[5];
lean_object* v___x_3061_ = _args[6];
lean_object* v_group_3062_ = _args[7];
lean_object* v_as_3063_ = _args[8];
lean_object* v_sz_3064_ = _args[9];
lean_object* v_i_3065_ = _args[10];
lean_object* v_b_3066_ = _args[11];
lean_object* v___y_3067_ = _args[12];
lean_object* v___y_3068_ = _args[13];
lean_object* v___y_3069_ = _args[14];
lean_object* v___y_3070_ = _args[15];
lean_object* v___y_3071_ = _args[16];
_start:
{
size_t v_sz_boxed_3072_; size_t v_i_boxed_3073_; lean_object* v_res_3074_; 
v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3064_);
lean_dec(v_sz_3064_);
v_i_boxed_3073_ = lean_unbox_usize(v_i_3065_);
lean_dec(v_i_3065_);
v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3055_, v___x_3056_, v_ys_3057_, v___x_3058_, v_recArgInfo_3059_, v___x_3060_, v___x_3061_, v_group_3062_, v_as_3063_, v_sz_boxed_3072_, v_i_boxed_3073_, v_b_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_as_3063_);
lean_dec_ref(v___x_3058_);
lean_dec_ref(v_ys_3057_);
lean_dec(v___x_3056_);
return v_res_3074_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3075_, lean_object* v_fixedParamPerm_3076_, lean_object* v_xs_3077_, lean_object* v___x_3078_, lean_object* v_recArgPos_3079_, lean_object* v_a_3080_, lean_object* v___x_3081_, lean_object* v___x_3082_, lean_object* v_ys_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_toIndGroupInfo_3090_; lean_object* v_all_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3129_; 
v_toIndGroupInfo_3090_ = lean_ctor_get(v_group_3075_, 0);
lean_inc_ref(v_toIndGroupInfo_3090_);
v_all_3091_ = lean_ctor_get(v_toIndGroupInfo_3090_, 0);
lean_inc_ref(v_ys_3083_);
lean_inc_ref(v_fixedParamPerm_3076_);
v___x_3092_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3076_, v_xs_3077_, v_ys_3083_);
v___x_3093_ = lean_array_get(v___x_3078_, v___x_3092_, v_recArgPos_3079_);
v___x_3094_ = lean_array_get_size(v_all_3091_);
v___x_3095_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3090_);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_toIndGroupInfo_3090_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3130_ = lean_ctor_get(v_toIndGroupInfo_3090_, 1);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_toIndGroupInfo_3090_, 0);
lean_dec(v_unused_3131_);
v___x_3097_ = v_toIndGroupInfo_3090_;
v_isShared_3098_ = v_isSharedCheck_3129_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v_toIndGroupInfo_3090_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3129_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3094_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3095_);
lean_ctor_set(v___x_3097_, 0, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3095_);
v___x_3101_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3101_);
v_sz_3104_ = lean_array_size(v_a_3080_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3093_, v___x_3081_, v_ys_3083_, v___x_3092_, v___x_3082_, v_fixedParamPerm_3076_, v_recArgPos_3079_, v_group_3075_, v_a_3080_, v_sz_3104_, v___x_3105_, v___x_3103_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v_ys_3083_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3119_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3119_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3119_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_fst_3111_; 
v_fst_3111_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_fst_3111_);
lean_dec(v_a_3107_);
if (lean_obj_tag(v_fst_3111_) == 0)
{
lean_object* v___x_3113_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3102_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3102_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
else
{
lean_object* v_val_3115_; lean_object* v___x_3117_; 
v_val_3115_ = lean_ctor_get(v_fst_3111_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v_fst_3111_, 1);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v_val_3115_);
v___x_3117_ = v___x_3109_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_val_3115_);
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
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
v_a_3120_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3106_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3106_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_group_3075_ = stack[0].m_obj;
lean_object* v_fixedParamPerm_3076_ = stack[1].m_obj;
lean_object* v_xs_3077_ = stack[2].m_obj;
lean_object* v___x_3078_ = stack[3].m_obj;
lean_object* v_recArgPos_3079_ = stack[4].m_obj;
lean_object* v_a_3080_ = stack[5].m_obj;
lean_object* v___x_3081_ = stack[6].m_obj;
lean_object* v___x_3082_ = stack[7].m_obj;
lean_object* v_ys_3083_ = stack[8].m_obj;
lean_object* v_x_3084_ = stack[9].m_obj;
lean_object* v___y_3085_ = stack[10].m_obj;
lean_object* v___y_3086_ = stack[11].m_obj;
lean_object* v___y_3087_ = stack[12].m_obj;
lean_object* v___y_3088_ = stack[13].m_obj;
lean_object* v_res_3132_;
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3075_, v_fixedParamPerm_3076_, v_xs_3077_, v___x_3078_, v_recArgPos_3079_, v_a_3080_, v___x_3081_, v___x_3082_, v_ys_3083_, v_x_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
stack->m_obj
 = v_res_3132_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3133_, lean_object* v_fixedParamPerm_3134_, lean_object* v_xs_3135_, lean_object* v___x_3136_, lean_object* v_recArgPos_3137_, lean_object* v_a_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v_ys_3141_, lean_object* v_x_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3133_, v_fixedParamPerm_3134_, v_xs_3135_, v___x_3136_, v_recArgPos_3137_, v_a_3138_, v___x_3139_, v___x_3140_, v_ys_3141_, v_x_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_x_3142_);
lean_dec(v___x_3139_);
lean_dec_ref(v_a_3138_);
lean_dec_ref(v___x_3136_);
lean_dec_ref(v_xs_3135_);
return v_res_3148_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3149_, lean_object* v_a_3150_, lean_object* v_xs_3151_, lean_object* v_value_3152_, lean_object* v_as_3153_, size_t v_i_3154_, size_t v_stop_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_a_3163_; lean_object* v_val_3168_; uint8_t v___x_3170_; 
v___x_3170_ = lean_usize_dec_eq(v_i_3154_, v_stop_3155_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; lean_object* v_fixedParamPerm_3172_; lean_object* v_recArgPos_3173_; lean_object* v_indGroupInst_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3171_ = lean_array_uget_borrowed(v_as_3153_, v_i_3154_);
v_fixedParamPerm_3172_ = lean_ctor_get(v___x_3171_, 1);
v_recArgPos_3173_ = lean_ctor_get(v___x_3171_, 2);
v_indGroupInst_3174_ = lean_ctor_get(v___x_3171_, 4);
v___x_3175_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_indGroupInst_3174_);
lean_inc_ref(v_group_3149_);
v___x_3176_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3149_, v_indGroupInst_3174_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; uint8_t v___x_3178_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = lean_unbox(v_a_3177_);
lean_dec(v_a_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3179_ = lean_array_get_size(v_a_3150_);
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_nat_dec_eq(v___x_3179_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___f_3182_; lean_object* v___x_3183_; 
lean_inc(v___x_3171_);
lean_inc_ref(v_a_3150_);
lean_inc(v_recArgPos_3173_);
lean_inc_ref(v_xs_3151_);
lean_inc_ref(v_fixedParamPerm_3172_);
lean_inc_ref(v_group_3149_);
v___f_3182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3182_, 0, v_group_3149_);
lean_closure_set(v___f_3182_, 1, v_fixedParamPerm_3172_);
lean_closure_set(v___f_3182_, 2, v_xs_3151_);
lean_closure_set(v___f_3182_, 3, v___x_3175_);
lean_closure_set(v___f_3182_, 4, v_recArgPos_3173_);
lean_closure_set(v___f_3182_, 5, v_a_3150_);
lean_closure_set(v___f_3182_, 6, v___x_3179_);
lean_closure_set(v___f_3182_, 7, v___x_3171_);
lean_inc_ref(v_value_3152_);
v___x_3183_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3152_, v___f_3182_, v___x_3181_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
if (lean_obj_tag(v_a_3184_) == 0)
{
v_a_3163_ = v_b_3156_;
goto v___jp_3162_;
}
else
{
lean_object* v_val_3185_; 
v_val_3185_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_val_3185_);
lean_dec_ref_known(v_a_3184_, 1);
v_val_3168_ = v_val_3185_;
goto v___jp_3167_;
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v_b_3156_);
lean_dec_ref(v_value_3152_);
lean_dec_ref(v_xs_3151_);
lean_dec_ref(v_a_3150_);
lean_dec_ref(v_group_3149_);
v_a_3186_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3183_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3183_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
v_a_3163_ = v_b_3156_;
goto v___jp_3162_;
}
}
else
{
lean_inc(v___x_3171_);
v_val_3168_ = v___x_3171_;
goto v___jp_3167_;
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v_b_3156_);
lean_dec_ref(v_value_3152_);
lean_dec_ref(v_xs_3151_);
lean_dec_ref(v_a_3150_);
lean_dec_ref(v_group_3149_);
v_a_3194_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3176_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3176_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v___x_3202_; 
lean_dec_ref(v_value_3152_);
lean_dec_ref(v_xs_3151_);
lean_dec_ref(v_a_3150_);
lean_dec_ref(v_group_3149_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_b_3156_);
return v___x_3202_;
}
v___jp_3162_:
{
size_t v___x_3164_; size_t v___x_3165_; 
v___x_3164_ = ((size_t)1ULL);
v___x_3165_ = lean_usize_add(v_i_3154_, v___x_3164_);
v_i_3154_ = v___x_3165_;
v_b_3156_ = v_a_3163_;
goto _start;
}
v___jp_3167_:
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_array_push(v_b_3156_, v_val_3168_);
v_a_3163_ = v___x_3169_;
goto v___jp_3162_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_group_3149_ = stack[0].m_obj;
lean_object* v_a_3150_ = stack[1].m_obj;
lean_object* v_xs_3151_ = stack[2].m_obj;
lean_object* v_value_3152_ = stack[3].m_obj;
lean_object* v_as_3153_ = stack[4].m_obj;
size_t v_i_3154_ = stack[5].m_num;
size_t v_stop_3155_ = stack[6].m_num;
lean_object* v_b_3156_ = stack[7].m_obj;
lean_object* v___y_3157_ = stack[8].m_obj;
lean_object* v___y_3158_ = stack[9].m_obj;
lean_object* v___y_3159_ = stack[10].m_obj;
lean_object* v___y_3160_ = stack[11].m_obj;
lean_object* v_res_3203_;
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3149_, v_a_3150_, v_xs_3151_, v_value_3152_, v_as_3153_, v_i_3154_, v_stop_3155_, v_b_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3204_, lean_object* v_a_3205_, lean_object* v_xs_3206_, lean_object* v_value_3207_, lean_object* v_as_3208_, lean_object* v_i_3209_, lean_object* v_stop_3210_, lean_object* v_b_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
size_t v_i_boxed_3217_; size_t v_stop_boxed_3218_; lean_object* v_res_3219_; 
v_i_boxed_3217_ = lean_unbox_usize(v_i_3209_);
lean_dec(v_i_3209_);
v_stop_boxed_3218_ = lean_unbox_usize(v_stop_3210_);
lean_dec(v_stop_3210_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3204_, v_a_3205_, v_xs_3206_, v_value_3207_, v_as_3208_, v_i_boxed_3217_, v_stop_boxed_3218_, v_b_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v_as_3208_);
return v_res_3219_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3220_, lean_object* v_a_3221_, lean_object* v_xs_3222_, lean_object* v_value_3223_, lean_object* v_as_3224_, lean_object* v_start_3225_, lean_object* v_stop_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3233_ = lean_nat_dec_lt(v_start_3225_, v_stop_3226_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref(v_value_3223_);
lean_dec_ref(v_xs_3222_);
lean_dec_ref(v_a_3221_);
lean_dec_ref(v_group_3220_);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_array_get_size(v_as_3224_);
v___x_3236_ = lean_nat_dec_le(v_stop_3226_, v___x_3235_);
if (v___x_3236_ == 0)
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_nat_dec_lt(v_start_3225_, v___x_3235_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref(v_value_3223_);
lean_dec_ref(v_xs_3222_);
lean_dec_ref(v_a_3221_);
lean_dec_ref(v_group_3220_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3232_);
return v___x_3238_;
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_usize_of_nat(v_start_3225_);
v___x_3240_ = lean_usize_of_nat(v___x_3235_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3220_, v_a_3221_, v_xs_3222_, v_value_3223_, v_as_3224_, v___x_3239_, v___x_3240_, v___x_3232_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3241_;
}
}
else
{
size_t v___x_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_usize_of_nat(v_start_3225_);
v___x_3243_ = lean_usize_of_nat(v_stop_3226_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3220_, v_a_3221_, v_xs_3222_, v_value_3223_, v_as_3224_, v___x_3242_, v___x_3243_, v___x_3232_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3244_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_group_3220_ = stack[0].m_obj;
lean_object* v_a_3221_ = stack[1].m_obj;
lean_object* v_xs_3222_ = stack[2].m_obj;
lean_object* v_value_3223_ = stack[3].m_obj;
lean_object* v_as_3224_ = stack[4].m_obj;
lean_object* v_start_3225_ = stack[5].m_obj;
lean_object* v_stop_3226_ = stack[6].m_obj;
lean_object* v___y_3227_ = stack[7].m_obj;
lean_object* v___y_3228_ = stack[8].m_obj;
lean_object* v___y_3229_ = stack[9].m_obj;
lean_object* v___y_3230_ = stack[10].m_obj;
lean_object* v_res_3245_;
v_res_3245_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3220_, v_a_3221_, v_xs_3222_, v_value_3223_, v_as_3224_, v_start_3225_, v_stop_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
stack->m_obj
 = v_res_3245_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3246_, lean_object* v_a_3247_, lean_object* v_xs_3248_, lean_object* v_value_3249_, lean_object* v_as_3250_, lean_object* v_start_3251_, lean_object* v_stop_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3246_, v_a_3247_, v_xs_3248_, v_value_3249_, v_as_3250_, v_start_3251_, v_stop_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v_stop_3252_);
lean_dec(v_start_3251_);
lean_dec_ref(v_as_3250_);
return v_res_3258_;
}
}
lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3259_, lean_object* v_xs_3260_, lean_object* v_value_3261_, lean_object* v_recArgInfos_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v___x_3268_; 
lean_inc_ref(v_group_3259_);
v___x_3268_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3259_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = lean_array_get_size(v_recArgInfos_3262_);
v___x_3272_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3259_, v_a_3269_, v_xs_3260_, v_value_3261_, v_recArgInfos_3262_, v___x_3270_, v___x_3271_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
return v___x_3272_;
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec_ref(v_value_3261_);
lean_dec_ref(v_xs_3260_);
lean_dec_ref(v_group_3259_);
v_a_3273_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3268_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3268_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_argsInGroup_0interp(lean_interpreter_value* stack)
{
lean_object* v_group_3259_ = stack[0].m_obj;
lean_object* v_xs_3260_ = stack[1].m_obj;
lean_object* v_value_3261_ = stack[2].m_obj;
lean_object* v_recArgInfos_3262_ = stack[3].m_obj;
lean_object* v_a_3263_ = stack[4].m_obj;
lean_object* v_a_3264_ = stack[5].m_obj;
lean_object* v_a_3265_ = stack[6].m_obj;
lean_object* v_a_3266_ = stack[7].m_obj;
lean_object* v_res_3281_;
v_res_3281_ = l_Lean_Elab_Structural_argsInGroup(v_group_3259_, v_xs_3260_, v_value_3261_, v_recArgInfos_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3282_, lean_object* v_xs_3283_, lean_object* v_value_3284_, lean_object* v_recArgInfos_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_Elab_Structural_argsInGroup(v_group_3282_, v_xs_3283_, v_value_3284_, v_recArgInfos_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec_ref(v_recArgInfos_3285_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_unsigned_to_nat(10u);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3295_, lean_object* v_i_3296_, lean_object* v_acc_3297_){
_start:
{
lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = lean_array_get_size(v_xss_3295_);
v___x_3299_ = lean_nat_dec_lt(v_i_3296_, v___x_3298_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_unsigned_to_nat(1u);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3300_);
v___x_3302_ = lean_array_push(v___x_3301_, v_acc_3297_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3303_ = lean_array_fget_borrowed(v_xss_3295_, v_i_3296_);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3306_ = lean_array_get_size(v___x_3303_);
v___x_3307_ = lean_nat_dec_lt(v___x_3304_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v_acc_3297_);
return v___x_3305_;
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3306_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3296_, v_acc_3297_, v_xss_3295_, v___x_3303_, v___x_3308_, v___x_3309_, v___x_3305_);
return v___x_3310_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3311_, lean_object* v_acc_3312_, lean_object* v_xss_3313_, lean_object* v_as_3314_, size_t v_i_3315_, size_t v_stop_3316_, lean_object* v_b_3317_){
_start:
{
uint8_t v___x_3318_; 
v___x_3318_ = lean_usize_dec_eq(v_i_3315_, v_stop_3316_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; size_t v___x_3325_; size_t v___x_3326_; 
v___x_3319_ = lean_array_uget_borrowed(v_as_3314_, v_i_3315_);
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_nat_add(v_i_3311_, v___x_3320_);
lean_inc(v___x_3319_);
lean_inc_ref(v_acc_3312_);
v___x_3322_ = lean_array_push(v_acc_3312_, v___x_3319_);
v___x_3323_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3313_, v___x_3321_, v___x_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = l_Array_append___redArg(v_b_3317_, v___x_3323_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = ((size_t)1ULL);
v___x_3326_ = lean_usize_add(v_i_3315_, v___x_3325_);
v_i_3315_ = v___x_3326_;
v_b_3317_ = v___x_3324_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3312_);
return v_b_3317_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3311_ = stack[0].m_obj;
lean_object* v_acc_3312_ = stack[1].m_obj;
lean_object* v_xss_3313_ = stack[2].m_obj;
lean_object* v_as_3314_ = stack[3].m_obj;
size_t v_i_3315_ = stack[4].m_num;
size_t v_stop_3316_ = stack[5].m_num;
lean_object* v_b_3317_ = stack[6].m_obj;
lean_object* v_res_3328_;
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3311_, v_acc_3312_, v_xss_3313_, v_as_3314_, v_i_3315_, v_stop_3316_, v_b_3317_);
stack->m_obj
 = v_res_3328_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3329_, lean_object* v_acc_3330_, lean_object* v_xss_3331_, lean_object* v_as_3332_, lean_object* v_i_3333_, lean_object* v_stop_3334_, lean_object* v_b_3335_){
_start:
{
size_t v_i_boxed_3336_; size_t v_stop_boxed_3337_; lean_object* v_res_3338_; 
v_i_boxed_3336_ = lean_unbox_usize(v_i_3333_);
lean_dec(v_i_3333_);
v_stop_boxed_3337_ = lean_unbox_usize(v_stop_3334_);
lean_dec(v_stop_3334_);
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3329_, v_acc_3330_, v_xss_3331_, v_as_3332_, v_i_boxed_3336_, v_stop_boxed_3337_, v_b_3335_);
lean_dec_ref(v_as_3332_);
lean_dec_ref(v_xss_3331_);
lean_dec(v_i_3329_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3339_, lean_object* v_i_3340_, lean_object* v_acc_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3339_, v_i_3340_, v_acc_3341_);
lean_dec(v_i_3340_);
lean_dec_ref(v_xss_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3343_, lean_object* v_xss_3344_, lean_object* v_i_3345_, lean_object* v_acc_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3344_, v_i_3345_, v_acc_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3348_, lean_object* v_xss_3349_, lean_object* v_i_3350_, lean_object* v_acc_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3348_, v_xss_3349_, v_i_3350_, v_acc_3351_);
lean_dec(v_i_3350_);
lean_dec_ref(v_xss_3349_);
return v_res_3352_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3353_, lean_object* v_i_3354_, lean_object* v_acc_3355_, lean_object* v_xss_3356_, lean_object* v_as_3357_, size_t v_i_3358_, size_t v_stop_3359_, lean_object* v_b_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3354_, v_acc_3355_, v_xss_3356_, v_as_3357_, v_i_3358_, v_stop_3359_, v_b_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_3354_ = stack[1].m_obj;
lean_object* v_acc_3355_ = stack[2].m_obj;
lean_object* v_xss_3356_ = stack[3].m_obj;
lean_object* v_as_3357_ = stack[4].m_obj;
size_t v_i_3358_ = stack[5].m_num;
size_t v_stop_3359_ = stack[6].m_num;
lean_object* v_b_3360_ = stack[7].m_obj;
lean_object* v_res_3362_;
v_res_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_box(0), v_i_3354_, v_acc_3355_, v_xss_3356_, v_as_3357_, v_i_3358_, v_stop_3359_, v_b_3360_);
stack->m_obj
 = v_res_3362_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_i_3364_, lean_object* v_acc_3365_, lean_object* v_xss_3366_, lean_object* v_as_3367_, lean_object* v_i_3368_, lean_object* v_stop_3369_, lean_object* v_b_3370_){
_start:
{
size_t v_i_boxed_3371_; size_t v_stop_boxed_3372_; lean_object* v_res_3373_; 
v_i_boxed_3371_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_stop_boxed_3372_ = lean_unbox_usize(v_stop_3369_);
lean_dec(v_stop_3369_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3363_, v_i_3364_, v_acc_3365_, v_xss_3366_, v_as_3367_, v_i_boxed_3371_, v_stop_boxed_3372_, v_b_3370_);
lean_dec_ref(v_as_3367_);
lean_dec_ref(v_xss_3366_);
lean_dec(v_i_3364_);
return v_res_3373_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3374_, size_t v_i_3375_, size_t v_stop_3376_, lean_object* v_b_3377_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_eq(v_i_3375_, v_stop_3376_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; 
v___x_3379_ = lean_array_uget_borrowed(v_as_3374_, v_i_3375_);
v___x_3380_ = lean_array_get_size(v___x_3379_);
v___x_3381_ = lean_nat_mul(v_b_3377_, v___x_3380_);
lean_dec(v_b_3377_);
v___x_3382_ = ((size_t)1ULL);
v___x_3383_ = lean_usize_add(v_i_3375_, v___x_3382_);
v_i_3375_ = v___x_3383_;
v_b_3377_ = v___x_3381_;
goto _start;
}
else
{
return v_b_3377_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3374_ = stack[0].m_obj;
size_t v_i_3375_ = stack[1].m_num;
size_t v_stop_3376_ = stack[2].m_num;
lean_object* v_b_3377_ = stack[3].m_obj;
lean_object* v_res_3385_;
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3374_, v_i_3375_, v_stop_3376_, v_b_3377_);
stack->m_obj
 = v_res_3385_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3386_, lean_object* v_i_3387_, lean_object* v_stop_3388_, lean_object* v_b_3389_){
_start:
{
size_t v_i_boxed_3390_; size_t v_stop_boxed_3391_; lean_object* v_res_3392_; 
v_i_boxed_3390_ = lean_unbox_usize(v_i_3387_);
lean_dec(v_i_3387_);
v_stop_boxed_3391_ = lean_unbox_usize(v_stop_3388_);
lean_dec(v_stop_3388_);
v_res_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3386_, v_i_boxed_3390_, v_stop_boxed_3391_, v_b_3389_);
lean_dec_ref(v_as_3386_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3393_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___y_3398_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3394_ = lean_unsigned_to_nat(10u);
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_unsigned_to_nat(0u);
v___x_3404_ = lean_array_get_size(v_xss_3393_);
v___x_3405_ = lean_nat_dec_lt(v___x_3396_, v___x_3404_);
if (v___x_3405_ == 0)
{
v___y_3398_ = v___x_3395_;
goto v___jp_3397_;
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = lean_nat_dec_le(v___x_3404_, v___x_3404_);
if (v___x_3406_ == 0)
{
if (v___x_3405_ == 0)
{
v___y_3398_ = v___x_3395_;
goto v___jp_3397_;
}
else
{
size_t v___x_3407_; size_t v___x_3408_; lean_object* v___x_3409_; 
v___x_3407_ = ((size_t)0ULL);
v___x_3408_ = lean_usize_of_nat(v___x_3404_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3393_, v___x_3407_, v___x_3408_, v___x_3395_);
v___y_3398_ = v___x_3409_;
goto v___jp_3397_;
}
}
else
{
size_t v___x_3410_; size_t v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = ((size_t)0ULL);
v___x_3411_ = lean_usize_of_nat(v___x_3404_);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3393_, v___x_3410_, v___x_3411_, v___x_3395_);
v___y_3398_ = v___x_3412_;
goto v___jp_3397_;
}
}
v___jp_3397_:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_nat_dec_lt(v___x_3394_, v___y_3398_);
lean_dec(v___y_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3401_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3393_, v___x_3396_, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
else
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_box(0);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3413_);
lean_dec_ref(v_xss_3413_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3415_, lean_object* v_xss_3416_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_xss_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3418_, v_xss_3419_);
lean_dec_ref(v_xss_3419_);
return v_res_3420_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3421_, lean_object* v_as_3422_, size_t v_i_3423_, size_t v_stop_3424_, lean_object* v_b_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3422_, v_i_3423_, v_stop_3424_, v_b_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3422_ = stack[1].m_obj;
size_t v_i_3423_ = stack[2].m_num;
size_t v_stop_3424_ = stack[3].m_num;
lean_object* v_b_3425_ = stack[4].m_obj;
lean_object* v_res_3427_;
v_res_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_box(0), v_as_3422_, v_i_3423_, v_stop_3424_, v_b_3425_);
stack->m_obj
 = v_res_3427_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_as_3429_, lean_object* v_i_3430_, lean_object* v_stop_3431_, lean_object* v_b_3432_){
_start:
{
size_t v_i_boxed_3433_; size_t v_stop_boxed_3434_; lean_object* v_res_3435_; 
v_i_boxed_3433_ = lean_unbox_usize(v_i_3430_);
lean_dec(v_i_3430_);
v_stop_boxed_3434_ = lean_unbox_usize(v_stop_3431_);
lean_dec(v_stop_3431_);
v_res_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3428_, v_as_3429_, v_i_boxed_3433_, v_stop_boxed_3434_, v_b_3432_);
lean_dec_ref(v_as_3429_);
return v_res_3435_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3436_, size_t v_i_3437_, size_t v_stop_3438_, lean_object* v_b_3439_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_eq(v_i_3437_, v_stop_3438_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; size_t v___x_3443_; size_t v___x_3444_; 
v___x_3441_ = lean_array_uget_borrowed(v_as_3436_, v_i_3437_);
v___x_3442_ = l_Array_append___redArg(v_b_3439_, v___x_3441_);
v___x_3443_ = ((size_t)1ULL);
v___x_3444_ = lean_usize_add(v_i_3437_, v___x_3443_);
v_i_3437_ = v___x_3444_;
v_b_3439_ = v___x_3442_;
goto _start;
}
else
{
return v_b_3439_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3436_ = stack[0].m_obj;
size_t v_i_3437_ = stack[1].m_num;
size_t v_stop_3438_ = stack[2].m_num;
lean_object* v_b_3439_ = stack[3].m_obj;
lean_object* v_res_3446_;
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3436_, v_i_3437_, v_stop_3438_, v_b_3439_);
stack->m_obj
 = v_res_3446_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3447_, lean_object* v_i_3448_, lean_object* v_stop_3449_, lean_object* v_b_3450_){
_start:
{
size_t v_i_boxed_3451_; size_t v_stop_boxed_3452_; lean_object* v_res_3453_; 
v_i_boxed_3451_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_stop_boxed_3452_ = lean_unbox_usize(v_stop_3449_);
lean_dec(v_stop_3449_);
v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3447_, v_i_boxed_3451_, v_stop_boxed_3452_, v_b_3450_);
lean_dec_ref(v_as_3447_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
if (lean_obj_tag(v_a_3454_) == 0)
{
lean_object* v___x_3456_; 
v___x_3456_ = l_List_reverse___redArg(v_a_3455_);
return v___x_3456_;
}
else
{
lean_object* v_head_3457_; lean_object* v_tail_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3468_; 
v_head_3457_ = lean_ctor_get(v_a_3454_, 0);
v_tail_3458_ = lean_ctor_get(v_a_3454_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3454_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3460_ = v_a_3454_;
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_tail_3458_);
lean_inc(v_head_3457_);
lean_dec(v_a_3454_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3462_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3457_);
v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v_a_3455_);
lean_ctor_set(v___x_3460_, 0, v___x_3463_);
v___x_3465_ = v___x_3460_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_a_3455_);
v___x_3465_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v_a_3454_ = v_tail_3458_;
v_a_3455_ = v___x_3465_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3469_, size_t v_i_3470_, lean_object* v_bs_3471_){
_start:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_usize_dec_lt(v_i_3470_, v_sz_3469_);
if (v___x_3472_ == 0)
{
return v_bs_3471_;
}
else
{
lean_object* v_v_3473_; lean_object* v___x_3474_; lean_object* v_bs_x27_3475_; lean_object* v___x_3476_; size_t v___x_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v_v_3473_ = lean_array_uget(v_bs_3471_, v_i_3470_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v_bs_x27_3475_ = lean_array_uset(v_bs_3471_, v_i_3470_, v___x_3474_);
v___x_3476_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3473_);
lean_dec(v_v_3473_);
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3470_, v___x_3477_);
v___x_3479_ = lean_array_uset(v_bs_x27_3475_, v_i_3470_, v___x_3476_);
v_i_3470_ = v___x_3478_;
v_bs_3471_ = v___x_3479_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3469_ = stack[0].m_num;
size_t v_i_3470_ = stack[1].m_num;
lean_object* v_bs_3471_ = stack[2].m_obj;
lean_object* v_res_3481_;
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_3469_, v_i_3470_, v_bs_3471_);
stack->m_obj
 = v_res_3481_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3482_, lean_object* v_i_3483_, lean_object* v_bs_3484_){
_start:
{
size_t v_sz_boxed_3485_; size_t v_i_boxed_3486_; lean_object* v_res_3487_; 
v_sz_boxed_3485_ = lean_unbox_usize(v_sz_3482_);
lean_dec(v_sz_3482_);
v_i_boxed_3486_ = lean_unbox_usize(v_i_3483_);
lean_dec(v_i_3483_);
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3485_, v_i_boxed_3486_, v_bs_3484_);
return v_res_3487_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3488_, lean_object* v_as_3489_, size_t v_sz_3490_, size_t v_i_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec_ref(v_xs_3488_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_b_3492_);
return v___x_3499_;
}
else
{
lean_object* v_snd_3500_; lean_object* v_snd_3501_; lean_object* v_snd_3502_; lean_object* v_snd_3503_; lean_object* v_fst_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3648_; 
v_snd_3500_ = lean_ctor_get(v_b_3492_, 1);
lean_inc(v_snd_3500_);
v_snd_3501_ = lean_ctor_get(v_snd_3500_, 1);
lean_inc(v_snd_3501_);
v_snd_3502_ = lean_ctor_get(v_snd_3501_, 1);
lean_inc(v_snd_3502_);
v_snd_3503_ = lean_ctor_get(v_snd_3502_, 1);
lean_inc(v_snd_3503_);
v_fst_3504_ = lean_ctor_get(v_b_3492_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_b_3492_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v_b_3492_, 1);
lean_dec(v_unused_3649_);
v___x_3506_ = v_b_3492_;
v_isShared_3507_ = v_isSharedCheck_3648_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_fst_3504_);
lean_dec(v_b_3492_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3648_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_fst_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3646_; 
v_fst_3508_ = lean_ctor_get(v_snd_3500_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_snd_3500_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; 
v_unused_3647_ = lean_ctor_get(v_snd_3500_, 1);
lean_dec(v_unused_3647_);
v___x_3510_ = v_snd_3500_;
v_isShared_3511_ = v_isSharedCheck_3646_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_fst_3508_);
lean_dec(v_snd_3500_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3646_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_fst_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3644_; 
v_fst_3512_ = lean_ctor_get(v_snd_3501_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_snd_3501_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v_snd_3501_, 1);
lean_dec(v_unused_3645_);
v___x_3514_ = v_snd_3501_;
v_isShared_3515_ = v_isSharedCheck_3644_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_fst_3512_);
lean_dec(v_snd_3501_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3644_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_fst_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3642_; 
v_fst_3516_ = lean_ctor_get(v_snd_3502_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_snd_3502_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v_snd_3502_, 1);
lean_dec(v_unused_3643_);
v___x_3518_ = v_snd_3502_;
v_isShared_3519_ = v_isSharedCheck_3642_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_fst_3516_);
lean_dec(v_snd_3502_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3642_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_array_3520_; lean_object* v_start_3521_; lean_object* v_stop_3522_; uint8_t v___x_3523_; 
v_array_3520_ = lean_ctor_get(v_snd_3503_, 0);
v_start_3521_ = lean_ctor_get(v_snd_3503_, 1);
v_stop_3522_ = lean_ctor_get(v_snd_3503_, 2);
v___x_3523_ = lean_nat_dec_lt(v_start_3521_, v_stop_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3525_; 
lean_dec_ref(v_xs_3488_);
if (v_isShared_3519_ == 0)
{
v___x_3525_ = v___x_3518_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_snd_3503_);
v___x_3525_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v___x_3525_);
v___x_3527_ = v___x_3514_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_fst_3512_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3527_);
v___x_3529_ = v___x_3510_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3529_);
v___x_3531_ = v___x_3506_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
}
}
}
else
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3638_; 
lean_inc(v_stop_3522_);
lean_inc(v_start_3521_);
lean_inc_ref(v_array_3520_);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_snd_3503_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; lean_object* v_unused_3640_; lean_object* v_unused_3641_; 
v_unused_3639_ = lean_ctor_get(v_snd_3503_, 2);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_snd_3503_, 1);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v_snd_3503_, 0);
lean_dec(v_unused_3641_);
v___x_3538_ = v_snd_3503_;
v_isShared_3539_ = v_isSharedCheck_3638_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v_snd_3503_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3638_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_array_3540_; lean_object* v_start_3541_; lean_object* v_stop_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v_array_3540_ = lean_ctor_get(v_fst_3516_, 0);
v_start_3541_ = lean_ctor_get(v_fst_3516_, 1);
v_stop_3542_ = lean_ctor_get(v_fst_3516_, 2);
v___x_3543_ = lean_array_fget(v_array_3520_, v_start_3521_);
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3545_ = lean_nat_add(v_start_3521_, v___x_3544_);
lean_dec(v_start_3521_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v___x_3545_);
v___x_3547_ = v___x_3538_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_array_3520_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_stop_3522_);
v___x_3547_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_lt(v_start_3541_, v_stop_3542_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3550_; 
lean_dec(v___x_3543_);
lean_dec_ref(v_xs_3488_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3547_);
v___x_3550_ = v___x_3518_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3547_);
v___x_3550_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v___x_3550_);
v___x_3552_ = v___x_3514_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_fst_3512_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3552_);
v___x_3554_ = v___x_3510_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3556_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3554_);
v___x_3556_ = v___x_3506_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
}
}
}
else
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3633_; 
lean_inc(v_stop_3542_);
lean_inc(v_start_3541_);
lean_inc_ref(v_array_3540_);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_fst_3516_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; lean_object* v_unused_3635_; lean_object* v_unused_3636_; 
v_unused_3634_ = lean_ctor_get(v_fst_3516_, 2);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_fst_3516_, 1);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_fst_3516_, 0);
lean_dec(v_unused_3636_);
v___x_3563_ = v_fst_3516_;
v_isShared_3564_ = v_isSharedCheck_3633_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v_fst_3516_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3633_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v_array_3565_; lean_object* v_start_3566_; lean_object* v_stop_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v_array_3565_ = lean_ctor_get(v_fst_3512_, 0);
v_start_3566_ = lean_ctor_get(v_fst_3512_, 1);
v_stop_3567_ = lean_ctor_get(v_fst_3512_, 2);
v___x_3568_ = lean_array_fget(v_array_3540_, v_start_3541_);
v___x_3569_ = lean_nat_add(v_start_3541_, v___x_3544_);
lean_dec(v_start_3541_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3569_);
v___x_3571_ = v___x_3563_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_array_3540_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_stop_3542_);
v___x_3571_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_nat_dec_lt(v_start_3566_, v_stop_3567_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3574_; 
lean_dec(v___x_3568_);
lean_dec(v___x_3543_);
lean_dec_ref(v_xs_3488_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3547_);
lean_ctor_set(v___x_3518_, 0, v___x_3571_);
v___x_3574_ = v___x_3518_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3547_);
v___x_3574_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3576_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v___x_3574_);
v___x_3576_ = v___x_3514_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_fst_3512_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3576_);
v___x_3578_ = v___x_3510_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_fst_3508_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3580_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3578_);
v___x_3580_ = v___x_3506_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3628_; 
lean_inc(v_stop_3567_);
lean_inc(v_start_3566_);
lean_inc_ref(v_array_3565_);
lean_del_object(v___x_3506_);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_fst_3512_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; 
v_unused_3629_ = lean_ctor_get(v_fst_3512_, 2);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_fst_3512_, 1);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_fst_3512_, 0);
lean_dec(v_unused_3631_);
v___x_3587_ = v_fst_3512_;
v_isShared_3588_ = v_isSharedCheck_3628_;
goto v_resetjp_3586_;
}
else
{
lean_dec(v_fst_3512_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3628_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v_a_3589_ = lean_array_uget_borrowed(v_as_3489_, v_i_3491_);
v___x_3590_ = lean_array_fget(v_array_3565_, v_start_3566_);
v___x_3591_ = lean_nat_add(v_start_3566_, v___x_3544_);
lean_dec(v_start_3566_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v___x_3591_);
v___x_3593_ = v___x_3587_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_array_3565_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_stop_3567_);
v___x_3593_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; 
lean_inc_ref(v_xs_3488_);
lean_inc(v_a_3589_);
v___x_3594_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3589_, v___x_3543_, v_xs_3488_, v___x_3590_, v___x_3568_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v_fst_3596_; lean_object* v_snd_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3618_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v_fst_3596_ = lean_ctor_get(v_a_3595_, 0);
v_snd_3597_ = lean_ctor_get(v_a_3595_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_a_3595_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3599_ = v_a_3595_;
v_isShared_3600_ = v_isSharedCheck_3618_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_snd_3597_);
lean_inc(v_fst_3596_);
lean_dec(v_a_3595_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3618_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v_fst_3504_);
lean_ctor_set(v___x_3601_, 1, v_snd_3597_);
v___x_3602_ = lean_array_push(v_fst_3508_, v_fst_3596_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 1, v___x_3547_);
lean_ctor_set(v___x_3599_, 0, v___x_3571_);
v___x_3604_ = v___x_3599_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v___x_3547_);
v___x_3604_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3604_);
lean_ctor_set(v___x_3518_, 0, v___x_3593_);
v___x_3606_ = v___x_3518_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v___x_3606_);
lean_ctor_set(v___x_3514_, 0, v___x_3602_);
v___x_3608_ = v___x_3514_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3608_);
lean_ctor_set(v___x_3510_, 0, v___x_3601_);
v___x_3610_ = v___x_3510_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
size_t v___x_3611_; size_t v___x_3612_; 
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_add(v_i_3491_, v___x_3611_);
v_i_3491_ = v___x_3612_;
v_b_3492_ = v___x_3610_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3571_);
lean_dec_ref(v___x_3547_);
lean_del_object(v___x_3518_);
lean_del_object(v___x_3514_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
lean_dec(v_fst_3504_);
lean_dec_ref(v_xs_3488_);
v_a_3619_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3594_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3594_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3488_ = stack[0].m_obj;
lean_object* v_as_3489_ = stack[1].m_obj;
size_t v_sz_3490_ = stack[2].m_num;
size_t v_i_3491_ = stack[3].m_num;
lean_object* v_b_3492_ = stack[4].m_obj;
lean_object* v___y_3493_ = stack[5].m_obj;
lean_object* v___y_3494_ = stack[6].m_obj;
lean_object* v___y_3495_ = stack[7].m_obj;
lean_object* v___y_3496_ = stack[8].m_obj;
lean_object* v_res_3650_;
v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3488_, v_as_3489_, v_sz_3490_, v_i_3491_, v_b_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
stack->m_obj
 = v_res_3650_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3651_, lean_object* v_as_3652_, lean_object* v_sz_3653_, lean_object* v_i_3654_, lean_object* v_b_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
size_t v_sz_boxed_3661_; size_t v_i_boxed_3662_; lean_object* v_res_3663_; 
v_sz_boxed_3661_ = lean_unbox_usize(v_sz_3653_);
lean_dec(v_sz_3653_);
v_i_boxed_3662_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3651_, v_as_3652_, v_sz_boxed_3661_, v_i_boxed_3662_, v_b_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec_ref(v_as_3652_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
if (lean_obj_tag(v_a_3664_) == 0)
{
lean_object* v___x_3666_; 
v___x_3666_ = l_List_reverse___redArg(v_a_3665_);
return v___x_3666_;
}
else
{
lean_object* v_head_3667_; lean_object* v_tail_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3677_; 
v_head_3667_ = lean_ctor_get(v_a_3664_, 0);
v_tail_3668_ = lean_ctor_get(v_a_3664_, 1);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3670_ = v_a_3664_;
v_isShared_3671_ = v_isSharedCheck_3677_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_tail_3668_);
lean_inc(v_head_3667_);
lean_dec(v_a_3664_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3677_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3667_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 1, v_a_3665_);
lean_ctor_set(v___x_3670_, 0, v___x_3672_);
v___x_3674_ = v___x_3670_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_a_3665_);
v___x_3674_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
v_a_3664_ = v_tail_3668_;
v_a_3665_ = v___x_3674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3678_, lean_object* v_j_3679_){
_start:
{
lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = lean_array_get_size(v_as_3678_);
v___x_3681_ = lean_nat_dec_lt(v_j_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v_j_3679_);
v___x_3682_ = lean_box(0);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3683_ = lean_array_fget_borrowed(v_as_3678_, v_j_3679_);
v___x_3684_ = lean_array_get_size(v___x_3683_);
v___x_3685_ = lean_unsigned_to_nat(0u);
v___x_3686_ = lean_nat_dec_eq(v___x_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_nat_add(v_j_3679_, v___x_3687_);
lean_dec(v_j_3679_);
v_j_3679_ = v___x_3688_;
goto _start;
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_j_3679_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3691_, lean_object* v_j_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3691_, v_j_3692_);
lean_dec_ref(v_as_3691_);
return v_res_3693_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3694_, lean_object* v_as_3695_, size_t v_sz_3696_, size_t v_i_3697_, lean_object* v_b_3698_){
_start:
{
uint8_t v___x_3700_; 
v___x_3700_ = lean_usize_dec_lt(v_i_3697_, v_sz_3696_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; 
lean_dec_ref(v_a_3694_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_b_3698_);
return v___x_3701_;
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; size_t v___x_3705_; size_t v___x_3706_; 
v_a_3702_ = lean_array_uget_borrowed(v_as_3695_, v_i_3697_);
lean_inc(v_a_3702_);
lean_inc_ref(v_a_3694_);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v_a_3694_);
lean_ctor_set(v___x_3703_, 1, v_a_3702_);
v___x_3704_ = lean_array_push(v_b_3698_, v___x_3703_);
v___x_3705_ = ((size_t)1ULL);
v___x_3706_ = lean_usize_add(v_i_3697_, v___x_3705_);
v_i_3697_ = v___x_3706_;
v_b_3698_ = v___x_3704_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3694_ = stack[0].m_obj;
lean_object* v_as_3695_ = stack[1].m_obj;
size_t v_sz_3696_ = stack[2].m_num;
size_t v_i_3697_ = stack[3].m_num;
lean_object* v_b_3698_ = stack[4].m_obj;
lean_object* v_res_3708_;
v_res_3708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3694_, v_as_3695_, v_sz_3696_, v_i_3697_, v_b_3698_);
stack->m_obj
 = v_res_3708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3709_, lean_object* v_as_3710_, lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_b_3713_, lean_object* v___y_3714_){
_start:
{
size_t v_sz_boxed_3715_; size_t v_i_boxed_3716_; lean_object* v_res_3717_; 
v_sz_boxed_3715_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3716_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3709_, v_as_3710_, v_sz_boxed_3715_, v_i_boxed_3716_, v_b_3713_);
lean_dec_ref(v_as_3710_);
return v_res_3717_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3718_, lean_object* v_xs_3719_, lean_object* v_as_3720_, size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_b_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; 
lean_dec_ref(v_xs_3719_);
lean_dec_ref(v_a_3718_);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_b_3723_);
return v___x_3730_;
}
else
{
lean_object* v_snd_3731_; lean_object* v_fst_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3775_; 
v_snd_3731_ = lean_ctor_get(v_b_3723_, 1);
v_fst_3732_ = lean_ctor_get(v_b_3723_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_b_3723_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3734_ = v_b_3723_;
v_isShared_3735_ = v_isSharedCheck_3775_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_snd_3731_);
lean_inc(v_fst_3732_);
lean_dec(v_b_3723_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3775_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_array_3736_; lean_object* v_start_3737_; lean_object* v_stop_3738_; uint8_t v___x_3739_; 
v_array_3736_ = lean_ctor_get(v_snd_3731_, 0);
v_start_3737_ = lean_ctor_get(v_snd_3731_, 1);
v_stop_3738_ = lean_ctor_get(v_snd_3731_, 2);
v___x_3739_ = lean_nat_dec_lt(v_start_3737_, v_stop_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v_xs_3719_);
lean_dec_ref(v_a_3718_);
if (v_isShared_3735_ == 0)
{
v___x_3741_ = v___x_3734_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_fst_3732_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_snd_3731_);
v___x_3741_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
return v___x_3742_;
}
}
else
{
lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3771_; 
lean_inc(v_stop_3738_);
lean_inc(v_start_3737_);
lean_inc_ref(v_array_3736_);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_snd_3731_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3772_ = lean_ctor_get(v_snd_3731_, 2);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_snd_3731_, 1);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_snd_3731_, 0);
lean_dec(v_unused_3774_);
v___x_3745_ = v_snd_3731_;
v_isShared_3746_ = v_isSharedCheck_3771_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v_snd_3731_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3771_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v_a_3747_ = lean_array_uget_borrowed(v_as_3720_, v_i_3722_);
v___x_3748_ = lean_array_fget(v_array_3736_, v_start_3737_);
v___x_3749_ = lean_unsigned_to_nat(1u);
v___x_3750_ = lean_nat_add(v_start_3737_, v___x_3749_);
lean_dec(v_start_3737_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 1, v___x_3750_);
v___x_3752_ = v___x_3745_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_array_3736_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_stop_3738_);
v___x_3752_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; 
lean_inc(v_a_3747_);
lean_inc_ref(v_xs_3719_);
lean_inc_ref(v_a_3718_);
v___x_3753_ = l_Lean_Elab_Structural_argsInGroup(v_a_3718_, v_xs_3719_, v_a_3747_, v___x_3748_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___x_3748_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v___x_3755_ = lean_array_push(v_fst_3732_, v_a_3754_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v___x_3752_);
lean_ctor_set(v___x_3734_, 0, v___x_3755_);
v___x_3757_ = v___x_3734_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3752_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
size_t v___x_3758_; size_t v___x_3759_; 
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_add(v_i_3722_, v___x_3758_);
v_i_3722_ = v___x_3759_;
v_b_3723_ = v___x_3757_;
goto _start;
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v___x_3752_);
lean_del_object(v___x_3734_);
lean_dec(v_fst_3732_);
lean_dec_ref(v_xs_3719_);
lean_dec_ref(v_a_3718_);
v_a_3762_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3753_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3753_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3718_ = stack[0].m_obj;
lean_object* v_xs_3719_ = stack[1].m_obj;
lean_object* v_as_3720_ = stack[2].m_obj;
size_t v_sz_3721_ = stack[3].m_num;
size_t v_i_3722_ = stack[4].m_num;
lean_object* v_b_3723_ = stack[5].m_obj;
lean_object* v___y_3724_ = stack[6].m_obj;
lean_object* v___y_3725_ = stack[7].m_obj;
lean_object* v___y_3726_ = stack[8].m_obj;
lean_object* v___y_3727_ = stack[9].m_obj;
lean_object* v_res_3776_;
v_res_3776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3718_, v_xs_3719_, v_as_3720_, v_sz_3721_, v_i_3722_, v_b_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
stack->m_obj
 = v_res_3776_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3777_, lean_object* v_xs_3778_, lean_object* v_as_3779_, lean_object* v_sz_3780_, lean_object* v_i_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
size_t v_sz_boxed_3788_; size_t v_i_boxed_3789_; lean_object* v_res_3790_; 
v_sz_boxed_3788_ = lean_unbox_usize(v_sz_3780_);
lean_dec(v_sz_3780_);
v_i_boxed_3789_ = lean_unbox_usize(v_i_3781_);
lean_dec(v_i_3781_);
v_res_3790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3777_, v_xs_3778_, v_as_3779_, v_sz_boxed_3788_, v_i_boxed_3789_, v_b_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_as_3779_);
return v_res_3790_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
return v___x_3795_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
return v___x_3801_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3804_ = l_Lean_stringToMessageData(v___x_3803_);
return v___x_3804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3807_ = l_Lean_stringToMessageData(v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
return v___x_3810_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3811_, lean_object* v_values_3812_, lean_object* v_xs_3813_, lean_object* v_fnNames_3814_, lean_object* v_as_3815_, size_t v_sz_3816_, size_t v_i_3817_, lean_object* v_b_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_a_3825_; uint8_t v___x_3829_; 
v___x_3829_ = lean_usize_dec_lt(v_i_3817_, v_sz_3816_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
lean_dec_ref(v_xs_3813_);
lean_dec_ref(v___x_3811_);
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_b_3818_);
return v___x_3830_;
}
else
{
lean_object* v_fst_3831_; lean_object* v_snd_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3906_; 
v_fst_3831_ = lean_ctor_get(v_b_3818_, 0);
v_snd_3832_ = lean_ctor_get(v_b_3818_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_b_3818_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3834_ = v_b_3818_;
v_isShared_3835_ = v_isSharedCheck_3906_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_snd_3832_);
lean_inc(v_fst_3831_);
lean_dec(v_b_3818_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3906_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v_recArgInfoss_3837_; lean_object* v___x_3838_; lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3836_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3838_ = lean_box(0);
v_a_3839_ = lean_array_uget_borrowed(v_as_3815_, v_i_3817_);
v___x_3840_ = lean_array_get_size(v___x_3811_);
lean_inc_ref(v___x_3811_);
v___x_3841_ = l_Array_toSubarray___redArg(v___x_3811_, v___x_3836_, v___x_3840_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3841_);
lean_ctor_set(v___x_3834_, 0, v_recArgInfoss_3837_);
v___x_3843_ = v___x_3834_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_recArgInfoss_3837_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
size_t v_sz_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v_sz_3844_ = lean_array_size(v_values_3812_);
v___x_3845_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3813_);
lean_inc(v_a_3839_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3839_, v_xs_3813_, v_values_3812_, v_sz_3844_, v___x_3845_, v___x_3843_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v_fst_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3895_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
v_fst_3848_ = lean_ctor_get(v_a_3847_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3895_ == 0)
{
lean_object* v_unused_3896_; 
v_unused_3896_ = lean_ctor_get(v_a_3847_, 1);
lean_dec(v_unused_3896_);
v___x_3850_ = v_a_3847_;
v_isShared_3851_ = v_isSharedCheck_3895_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_fst_3848_);
lean_dec(v_a_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3895_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3848_, v___x_3836_);
if (lean_obj_tag(v___x_3852_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec(v_fst_3848_);
v_val_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_val_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3839_);
v___x_3855_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3839_);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_array_get_borrowed(v___x_3838_, v_fnNames_3814_, v_val_3853_);
lean_dec(v_val_3853_);
lean_inc(v___x_3859_);
v___x_3860_ = l_Lean_MessageData_ofName(v___x_3859_);
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3858_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3864_, 0, v_fst_3831_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v_snd_3832_);
lean_ctor_set(v___x_3850_, 0, v___x_3864_);
v___x_3866_ = v___x_3850_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_snd_3832_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
v_a_3825_ = v___x_3866_;
goto v___jp_3824_;
}
}
else
{
lean_object* v___x_3868_; 
lean_dec(v___x_3852_);
v___x_3868_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3848_);
lean_dec(v_fst_3848_);
if (lean_obj_tag(v___x_3868_) == 1)
{
lean_object* v_val_3869_; size_t v_sz_3870_; lean_object* v___x_3871_; 
v_val_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_val_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v_sz_3870_ = lean_array_size(v_val_3869_);
lean_inc(v_a_3839_);
v___x_3871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3839_, v_val_3869_, v_sz_3870_, v___x_3845_, v_snd_3832_);
lean_dec(v_val_3869_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v_a_3872_);
lean_ctor_set(v___x_3850_, 0, v_fst_3831_);
v___x_3874_ = v___x_3850_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_fst_3831_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_a_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
v_a_3825_ = v___x_3874_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_del_object(v___x_3850_);
lean_dec(v_fst_3831_);
lean_dec_ref(v_xs_3813_);
lean_dec_ref(v___x_3811_);
v_a_3876_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3871_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3871_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3893_; 
lean_dec(v___x_3868_);
v___x_3884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3839_);
v___x_3885_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3839_);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_fst_3831_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v_snd_3832_);
lean_ctor_set(v___x_3850_, 0, v___x_3891_);
v___x_3893_ = v___x_3850_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_snd_3832_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
v_a_3825_ = v___x_3893_;
goto v___jp_3824_;
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_snd_3832_);
lean_dec(v_fst_3831_);
lean_dec_ref(v_xs_3813_);
lean_dec_ref(v___x_3811_);
v_a_3897_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3846_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3846_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
}
v___jp_3824_:
{
size_t v___x_3826_; size_t v___x_3827_; 
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = lean_usize_add(v_i_3817_, v___x_3826_);
v_i_3817_ = v___x_3827_;
v_b_3818_ = v_a_3825_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3811_ = stack[0].m_obj;
lean_object* v_values_3812_ = stack[1].m_obj;
lean_object* v_xs_3813_ = stack[2].m_obj;
lean_object* v_fnNames_3814_ = stack[3].m_obj;
lean_object* v_as_3815_ = stack[4].m_obj;
size_t v_sz_3816_ = stack[5].m_num;
size_t v_i_3817_ = stack[6].m_num;
lean_object* v_b_3818_ = stack[7].m_obj;
lean_object* v___y_3819_ = stack[8].m_obj;
lean_object* v___y_3820_ = stack[9].m_obj;
lean_object* v___y_3821_ = stack[10].m_obj;
lean_object* v___y_3822_ = stack[11].m_obj;
lean_object* v_res_3907_;
v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3811_, v_values_3812_, v_xs_3813_, v_fnNames_3814_, v_as_3815_, v_sz_3816_, v_i_3817_, v_b_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
stack->m_obj
 = v_res_3907_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3908_, lean_object* v_values_3909_, lean_object* v_xs_3910_, lean_object* v_fnNames_3911_, lean_object* v_as_3912_, lean_object* v_sz_3913_, lean_object* v_i_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
size_t v_sz_boxed_3921_; size_t v_i_boxed_3922_; lean_object* v_res_3923_; 
v_sz_boxed_3921_ = lean_unbox_usize(v_sz_3913_);
lean_dec(v_sz_3913_);
v_i_boxed_3922_ = lean_unbox_usize(v_i_3914_);
lean_dec(v_i_3914_);
v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3908_, v_values_3909_, v_xs_3910_, v_fnNames_3911_, v_as_3912_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v_as_3912_);
lean_dec_ref(v_fnNames_3911_);
lean_dec_ref(v_values_3909_);
return v_res_3923_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3924_, lean_object* v___x_3925_, lean_object* v_values_3926_, lean_object* v_fnNames_3927_, lean_object* v_as_3928_, size_t v_sz_3929_, size_t v_i_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_a_3938_; uint8_t v___x_3942_; 
v___x_3942_ = lean_usize_dec_lt(v_i_3930_, v_sz_3929_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref(v___x_3925_);
lean_dec_ref(v_xs_3924_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v_b_3931_);
return v___x_3943_;
}
else
{
lean_object* v_fst_3944_; lean_object* v_snd_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_4019_; 
v_fst_3944_ = lean_ctor_get(v_b_3931_, 0);
v_snd_3945_ = lean_ctor_get(v_b_3931_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_b_3931_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3947_ = v_b_3931_;
v_isShared_3948_ = v_isSharedCheck_4019_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_snd_3945_);
lean_inc(v_fst_3944_);
lean_dec(v_b_3931_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_4019_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v_recArgInfoss_3950_; lean_object* v___x_3951_; lean_object* v_a_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3949_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3951_ = lean_box(0);
v_a_3952_ = lean_array_uget_borrowed(v_as_3928_, v_i_3930_);
v___x_3953_ = lean_array_get_size(v___x_3925_);
lean_inc_ref(v___x_3925_);
v___x_3954_ = l_Array_toSubarray___redArg(v___x_3925_, v___x_3949_, v___x_3953_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v___x_3954_);
lean_ctor_set(v___x_3947_, 0, v_recArgInfoss_3950_);
v___x_3956_ = v___x_3947_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_recArgInfoss_3950_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_4018_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
size_t v_sz_3957_; size_t v___x_3958_; lean_object* v___x_3959_; 
v_sz_3957_ = lean_array_size(v_values_3926_);
v___x_3958_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3924_);
lean_inc(v_a_3952_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3952_, v_xs_3924_, v_values_3926_, v_sz_3957_, v___x_3958_, v___x_3956_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v_fst_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_4008_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v_fst_3961_ = lean_ctor_get(v_a_3960_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_a_3960_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v_a_3960_, 1);
lean_dec(v_unused_4009_);
v___x_3963_ = v_a_3960_;
v_isShared_3964_ = v_isSharedCheck_4008_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_fst_3961_);
lean_dec(v_a_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_4008_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3961_, v___x_3949_);
if (lean_obj_tag(v___x_3965_) == 1)
{
lean_object* v_val_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
lean_dec(v_fst_3961_);
v_val_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_val_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3952_);
v___x_3968_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3952_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_array_get_borrowed(v___x_3951_, v_fnNames_3927_, v_val_3966_);
lean_dec(v_val_3966_);
lean_inc(v___x_3972_);
v___x_3973_ = l_Lean_MessageData_ofName(v___x_3972_);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3971_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v_fst_3944_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 1, v_snd_3945_);
lean_ctor_set(v___x_3963_, 0, v___x_3977_);
v___x_3979_ = v___x_3963_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_snd_3945_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
v_a_3938_ = v___x_3979_;
goto v___jp_3937_;
}
}
else
{
lean_object* v___x_3981_; 
lean_dec(v___x_3965_);
v___x_3981_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3961_);
lean_dec(v_fst_3961_);
if (lean_obj_tag(v___x_3981_) == 1)
{
lean_object* v_val_3982_; size_t v_sz_3983_; lean_object* v___x_3984_; 
v_val_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_val_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v_sz_3983_ = lean_array_size(v_val_3982_);
lean_inc(v_a_3952_);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3952_, v_val_3982_, v_sz_3983_, v___x_3958_, v_snd_3945_);
lean_dec(v_val_3982_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 1, v_a_3985_);
lean_ctor_set(v___x_3963_, 0, v_fst_3944_);
v___x_3987_ = v___x_3963_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_fst_3944_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v_a_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
v_a_3938_ = v___x_3987_;
goto v___jp_3937_;
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_del_object(v___x_3963_);
lean_dec(v_fst_3944_);
lean_dec_ref(v___x_3925_);
lean_dec_ref(v_xs_3924_);
v_a_3989_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3984_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3984_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
lean_dec(v___x_3981_);
v___x_3997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3952_);
v___x_3998_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3952_);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4002_, 0, v_fst_3944_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4002_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 1, v_snd_3945_);
lean_ctor_set(v___x_3963_, 0, v___x_4004_);
v___x_4006_ = v___x_3963_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_snd_3945_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
v_a_3938_ = v___x_4006_;
goto v___jp_3937_;
}
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_snd_3945_);
lean_dec(v_fst_3944_);
lean_dec_ref(v___x_3925_);
lean_dec_ref(v_xs_3924_);
v_a_4010_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3959_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3959_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
}
v___jp_3937_:
{
size_t v___x_3939_; size_t v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = ((size_t)1ULL);
v___x_3940_ = lean_usize_add(v_i_3930_, v___x_3939_);
v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3925_, v_values_3926_, v_xs_3924_, v_fnNames_3927_, v_as_3928_, v_sz_3929_, v___x_3940_, v_a_3938_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
return v___x_3941_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3924_ = stack[0].m_obj;
lean_object* v___x_3925_ = stack[1].m_obj;
lean_object* v_values_3926_ = stack[2].m_obj;
lean_object* v_fnNames_3927_ = stack[3].m_obj;
lean_object* v_as_3928_ = stack[4].m_obj;
size_t v_sz_3929_ = stack[5].m_num;
size_t v_i_3930_ = stack[6].m_num;
lean_object* v_b_3931_ = stack[7].m_obj;
lean_object* v___y_3932_ = stack[8].m_obj;
lean_object* v___y_3933_ = stack[9].m_obj;
lean_object* v___y_3934_ = stack[10].m_obj;
lean_object* v___y_3935_ = stack[11].m_obj;
lean_object* v_res_4020_;
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3924_, v___x_3925_, v_values_3926_, v_fnNames_3927_, v_as_3928_, v_sz_3929_, v_i_3930_, v_b_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
stack->m_obj
 = v_res_4020_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_4021_, lean_object* v___x_4022_, lean_object* v_values_4023_, lean_object* v_fnNames_4024_, lean_object* v_as_4025_, lean_object* v_sz_4026_, lean_object* v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
size_t v_sz_boxed_4034_; size_t v_i_boxed_4035_; lean_object* v_res_4036_; 
v_sz_boxed_4034_ = lean_unbox_usize(v_sz_4026_);
lean_dec(v_sz_4026_);
v_i_boxed_4035_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_4021_, v___x_4022_, v_values_4023_, v_fnNames_4024_, v_as_4025_, v_sz_boxed_4034_, v_i_boxed_4035_, v_b_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v_as_4025_);
lean_dec_ref(v_fnNames_4024_);
lean_dec_ref(v_values_4023_);
return v_res_4036_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__2));
v___x_4043_ = l_Lean_MessageData_ofFormat(v___x_4042_);
return v___x_4043_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__4));
v___x_4046_ = l_Lean_stringToMessageData(v___x_4045_);
return v___x_4046_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__7));
v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
return v___x_4051_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(1);
v___x_4053_ = l_Lean_MessageData_ofFormat(v___x_4052_);
return v___x_4053_;
}
}
lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_4054_, lean_object* v_fixedParamPerms_4055_, lean_object* v_xs_4056_, lean_object* v_values_4057_, lean_object* v_termMeasure_x3fs_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v_candidates_4065_; lean_object* v___x_4066_; lean_object* v_perms_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v_report_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; size_t v_sz_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
v___x_4064_ = lean_unsigned_to_nat(0u);
v_candidates_4065_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__0));
v___x_4066_ = lean_array_get_size(v_values_4057_);
v_perms_4067_ = lean_ctor_get(v_fixedParamPerms_4055_, 1);
lean_inc_ref(v_perms_4067_);
lean_dec_ref(v_fixedParamPerms_4055_);
lean_inc_ref(v_values_4057_);
v___x_4068_ = l_Array_toSubarray___redArg(v_values_4057_, v___x_4064_, v___x_4066_);
v___x_4069_ = lean_array_get_size(v_termMeasure_x3fs_4058_);
v_report_4070_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_4071_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_4058_, v___x_4064_, v___x_4069_);
v___x_4072_ = lean_array_get_size(v_perms_4067_);
v___x_4073_ = l_Array_toSubarray___redArg(v_perms_4067_, v___x_4064_, v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4071_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4068_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_candidates_4065_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v_report_4070_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v_sz_4078_ = lean_array_size(v_fnNames_4054_);
v___x_4079_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4056_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_4056_, v_fnNames_4054_, v_sz_4078_, v___x_4079_, v___x_4077_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v_snd_4082_; lean_object* v_toCold_4083_; lean_object* v_options_4084_; lean_object* v_fst_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4223_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v_snd_4082_ = lean_ctor_get(v_a_4081_, 1);
lean_inc(v_snd_4082_);
v_toCold_4083_ = lean_ctor_get(v_a_4061_, 0);
v_options_4084_ = lean_ctor_get(v_toCold_4083_, 2);
v_fst_4085_ = lean_ctor_get(v_a_4081_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_a_4081_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v_a_4081_, 1);
lean_dec(v_unused_4224_);
v___x_4087_ = v_a_4081_;
v_isShared_4088_ = v_isSharedCheck_4223_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_fst_4085_);
lean_dec(v_a_4081_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4223_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v_fst_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4221_; 
v_fst_4089_ = lean_ctor_get(v_snd_4082_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_snd_4082_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v_snd_4082_, 1);
lean_dec(v_unused_4222_);
v___x_4091_ = v_snd_4082_;
v_isShared_4092_ = v_isSharedCheck_4221_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_fst_4089_);
lean_dec(v_snd_4082_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4221_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v_inheritedTraceOptions_4093_; uint8_t v_hasTrace_4094_; size_t v_sz_4095_; lean_object* v___x_4096_; lean_object* v___y_4098_; lean_object* v_report_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___x_4146_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; 
v_inheritedTraceOptions_4093_ = lean_ctor_get(v_toCold_4083_, 11);
v_hasTrace_4094_ = lean_ctor_get_uint8(v_options_4084_, sizeof(void*)*1);
v_sz_4095_ = lean_array_size(v_fst_4089_);
v___x_4096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4095_, v___x_4079_, v_fst_4089_);
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4094_ == 0)
{
v___y_4186_ = v_a_4059_;
v___y_4187_ = v_a_4060_;
v___y_4188_ = v_a_4061_;
v___y_4189_ = v_a_4062_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4195_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4093_, v_options_4084_, v___x_4195_);
if (v___x_4196_ == 0)
{
v___y_4186_ = v_a_4059_;
v___y_4187_ = v_a_4060_;
v___y_4188_ = v_a_4061_;
v___y_4189_ = v_a_4062_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4197_; lean_object* v___y_4199_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4197_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4217_ = lean_array_get_size(v___x_4096_);
v___x_4218_ = lean_nat_dec_lt(v___x_4064_, v___x_4217_);
if (v___x_4218_ == 0)
{
v___y_4199_ = v___x_4216_;
goto v___jp_4198_;
}
else
{
size_t v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = lean_usize_of_nat(v___x_4217_);
v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4096_, v___x_4079_, v___x_4219_, v___x_4216_);
v___y_4199_ = v___x_4220_;
goto v___jp_4198_;
}
v___jp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4200_ = lean_array_to_list(v___y_4199_);
v___x_4201_ = lean_box(0);
v___x_4202_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4200_, v___x_4201_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__9, &l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9);
v___x_4204_ = l_Lean_MessageData_joinSep(v___x_4202_, v___x_4203_);
v___x_4205_ = l_Lean_indentD(v___x_4204_);
v___x_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4197_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4146_, v___x_4206_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_dec_ref_known(v___x_4207_, 1);
v___y_4186_ = v_a_4059_;
v___y_4187_ = v_a_4060_;
v___y_4188_ = v_a_4061_;
v___y_4189_ = v_a_4062_;
goto v___jp_4185_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v___x_4096_);
lean_del_object(v___x_4091_);
lean_del_object(v___x_4087_);
lean_dec(v_fst_4085_);
lean_dec_ref(v_values_4057_);
lean_dec_ref(v_xs_4056_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
v___jp_4097_:
{
lean_object* v___x_4105_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 1, v_candidates_4065_);
lean_ctor_set(v___x_4091_, 0, v_report_4099_);
v___x_4105_ = v___x_4091_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_report_4099_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_candidates_4065_);
v___x_4105_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
size_t v_sz_4106_; lean_object* v___x_4107_; 
v_sz_4106_ = lean_array_size(v___y_4098_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_4056_, v___x_4096_, v_values_4057_, v_fnNames_4054_, v___y_4098_, v_sz_4106_, v___x_4079_, v___x_4105_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec_ref(v___y_4098_);
lean_dec_ref(v_values_4057_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4124_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4124_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4124_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_fst_4112_; lean_object* v_snd_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4123_; 
v_fst_4112_ = lean_ctor_get(v_a_4108_, 0);
v_snd_4113_ = lean_ctor_get(v_a_4108_, 1);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_a_4108_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4115_ = v_a_4108_;
v_isShared_4116_ = v_isSharedCheck_4123_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_snd_4113_);
lean_inc(v_fst_4112_);
lean_dec(v_a_4108_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4123_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 1, v_fst_4112_);
lean_ctor_set(v___x_4115_, 0, v_snd_4113_);
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_snd_4113_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_fst_4112_);
v___x_4118_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4120_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4118_);
v___x_4120_ = v___x_4110_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
v_a_4125_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4107_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4107_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
v___jp_4134_:
{
lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4140_ = lean_array_get_size(v___y_4135_);
v___x_4141_ = lean_nat_dec_eq(v___x_4140_, v___x_4064_);
if (v___x_4141_ == 0)
{
lean_del_object(v___x_4087_);
v___y_4098_ = v___y_4135_;
v_report_4099_ = v_fst_4085_;
v___y_4100_ = v___y_4136_;
v___y_4101_ = v___y_4137_;
v___y_4102_ = v___y_4138_;
v___y_4103_ = v___y_4139_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4142_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__3, &l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 7);
lean_ctor_set(v___x_4087_, 1, v___x_4142_);
v___x_4144_ = v___x_4087_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_fst_4085_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
v___y_4098_ = v___y_4135_;
v_report_4099_ = v___x_4144_;
v___y_4100_ = v___y_4136_;
v___y_4101_ = v___y_4137_;
v___y_4102_ = v___y_4138_;
v___y_4103_ = v___y_4139_;
goto v___jp_4097_;
}
}
}
v___jp_4147_:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4152_, v___y_4150_, v___y_4148_, v___y_4151_, v___y_4149_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_toCold_4154_; lean_object* v_options_4155_; uint8_t v_hasTrace_4156_; 
v_toCold_4154_ = lean_ctor_get(v___y_4151_, 0);
v_options_4155_ = lean_ctor_get(v_toCold_4154_, 2);
v_hasTrace_4156_ = lean_ctor_get_uint8(v_options_4155_, sizeof(void*)*1);
if (v_hasTrace_4156_ == 0)
{
lean_object* v_a_4157_; 
v_a_4157_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4135_ = v_a_4157_;
v___y_4136_ = v___y_4150_;
v___y_4137_ = v___y_4148_;
v___y_4138_ = v___y_4151_;
v___y_4139_ = v___y_4149_;
goto v___jp_4134_;
}
else
{
lean_object* v_a_4158_; lean_object* v_inheritedTraceOptions_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_a_4158_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4153_, 1);
v_inheritedTraceOptions_4159_ = lean_ctor_get(v_toCold_4154_, 11);
v___x_4160_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4159_, v_options_4155_, v___x_4160_);
if (v___x_4161_ == 0)
{
v___y_4135_ = v_a_4158_;
v___y_4136_ = v___y_4150_;
v___y_4137_ = v___y_4148_;
v___y_4138_ = v___y_4151_;
v___y_4139_ = v___y_4149_;
goto v___jp_4134_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4162_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__5, &l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5);
lean_inc(v_a_4158_);
v___x_4163_ = lean_array_to_list(v_a_4158_);
v___x_4164_ = lean_box(0);
v___x_4165_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4163_, v___x_4164_);
v___x_4166_ = l_Lean_MessageData_ofList(v___x_4165_);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4162_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4146_, v___x_4167_, v___y_4150_, v___y_4148_, v___y_4151_, v___y_4149_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_dec_ref_known(v___x_4168_, 1);
v___y_4135_ = v_a_4158_;
v___y_4136_ = v___y_4150_;
v___y_4137_ = v___y_4148_;
v___y_4138_ = v___y_4151_;
v___y_4139_ = v___y_4149_;
goto v___jp_4134_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v_a_4158_);
lean_dec_ref(v___x_4096_);
lean_del_object(v___x_4091_);
lean_del_object(v___x_4087_);
lean_dec(v_fst_4085_);
lean_dec_ref(v_values_4057_);
lean_dec_ref(v_xs_4056_);
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4168_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec_ref(v___x_4096_);
lean_del_object(v___x_4091_);
lean_del_object(v___x_4087_);
lean_dec(v_fst_4085_);
lean_dec_ref(v_values_4057_);
lean_dec_ref(v_xs_4056_);
v_a_4177_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4153_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4153_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
v___jp_4185_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4191_ = lean_array_get_size(v___x_4096_);
v___x_4192_ = lean_nat_dec_lt(v___x_4064_, v___x_4191_);
if (v___x_4192_ == 0)
{
v___y_4148_ = v___y_4187_;
v___y_4149_ = v___y_4189_;
v___y_4150_ = v___y_4186_;
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___x_4190_;
goto v___jp_4147_;
}
else
{
size_t v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_usize_of_nat(v___x_4191_);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4096_, v___x_4079_, v___x_4193_, v___x_4190_);
v___y_4148_ = v___y_4187_;
v___y_4149_ = v___y_4189_;
v___y_4150_ = v___y_4186_;
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___x_4194_;
goto v___jp_4147_;
}
}
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec_ref(v_values_4057_);
lean_dec_ref(v_xs_4056_);
v_a_4225_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4080_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4080_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_findRecArgCandidates_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_4054_ = stack[0].m_obj;
lean_object* v_fixedParamPerms_4055_ = stack[1].m_obj;
lean_object* v_xs_4056_ = stack[2].m_obj;
lean_object* v_values_4057_ = stack[3].m_obj;
lean_object* v_termMeasure_x3fs_4058_ = stack[4].m_obj;
lean_object* v_a_4059_ = stack[5].m_obj;
lean_object* v_a_4060_ = stack[6].m_obj;
lean_object* v_a_4061_ = stack[7].m_obj;
lean_object* v_a_4062_ = stack[8].m_obj;
lean_object* v_res_4233_;
v_res_4233_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4054_, v_fixedParamPerms_4055_, v_xs_4056_, v_values_4057_, v_termMeasure_x3fs_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
stack->m_obj
 = v_res_4233_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4234_, lean_object* v_fixedParamPerms_4235_, lean_object* v_xs_4236_, lean_object* v_values_4237_, lean_object* v_termMeasure_x3fs_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4234_, v_fixedParamPerms_4235_, v_xs_4236_, v_values_4237_, v_termMeasure_x3fs_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec_ref(v_fnNames_4234_);
return v_res_4244_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4245_, lean_object* v_as_4246_, size_t v_sz_4247_, size_t v_i_4248_, lean_object* v_b_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4245_, v_as_4246_, v_sz_4247_, v_i_4248_, v_b_4249_);
return v___x_4255_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4245_ = stack[0].m_obj;
lean_object* v_as_4246_ = stack[1].m_obj;
size_t v_sz_4247_ = stack[2].m_num;
size_t v_i_4248_ = stack[3].m_num;
lean_object* v_b_4249_ = stack[4].m_obj;
lean_object* v___y_4250_ = stack[5].m_obj;
lean_object* v___y_4251_ = stack[6].m_obj;
lean_object* v___y_4252_ = stack[7].m_obj;
lean_object* v___y_4253_ = stack[8].m_obj;
lean_object* v_res_4256_;
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4245_, v_as_4246_, v_sz_4247_, v_i_4248_, v_b_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
stack->m_obj
 = v_res_4256_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4257_, lean_object* v_as_4258_, lean_object* v_sz_4259_, lean_object* v_i_4260_, lean_object* v_b_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
size_t v_sz_boxed_4267_; size_t v_i_boxed_4268_; lean_object* v_res_4269_; 
v_sz_boxed_4267_ = lean_unbox_usize(v_sz_4259_);
lean_dec(v_sz_4259_);
v_i_boxed_4268_ = lean_unbox_usize(v_i_4260_);
lean_dec(v_i_4260_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4257_, v_as_4258_, v_sz_boxed_4267_, v_i_boxed_4268_, v_b_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v_as_4258_);
return v_res_4269_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4270_, uint8_t v_skipRealize_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v_env_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4274_ = lean_st_ref_get(v___y_4272_);
v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc_ref(v_env_4275_);
lean_dec(v___x_4274_);
v___x_4276_ = l_Lean_Environment_contains(v_env_4275_, v_constName_4270_, v_skipRealize_4271_);
v___x_4277_ = lean_box(v___x_4276_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_4270_ = stack[0].m_obj;
uint8_t v_skipRealize_4271_ = stack[1].m_num;
lean_object* v___y_4272_ = stack[2].m_obj;
lean_object* v_res_4279_;
v_res_4279_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4270_, v_skipRealize_4271_, v___y_4272_);
stack->m_obj
 = v_res_4279_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4280_, lean_object* v_skipRealize_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
uint8_t v_skipRealize_boxed_4284_; lean_object* v_res_4285_; 
v_skipRealize_boxed_4284_ = lean_unbox(v_skipRealize_4281_);
v_res_4285_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4280_, v_skipRealize_boxed_4284_, v___y_4282_);
lean_dec(v___y_4282_);
return v_res_4285_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4286_, uint8_t v_skipRealize_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4286_, v_skipRealize_4287_, v___y_4291_);
return v___x_4293_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_4286_ = stack[0].m_obj;
uint8_t v_skipRealize_4287_ = stack[1].m_num;
lean_object* v___y_4288_ = stack[2].m_obj;
lean_object* v___y_4289_ = stack[3].m_obj;
lean_object* v___y_4290_ = stack[4].m_obj;
lean_object* v___y_4291_ = stack[5].m_obj;
lean_object* v_res_4294_;
v_res_4294_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4286_, v_skipRealize_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
stack->m_obj
 = v_res_4294_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4295_, lean_object* v_skipRealize_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v_skipRealize_boxed_4302_; lean_object* v_res_4303_; 
v_skipRealize_boxed_4302_ = lean_unbox(v_skipRealize_4296_);
v_res_4303_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4295_, v_skipRealize_boxed_4302_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4303_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Meta_saveState___redArg(v___y_4306_, v___y_4308_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
lean_inc(v___y_4308_);
lean_inc_ref(v___y_4307_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
v___x_4312_ = lean_apply_5(v_x_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, lean_box(0));
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_dec(v_a_4311_);
return v___x_4312_;
}
else
{
lean_object* v_a_4313_; uint8_t v___y_4315_; uint8_t v___x_4333_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
v___x_4333_ = l_Lean_Exception_isInterrupt(v_a_4313_);
if (v___x_4333_ == 0)
{
uint8_t v___x_4334_; 
lean_inc(v_a_4313_);
v___x_4334_ = l_Lean_Exception_isRuntime(v_a_4313_);
v___y_4315_ = v___x_4334_;
goto v___jp_4314_;
}
else
{
v___y_4315_ = v___x_4333_;
goto v___jp_4314_;
}
v___jp_4314_:
{
if (v___y_4315_ == 0)
{
lean_object* v___x_4316_; 
lean_dec_ref_known(v___x_4312_, 1);
v___x_4316_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4311_, v___y_4306_, v___y_4308_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v___x_4316_, 0);
lean_dec(v_unused_4324_);
v___x_4318_ = v___x_4316_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_dec(v___x_4316_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 1);
lean_ctor_set(v___x_4318_, 0, v_a_4313_);
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4313_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_a_4313_);
v_a_4325_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4316_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4316_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_dec(v_a_4313_);
lean_dec(v_a_4311_);
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v_x_4304_);
v_a_4335_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4310_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4310_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4304_ = stack[0].m_obj;
lean_object* v___y_4305_ = stack[1].m_obj;
lean_object* v___y_4306_ = stack[2].m_obj;
lean_object* v___y_4307_ = stack[3].m_obj;
lean_object* v___y_4308_ = stack[4].m_obj;
lean_object* v_res_4343_;
v_res_4343_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
stack->m_obj
 = v_res_4343_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4350_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
return v___x_4358_;
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4352_ = stack[1].m_obj;
lean_object* v___y_4353_ = stack[2].m_obj;
lean_object* v___y_4354_ = stack[3].m_obj;
lean_object* v___y_4355_ = stack[4].m_obj;
lean_object* v___y_4356_ = stack[5].m_obj;
lean_object* v_res_4359_;
v_res_4359_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_box(0), v_x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
stack->m_obj
 = v_res_4359_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4360_, lean_object* v_x_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4360_, v_x_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4367_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
return v___x_4370_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
return v___x_4373_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4374_, uint8_t v___x_4375_, lean_object* v_group_4376_, lean_object* v_k_4377_, lean_object* v_comb_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4374_, v___x_4375_, v___y_4382_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; uint8_t v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_unbox(v_a_4385_);
lean_dec(v_a_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4388_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4376_);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4391_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v___x_4393_; 
lean_dec_ref_known(v___x_4392_, 1);
v___x_4393_ = lean_apply_6(v_k_4377_, v_comb_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, lean_box(0));
return v___x_4393_;
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v_comb_4378_);
lean_dec_ref(v_k_4377_);
v_a_4394_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4392_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4392_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
else
{
lean_object* v___x_4402_; 
lean_dec_ref(v_group_4376_);
v___x_4402_ = lean_apply_6(v_k_4377_, v_comb_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, lean_box(0));
return v___x_4402_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v_comb_4378_);
lean_dec_ref(v_k_4377_);
lean_dec_ref(v_group_4376_);
v_a_4403_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4384_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4384_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4374_ = stack[0].m_obj;
uint8_t v___x_4375_ = stack[1].m_num;
lean_object* v_group_4376_ = stack[2].m_obj;
lean_object* v_k_4377_ = stack[3].m_obj;
lean_object* v_comb_4378_ = stack[4].m_obj;
lean_object* v___y_4379_ = stack[5].m_obj;
lean_object* v___y_4380_ = stack[6].m_obj;
lean_object* v___y_4381_ = stack[7].m_obj;
lean_object* v___y_4382_ = stack[8].m_obj;
lean_object* v_res_4411_;
v_res_4411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4374_, v___x_4375_, v_group_4376_, v_k_4377_, v_comb_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
stack->m_obj
 = v_res_4411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4412_, lean_object* v___x_4413_, lean_object* v_group_4414_, lean_object* v_k_4415_, lean_object* v_comb_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v___x_4401__boxed_4422_; lean_object* v_res_4423_; 
v___x_4401__boxed_4422_ = lean_unbox(v___x_4413_);
v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4412_, v___x_4401__boxed_4422_, v_group_4414_, v_k_4415_, v_comb_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v_res_4423_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4426_ = l_Lean_stringToMessageData(v___x_4425_);
return v___x_4426_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4428_ = l_Lean_stringToMessageData(v___x_4427_);
return v___x_4428_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4429_, lean_object* v_fnNames_4430_, lean_object* v_xs_4431_, lean_object* v_values_4432_, lean_object* v_as_4433_, size_t v_sz_4434_, size_t v_i_4435_, lean_object* v_b_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
uint8_t v___x_4442_; 
v___x_4442_ = lean_usize_dec_lt(v_i_4435_, v_sz_4434_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; 
lean_dec_ref(v_values_4432_);
lean_dec_ref(v_xs_4431_);
lean_dec_ref(v_k_4429_);
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v_b_4436_);
return v___x_4443_;
}
else
{
lean_object* v_snd_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4514_; 
v_snd_4444_ = lean_ctor_get(v_b_4436_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_b_4436_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v_b_4436_, 0);
lean_dec(v_unused_4515_);
v___x_4446_ = v_b_4436_;
v_isShared_4447_ = v_isSharedCheck_4514_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_snd_4444_);
lean_dec(v_b_4436_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4514_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v_a_4448_; lean_object* v_group_4449_; lean_object* v_comb_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4513_; 
v_a_4448_ = lean_array_uget(v_as_4433_, v_i_4435_);
v_group_4449_ = lean_ctor_get(v_a_4448_, 0);
v_comb_4450_ = lean_ctor_get(v_a_4448_, 1);
v_isSharedCheck_4513_ = !lean_is_exclusive(v_a_4448_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4452_ = v_a_4448_;
v_isShared_4453_ = v_isSharedCheck_4513_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_comb_4450_);
lean_inc(v_group_4449_);
lean_dec(v_a_4448_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4513_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v_toIndGroupInfo_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___f_4459_; lean_object* v___x_4460_; 
v_toIndGroupInfo_4454_ = lean_ctor_get(v_group_4449_, 0);
v___x_4455_ = lean_box(0);
v___x_4456_ = lean_unsigned_to_nat(0u);
v___x_4457_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4454_, v___x_4456_);
v___x_4458_ = lean_box(v___x_4442_);
lean_inc_ref(v_comb_4450_);
lean_inc_ref(v_k_4429_);
v___f_4459_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4459_, 0, v___x_4457_);
lean_closure_set(v___f_4459_, 1, v___x_4458_);
lean_closure_set(v___f_4459_, 2, v_group_4449_);
lean_closure_set(v___f_4459_, 3, v_k_4429_);
lean_closure_set(v___f_4459_, 4, v_comb_4450_);
v___x_4460_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4459_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4472_; 
lean_del_object(v___x_4452_);
lean_dec_ref(v_comb_4450_);
lean_dec_ref(v_values_4432_);
lean_dec_ref(v_xs_4431_);
lean_dec_ref(v_k_4429_);
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4472_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4472_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_a_4461_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 0, v___x_4465_);
v___x_4467_ = v___x_4446_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_snd_4444_);
v___x_4467_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4469_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4467_);
v___x_4469_ = v___x_4463_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4512_; 
v_a_4473_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4475_ = v___x_4460_;
v_isShared_4476_ = v_isSharedCheck_4512_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4460_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4512_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
uint8_t v___y_4478_; uint8_t v___x_4510_; 
v___x_4510_ = l_Lean_Exception_isInterrupt(v_a_4473_);
if (v___x_4510_ == 0)
{
uint8_t v___x_4511_; 
lean_inc(v_a_4473_);
v___x_4511_ = l_Lean_Exception_isRuntime(v_a_4473_);
v___y_4478_ = v___x_4511_;
goto v___jp_4477_;
}
else
{
v___y_4478_ = v___x_4510_;
goto v___jp_4477_;
}
v___jp_4477_:
{
if (v___y_4478_ == 0)
{
lean_object* v___x_4479_; 
lean_del_object(v___x_4475_);
lean_inc_ref(v_values_4432_);
lean_inc_ref(v_xs_4431_);
v___x_4479_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4430_, v_xs_4431_, v_values_4432_, v_comb_4450_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___x_4481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4453_ == 0)
{
lean_ctor_set_tag(v___x_4452_, 7);
lean_ctor_set(v___x_4452_, 1, v_a_4480_);
lean_ctor_set(v___x_4452_, 0, v___x_4481_);
v___x_4483_ = v___x_4452_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_a_4480_);
v___x_4483_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4484_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = l_Lean_Exception_toMessageData(v_a_4473_);
v___x_4487_ = l_Lean_indentD(v___x_4486_);
v___x_4488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4485_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v___x_4489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4488_);
lean_ctor_set(v___x_4490_, 1, v___x_4489_);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v_snd_4444_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 1, v___x_4491_);
lean_ctor_set(v___x_4446_, 0, v___x_4455_);
v___x_4493_ = v___x_4446_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
size_t v___x_4494_; size_t v___x_4495_; 
v___x_4494_ = ((size_t)1ULL);
v___x_4495_ = lean_usize_add(v_i_4435_, v___x_4494_);
v_i_4435_ = v___x_4495_;
v_b_4436_ = v___x_4493_;
goto _start;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec(v_a_4473_);
lean_del_object(v___x_4452_);
lean_del_object(v___x_4446_);
lean_dec(v_snd_4444_);
lean_dec_ref(v_values_4432_);
lean_dec_ref(v_xs_4431_);
lean_dec_ref(v_k_4429_);
v_a_4499_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4479_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4479_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
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
lean_object* v___x_4508_; 
lean_del_object(v___x_4452_);
lean_dec_ref(v_comb_4450_);
lean_del_object(v___x_4446_);
lean_dec(v_snd_4444_);
lean_dec_ref(v_values_4432_);
lean_dec_ref(v_xs_4431_);
lean_dec_ref(v_k_4429_);
if (v_isShared_4476_ == 0)
{
v___x_4508_ = v___x_4475_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4473_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4429_ = stack[0].m_obj;
lean_object* v_fnNames_4430_ = stack[1].m_obj;
lean_object* v_xs_4431_ = stack[2].m_obj;
lean_object* v_values_4432_ = stack[3].m_obj;
lean_object* v_as_4433_ = stack[4].m_obj;
size_t v_sz_4434_ = stack[5].m_num;
size_t v_i_4435_ = stack[6].m_num;
lean_object* v_b_4436_ = stack[7].m_obj;
lean_object* v___y_4437_ = stack[8].m_obj;
lean_object* v___y_4438_ = stack[9].m_obj;
lean_object* v___y_4439_ = stack[10].m_obj;
lean_object* v___y_4440_ = stack[11].m_obj;
lean_object* v_res_4516_;
v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4429_, v_fnNames_4430_, v_xs_4431_, v_values_4432_, v_as_4433_, v_sz_4434_, v_i_4435_, v_b_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
stack->m_obj
 = v_res_4516_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4517_, lean_object* v_fnNames_4518_, lean_object* v_xs_4519_, lean_object* v_values_4520_, lean_object* v_as_4521_, lean_object* v_sz_4522_, lean_object* v_i_4523_, lean_object* v_b_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4522_);
lean_dec(v_sz_4522_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4523_);
lean_dec(v_i_4523_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4517_, v_fnNames_4518_, v_xs_4519_, v_values_4520_, v_as_4521_, v_sz_boxed_4530_, v_i_boxed_4531_, v_b_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v_as_4521_);
lean_dec_ref(v_fnNames_4518_);
return v_res_4532_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4535_ = l_Lean_stringToMessageData(v___x_4534_);
return v___x_4535_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4538_ = l_Lean_stringToMessageData(v___x_4537_);
return v___x_4538_;
}
}
lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4539_, lean_object* v_xs_4540_, lean_object* v_values_4541_, lean_object* v_candidates_4542_, lean_object* v_k_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_candidates_4549_; lean_object* v_report_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4610_; 
v_candidates_4549_ = lean_ctor_get(v_candidates_4542_, 0);
v_report_4550_ = lean_ctor_get(v_candidates_4542_, 1);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_candidates_4542_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4552_ = v_candidates_4542_;
v_isShared_4553_ = v_isSharedCheck_4610_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_report_4550_);
lean_inc(v_candidates_4549_);
lean_dec(v_candidates_4542_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4610_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = lean_box(0);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4554_);
v___x_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4554_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_report_4550_);
v___x_4556_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
size_t v_sz_4557_; size_t v___x_4558_; lean_object* v___x_4559_; 
v_sz_4557_ = lean_array_size(v_candidates_4549_);
v___x_4558_ = ((size_t)0ULL);
v___x_4559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4543_, v_fnNames_4539_, v_xs_4540_, v_values_4541_, v_candidates_4549_, v_sz_4557_, v___x_4558_, v___x_4556_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
lean_dec_ref(v_candidates_4549_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4600_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4600_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4600_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v_fst_4564_; 
v_fst_4564_ = lean_ctor_get(v_a_4560_, 0);
if (lean_obj_tag(v_fst_4564_) == 0)
{
lean_object* v_toCold_4565_; lean_object* v_options_4566_; lean_object* v_snd_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4594_; 
lean_del_object(v___x_4562_);
v_toCold_4565_ = lean_ctor_get(v_a_4546_, 0);
v_options_4566_ = lean_ctor_get(v_toCold_4565_, 2);
v_snd_4567_ = lean_ctor_get(v_a_4560_, 1);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_a_4560_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v_a_4560_, 0);
lean_dec(v_unused_4595_);
v___x_4569_ = v_a_4560_;
v_isShared_4570_ = v_isSharedCheck_4594_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_snd_4567_);
lean_dec(v_a_4560_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4594_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v_inheritedTraceOptions_4571_; uint8_t v_hasTrace_4572_; lean_object* v___x_4573_; lean_object* v___x_4575_; 
v_inheritedTraceOptions_4571_ = lean_ctor_get(v_toCold_4565_, 11);
v_hasTrace_4572_ = lean_ctor_get_uint8(v_options_4566_, sizeof(void*)*1);
v___x_4573_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4570_ == 0)
{
lean_ctor_set_tag(v___x_4569_, 7);
lean_ctor_set(v___x_4569_, 0, v___x_4573_);
v___x_4575_ = v___x_4569_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4573_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_snd_4567_);
v___x_4575_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
if (v_hasTrace_4572_ == 0)
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4575_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4577_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4578_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4579_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4571_, v_options_4566_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4575_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4575_);
v___x_4582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v___x_4575_);
v___x_4583_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4577_, v___x_4582_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v___x_4584_; 
lean_dec_ref_known(v___x_4583_, 1);
v___x_4584_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4575_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v___x_4575_);
v_a_4585_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4583_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4583_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
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
lean_object* v_val_4596_; lean_object* v___x_4598_; 
lean_inc_ref(v_fst_4564_);
lean_dec(v_a_4560_);
v_val_4596_ = lean_ctor_get(v_fst_4564_, 0);
lean_inc(v_val_4596_);
lean_dec_ref_known(v_fst_4564_, 1);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v_val_4596_);
v___x_4598_ = v___x_4562_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_val_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
v_a_4601_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4559_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4559_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_tryCandidates___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_4539_ = stack[0].m_obj;
lean_object* v_xs_4540_ = stack[1].m_obj;
lean_object* v_values_4541_ = stack[2].m_obj;
lean_object* v_candidates_4542_ = stack[3].m_obj;
lean_object* v_k_4543_ = stack[4].m_obj;
lean_object* v_a_4544_ = stack[5].m_obj;
lean_object* v_a_4545_ = stack[6].m_obj;
lean_object* v_a_4546_ = stack[7].m_obj;
lean_object* v_a_4547_ = stack[8].m_obj;
lean_object* v_res_4611_;
v_res_4611_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4539_, v_xs_4540_, v_values_4541_, v_candidates_4542_, v_k_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
stack->m_obj
 = v_res_4611_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4612_, lean_object* v_xs_4613_, lean_object* v_values_4614_, lean_object* v_candidates_4615_, lean_object* v_k_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4612_, v_xs_4613_, v_values_4614_, v_candidates_4615_, v_k_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec_ref(v_fnNames_4612_);
return v_res_4622_;
}
}
lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4623_, lean_object* v_fnNames_4624_, lean_object* v_xs_4625_, lean_object* v_values_4626_, lean_object* v_candidates_4627_, lean_object* v_k_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4624_, v_xs_4625_, v_values_4626_, v_candidates_4627_, v_k_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
return v___x_4634_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_tryCandidates_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_4624_ = stack[1].m_obj;
lean_object* v_xs_4625_ = stack[2].m_obj;
lean_object* v_values_4626_ = stack[3].m_obj;
lean_object* v_candidates_4627_ = stack[4].m_obj;
lean_object* v_k_4628_ = stack[5].m_obj;
lean_object* v_a_4629_ = stack[6].m_obj;
lean_object* v_a_4630_ = stack[7].m_obj;
lean_object* v_a_4631_ = stack[8].m_obj;
lean_object* v_a_4632_ = stack[9].m_obj;
lean_object* v_res_4635_;
v_res_4635_ = l_Lean_Elab_Structural_tryCandidates(lean_box(0), v_fnNames_4624_, v_xs_4625_, v_values_4626_, v_candidates_4627_, v_k_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
stack->m_obj
 = v_res_4635_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4636_, lean_object* v_fnNames_4637_, lean_object* v_xs_4638_, lean_object* v_values_4639_, lean_object* v_candidates_4640_, lean_object* v_k_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4636_, v_fnNames_4637_, v_xs_4638_, v_values_4639_, v_candidates_4640_, v_k_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec_ref(v_fnNames_4637_);
return v_res_4647_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4648_, lean_object* v_k_4649_, lean_object* v_fnNames_4650_, lean_object* v_xs_4651_, lean_object* v_values_4652_, lean_object* v_as_4653_, size_t v_sz_4654_, size_t v_i_4655_, lean_object* v_b_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4649_, v_fnNames_4650_, v_xs_4651_, v_values_4652_, v_as_4653_, v_sz_4654_, v_i_4655_, v_b_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
return v___x_4662_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4649_ = stack[1].m_obj;
lean_object* v_fnNames_4650_ = stack[2].m_obj;
lean_object* v_xs_4651_ = stack[3].m_obj;
lean_object* v_values_4652_ = stack[4].m_obj;
lean_object* v_as_4653_ = stack[5].m_obj;
size_t v_sz_4654_ = stack[6].m_num;
size_t v_i_4655_ = stack[7].m_num;
lean_object* v_b_4656_ = stack[8].m_obj;
lean_object* v___y_4657_ = stack[9].m_obj;
lean_object* v___y_4658_ = stack[10].m_obj;
lean_object* v___y_4659_ = stack[11].m_obj;
lean_object* v___y_4660_ = stack[12].m_obj;
lean_object* v_res_4663_;
v_res_4663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_box(0), v_k_4649_, v_fnNames_4650_, v_xs_4651_, v_values_4652_, v_as_4653_, v_sz_4654_, v_i_4655_, v_b_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
stack->m_obj
 = v_res_4663_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4664_, lean_object* v_k_4665_, lean_object* v_fnNames_4666_, lean_object* v_xs_4667_, lean_object* v_values_4668_, lean_object* v_as_4669_, lean_object* v_sz_4670_, lean_object* v_i_4671_, lean_object* v_b_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
size_t v_sz_boxed_4678_; size_t v_i_boxed_4679_; lean_object* v_res_4680_; 
v_sz_boxed_4678_ = lean_unbox_usize(v_sz_4670_);
lean_dec(v_sz_4670_);
v_i_boxed_4679_ = lean_unbox_usize(v_i_4671_);
lean_dec(v_i_4671_);
v_res_4680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4664_, v_k_4665_, v_fnNames_4666_, v_xs_4667_, v_values_4668_, v_as_4669_, v_sz_boxed_4678_, v_i_boxed_4679_, v_b_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec_ref(v_as_4669_);
lean_dec_ref(v_fnNames_4666_);
return v_res_4680_;
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
