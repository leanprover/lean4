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
lean_object* v___f_973_; lean_object* v___x_4723__overap_974_; lean_object* v___x_975_; 
v___f_973_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4723__overap_974_ = lean_panic_fn_borrowed(v___f_973_, v_msg_967_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
v___x_975_ = lean_apply_5(v___x_4723__overap_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
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
v___x_1229_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1222_);
if (v___x_1229_ == 0)
{
lean_object* v_name_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1230_ = lean_ctor_get(v___y_1221_, 0);
lean_inc(v_name_1230_);
lean_dec_ref(v___y_1221_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1232_ = l_Lean_MessageData_ofName(v_name_1230_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_indentExpr(v___y_1228_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1237_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1202_, v_xs_1203_);
v___x_1240_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1239_, v___y_1222_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
if (lean_obj_tag(v_a_1241_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1239_, v___y_1223_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
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
lean_dec_ref(v___y_1228_);
v_name_1247_ = lean_ctor_get(v___y_1221_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1221_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; 
v_unused_1268_ = lean_ctor_get(v___y_1221_, 2);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v___y_1221_, 1);
lean_dec(v_unused_1269_);
v___x_1249_ = v___y_1221_;
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_name_1247_);
lean_dec(v___y_1221_);
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
v_sz_1254_ = lean_array_size(v___y_1222_);
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1203_, v_sz_1254_, v___x_1255_, v___y_1222_);
v___x_1257_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1218_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 2, v___y_1223_);
lean_ctor_set(v___x_1249_, 1, v___y_1226_);
lean_ctor_set(v___x_1249_, 0, v___x_1257_);
v___x_1259_ = v___x_1249_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___y_1226_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___y_1223_);
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
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v___x_1265_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1266_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1265_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_val_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1245_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
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
v___x_1277_ = l_Lean_indentExpr(v___y_1228_);
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
v___x_1290_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1289_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
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
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
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
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1218_);
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
v_name_1308_ = lean_ctor_get(v___y_1221_, 0);
lean_inc(v_name_1308_);
lean_dec_ref(v___y_1221_);
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
v___x_1315_ = l_Lean_indentExpr(v___y_1228_);
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
v___x_1325_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1324_, v___y_1220_, v___y_1224_, v___y_1227_, v___y_1219_);
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
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1218_);
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
v___x_1356_ = lean_nat_dec_lt(v___y_1350_, v___x_1355_);
lean_dec(v___y_1350_);
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___y_1347_;
v___y_1220_ = v___y_1348_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___x_1354_;
v___y_1223_ = v___y_1340_;
v___y_1224_ = v___y_1341_;
v___y_1225_ = v___y_1342_;
v___y_1226_ = v___y_1343_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1346_;
goto v___jp_1217_;
}
else
{
if (v___x_1356_ == 0)
{
v___y_1218_ = v___y_1339_;
v___y_1219_ = v___y_1347_;
v___y_1220_ = v___y_1348_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___x_1354_;
v___y_1223_ = v___y_1340_;
v___y_1224_ = v___y_1341_;
v___y_1225_ = v___y_1342_;
v___y_1226_ = v___y_1343_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1346_;
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
v___y_1219_ = v___y_1347_;
v___y_1220_ = v___y_1348_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___x_1354_;
v___y_1223_ = v___y_1340_;
v___y_1224_ = v___y_1341_;
v___y_1225_ = v___y_1342_;
v___y_1226_ = v___y_1343_;
v___y_1227_ = v___y_1345_;
v___y_1228_ = v___y_1346_;
goto v___jp_1217_;
}
else
{
lean_object* v_name_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___x_1354_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v_i_1204_);
lean_dec_ref(v_fixedParamPerm_1202_);
lean_dec(v_fnName_1201_);
v_name_1360_ = lean_ctor_get(v___y_1349_, 0);
lean_inc(v_name_1360_);
lean_dec_ref(v___y_1349_);
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1362_ = l_Lean_MessageData_ofName(v_name_1360_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_indentExpr(v___y_1346_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1367_, v___y_1348_, v___y_1341_, v___y_1345_, v___y_1347_);
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
v___y_1339_ = v_val_1386_;
v___y_1340_ = v___x_1398_;
v___y_1341_ = v___y_1372_;
v___y_1342_ = v_all_1389_;
v___y_1343_ = v_us_1380_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v_a_1377_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1371_;
v___y_1349_ = v_toConstantVal_1387_;
v___y_1350_ = v___x_1396_;
v_lower_1351_ = v_numParams_1388_;
v_upper_1352_ = v___x_1399_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v_val_1386_;
v___y_1340_ = v___x_1398_;
v___y_1341_ = v___y_1372_;
v___y_1342_ = v_all_1389_;
v___y_1343_ = v_us_1380_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v_a_1377_;
v___y_1347_ = v___y_1374_;
v___y_1348_ = v___y_1371_;
v___y_1349_ = v_toConstantVal_1387_;
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
lean_object* v_val_1735_; lean_object* v_ref_1736_; lean_object* v_toCold_1737_; lean_object* v_currRecDepth_1738_; lean_object* v_ref_1739_; uint16_t v_optionFlags_1740_; uint8_t v_suppressElabErrors_1741_; uint8_t v_checkDeprecated_1742_; uint8_t v_isRecordingDeps_1743_; lean_object* v___f_1744_; lean_object* v_args_1745_; lean_object* v___f_1746_; lean_object* v_ref_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
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
v_checkDeprecated_1742_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1743_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*3 + 4);
v___f_1744_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1725_);
v_args_1745_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1725_, v_xs_1726_, v_ys_1728_);
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1746_, 0, v_val_1735_);
lean_closure_set(v___f_1746_, 1, v_fnName_1727_);
lean_closure_set(v___f_1746_, 2, v_fixedParamPerm_1725_);
lean_closure_set(v___f_1746_, 3, v_args_1745_);
v_ref_1747_ = l_Lean_replaceRef(v_ref_1736_, v_ref_1739_);
lean_dec(v_ref_1736_);
lean_inc(v_currRecDepth_1738_);
lean_inc_ref(v_toCold_1737_);
v___x_1748_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1748_, 0, v_toCold_1737_);
lean_ctor_set(v___x_1748_, 1, v_currRecDepth_1738_);
lean_ctor_set(v___x_1748_, 2, v_ref_1747_);
lean_ctor_set_uint16(v___x_1748_, sizeof(void*)*3, v_optionFlags_1740_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*3 + 2, v_suppressElabErrors_1741_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*3 + 3, v_checkDeprecated_1742_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*3 + 4, v_isRecordingDeps_1743_);
v___x_1749_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1746_, v___f_1744_, v___y_1730_, v___y_1731_, v___x_1748_, v___y_1733_);
lean_dec_ref_known(v___x_1748_, 3);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1762_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
v___x_1756_ = lean_array_push(v___x_1755_, v_a_1750_);
v___x_1757_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1758_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1749_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1749_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_args_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v_termMeasure_x3f_1724_);
lean_inc_ref(v_fixedParamPerm_1725_);
v_args_1771_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1725_, v_xs_1726_, v_ys_1728_);
v___x_1772_ = lean_array_get_size(v_args_1771_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1772_, v_fnName_1727_, v_fixedParamPerm_1725_, v_args_1771_, v___x_1773_, v___x_1774_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec_ref(v_args_1771_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1811_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1811_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1811_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1810_; 
v_fst_1780_ = lean_ctor_get(v_a_1776_, 0);
v_snd_1781_ = lean_ctor_get(v_a_1776_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1783_ = v_a_1776_;
v_isShared_1784_ = v_isSharedCheck_1810_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_snd_1781_);
lean_inc(v_fst_1780_);
lean_dec(v_a_1776_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1810_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_toCold_1792_; lean_object* v_options_1793_; uint8_t v_hasTrace_1794_; 
v_toCold_1792_ = lean_ctor_get(v___y_1732_, 0);
v_options_1793_ = lean_ctor_get(v_toCold_1792_, 2);
v_hasTrace_1794_ = lean_ctor_get_uint8(v_options_1793_, sizeof(void*)*1);
if (v_hasTrace_1794_ == 0)
{
goto v___jp_1785_;
}
else
{
lean_object* v_inheritedTraceOptions_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_inheritedTraceOptions_1795_ = lean_ctor_get(v_toCold_1792_, 11);
v___x_1796_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1795_, v_options_1793_, v___x_1797_);
if (v___x_1798_ == 0)
{
goto v___jp_1785_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1781_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v_snd_1781_);
v___x_1801_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1796_, v___x_1800_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_dec_ref_known(v___x_1801_, 1);
goto v___jp_1785_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_del_object(v___x_1783_);
lean_dec(v_snd_1781_);
lean_dec(v_fst_1780_);
lean_del_object(v___x_1778_);
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
v___jp_1785_:
{
lean_object* v___x_1787_; 
if (v_isShared_1784_ == 0)
{
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_fst_1780_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_snd_1781_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1787_);
v___x_1789_ = v___x_1778_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
else
{
return v___x_1775_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
return v_x_1878_;
}
else
{
lean_object* v_key_1880_; lean_object* v_value_1881_; lean_object* v_tail_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1905_; 
v_key_1880_ = lean_ctor_get(v_x_1879_, 0);
v_value_1881_ = lean_ctor_get(v_x_1879_, 1);
v_tail_1882_ = lean_ctor_get(v_x_1879_, 2);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1884_ = v_x_1879_;
v_isShared_1885_ = v_isSharedCheck_1905_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_tail_1882_);
lean_inc(v_value_1881_);
lean_inc(v_key_1880_);
lean_dec(v_x_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1905_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; uint64_t v_fold_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1886_ = lean_array_get_size(v_x_1878_);
v___x_1887_ = lean_uint64_of_nat(v_key_1880_);
v___x_1888_ = 32ULL;
v___x_1889_ = lean_uint64_shift_right(v___x_1887_, v___x_1888_);
v_fold_1890_ = lean_uint64_xor(v___x_1887_, v___x_1889_);
v___x_1891_ = 16ULL;
v___x_1892_ = lean_uint64_shift_right(v_fold_1890_, v___x_1891_);
v___x_1893_ = lean_uint64_xor(v_fold_1890_, v___x_1892_);
v___x_1894_ = lean_uint64_to_usize(v___x_1893_);
v___x_1895_ = lean_usize_of_nat(v___x_1886_);
v___x_1896_ = ((size_t)1ULL);
v___x_1897_ = lean_usize_sub(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_usize_land(v___x_1894_, v___x_1897_);
v___x_1899_ = lean_array_uget_borrowed(v_x_1878_, v___x_1898_);
lean_inc(v___x_1899_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v___x_1899_);
v___x_1901_ = v___x_1884_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_key_1880_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_value_1881_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_array_uset(v_x_1878_, v___x_1898_, v___x_1901_);
v_x_1878_ = v___x_1902_;
v_x_1879_ = v_tail_1882_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1906_, lean_object* v_source_1907_, lean_object* v_target_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_array_get_size(v_source_1907_);
v___x_1910_ = lean_nat_dec_lt(v_i_1906_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_dec_ref(v_source_1907_);
lean_dec(v_i_1906_);
return v_target_1908_;
}
else
{
lean_object* v_es_1911_; lean_object* v___x_1912_; lean_object* v_source_1913_; lean_object* v_target_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_es_1911_ = lean_array_fget(v_source_1907_, v_i_1906_);
v___x_1912_ = lean_box(0);
v_source_1913_ = lean_array_fset(v_source_1907_, v_i_1906_, v___x_1912_);
v_target_1914_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1908_, v_es_1911_);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_i_1906_, v___x_1915_);
lean_dec(v_i_1906_);
v_i_1906_ = v___x_1916_;
v_source_1907_ = v_source_1913_;
v_target_1908_ = v_target_1914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_nbuckets_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1919_ = lean_array_get_size(v_data_1918_);
v___x_1920_ = lean_unsigned_to_nat(2u);
v_nbuckets_1921_ = lean_nat_mul(v___x_1919_, v___x_1920_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_mk_array(v_nbuckets_1921_, v___x_1923_);
v___x_1925_ = lean_array_propagate_mark(v_data_1918_, v___x_1924_);
v___x_1926_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1922_, v_data_1918_, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1927_, lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = 0;
return v___x_1929_;
}
else
{
lean_object* v_key_1930_; lean_object* v_tail_1931_; uint8_t v___x_1932_; 
v_key_1930_ = lean_ctor_get(v_x_1928_, 0);
v_tail_1931_ = lean_ctor_get(v_x_1928_, 2);
v___x_1932_ = lean_nat_dec_eq(v_key_1930_, v_a_1927_);
if (v___x_1932_ == 0)
{
v_x_1928_ = v_tail_1931_;
goto _start;
}
else
{
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1934_, lean_object* v_x_1935_){
_start:
{
uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1934_, v_x_1935_);
lean_dec(v_x_1935_);
lean_dec(v_a_1934_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1938_, lean_object* v_a_1939_, lean_object* v_b_1940_){
_start:
{
lean_object* v_size_1941_; lean_object* v_buckets_1942_; lean_object* v___x_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; uint64_t v___x_1946_; uint64_t v_fold_1947_; uint64_t v___x_1948_; uint64_t v___x_1949_; uint64_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; lean_object* v_bkt_1956_; uint8_t v___x_1957_; 
v_size_1941_ = lean_ctor_get(v_m_1938_, 0);
v_buckets_1942_ = lean_ctor_get(v_m_1938_, 1);
v___x_1943_ = lean_array_get_size(v_buckets_1942_);
v___x_1944_ = lean_uint64_of_nat(v_a_1939_);
v___x_1945_ = 32ULL;
v___x_1946_ = lean_uint64_shift_right(v___x_1944_, v___x_1945_);
v_fold_1947_ = lean_uint64_xor(v___x_1944_, v___x_1946_);
v___x_1948_ = 16ULL;
v___x_1949_ = lean_uint64_shift_right(v_fold_1947_, v___x_1948_);
v___x_1950_ = lean_uint64_xor(v_fold_1947_, v___x_1949_);
v___x_1951_ = lean_uint64_to_usize(v___x_1950_);
v___x_1952_ = lean_usize_of_nat(v___x_1943_);
v___x_1953_ = ((size_t)1ULL);
v___x_1954_ = lean_usize_sub(v___x_1952_, v___x_1953_);
v___x_1955_ = lean_usize_land(v___x_1951_, v___x_1954_);
v_bkt_1956_ = lean_array_uget_borrowed(v_buckets_1942_, v___x_1955_);
v___x_1957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1939_, v_bkt_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1978_; 
lean_inc_ref(v_buckets_1942_);
lean_inc(v_size_1941_);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_m_1938_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; lean_object* v_unused_1980_; 
v_unused_1979_ = lean_ctor_get(v_m_1938_, 1);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_m_1938_, 0);
lean_dec(v_unused_1980_);
v___x_1959_ = v_m_1938_;
v_isShared_1960_ = v_isSharedCheck_1978_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v_m_1938_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1978_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v_size_x27_1962_; lean_object* v___x_1963_; lean_object* v_buckets_x27_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v_size_x27_1962_ = lean_nat_add(v_size_1941_, v___x_1961_);
lean_dec(v_size_1941_);
lean_inc(v_bkt_1956_);
v___x_1963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1963_, 0, v_a_1939_);
lean_ctor_set(v___x_1963_, 1, v_b_1940_);
lean_ctor_set(v___x_1963_, 2, v_bkt_1956_);
v_buckets_x27_1964_ = lean_array_uset(v_buckets_1942_, v___x_1955_, v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(4u);
v___x_1966_ = lean_nat_mul(v_size_x27_1962_, v___x_1965_);
v___x_1967_ = lean_unsigned_to_nat(3u);
v___x_1968_ = lean_nat_div(v___x_1966_, v___x_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_array_get_size(v_buckets_x27_1964_);
v___x_1970_ = lean_nat_dec_le(v___x_1968_, v___x_1969_);
lean_dec(v___x_1968_);
if (v___x_1970_ == 0)
{
lean_object* v_val_1971_; lean_object* v___x_1973_; 
v_val_1971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1964_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v_val_1971_);
lean_ctor_set(v___x_1959_, 0, v_size_x27_1962_);
v___x_1973_ = v___x_1959_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_size_x27_1962_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_val_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
else
{
lean_object* v___x_1976_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v_buckets_x27_1964_);
lean_ctor_set(v___x_1959_, 0, v_size_x27_1962_);
v___x_1976_ = v___x_1959_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_size_x27_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_buckets_x27_1964_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_dec(v_b_1940_);
lean_dec(v_a_1939_);
return v_m_1938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1981_, size_t v_sz_1982_, size_t v_i_1983_, lean_object* v_b_1984_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_usize_dec_lt(v_i_1983_, v_sz_1982_);
if (v___x_1985_ == 0)
{
return v_b_1984_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; 
v_a_1986_ = lean_array_uget_borrowed(v_as_1981_, v_i_1983_);
v___x_1987_ = lean_box(0);
lean_inc(v_a_1986_);
v___x_1988_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1984_, v_a_1986_, v___x_1987_);
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1983_, v___x_1989_);
v_i_1983_ = v___x_1990_;
v_b_1984_ = v___x_1988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1992_, lean_object* v_sz_1993_, lean_object* v_i_1994_, lean_object* v_b_1995_){
_start:
{
size_t v_sz_boxed_1996_; size_t v_i_boxed_1997_; lean_object* v_res_1998_; 
v_sz_boxed_1996_ = lean_unbox_usize(v_sz_1993_);
lean_dec(v_sz_1993_);
v_i_boxed_1997_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1992_, v_sz_boxed_1996_, v_i_boxed_1997_, v_b_1995_);
lean_dec_ref(v_as_1992_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2003_ == 0)
{
return v_b_2002_;
}
else
{
lean_object* v_a_2004_; lean_object* v_indicesPos_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; 
v_a_2004_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
v_indicesPos_2005_ = lean_ctor_get(v_a_2004_, 3);
v_sz_2006_ = lean_array_size(v_indicesPos_2005_);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2005_, v_sz_2006_, v___x_2007_, v_b_2002_);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_2001_, v___x_2009_);
v_i_2001_ = v___x_2010_;
v_b_2002_ = v___x_2008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2012_, lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_b_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2012_, v_sz_boxed_2016_, v_i_boxed_2017_, v_b_2015_);
lean_dec_ref(v_as_2012_);
return v_res_2018_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_buckets_2021_; lean_object* v___x_2022_; uint64_t v___x_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; uint64_t v_fold_2026_; uint64_t v___x_2027_; uint64_t v___x_2028_; uint64_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_buckets_2021_ = lean_ctor_get(v_m_2019_, 1);
v___x_2022_ = lean_array_get_size(v_buckets_2021_);
v___x_2023_ = lean_uint64_of_nat(v_a_2020_);
v___x_2024_ = 32ULL;
v___x_2025_ = lean_uint64_shift_right(v___x_2023_, v___x_2024_);
v_fold_2026_ = lean_uint64_xor(v___x_2023_, v___x_2025_);
v___x_2027_ = 16ULL;
v___x_2028_ = lean_uint64_shift_right(v_fold_2026_, v___x_2027_);
v___x_2029_ = lean_uint64_xor(v_fold_2026_, v___x_2028_);
v___x_2030_ = lean_uint64_to_usize(v___x_2029_);
v___x_2031_ = lean_usize_of_nat(v___x_2022_);
v___x_2032_ = ((size_t)1ULL);
v___x_2033_ = lean_usize_sub(v___x_2031_, v___x_2032_);
v___x_2034_ = lean_usize_land(v___x_2030_, v___x_2033_);
v___x_2035_ = lean_array_uget_borrowed(v_buckets_2021_, v___x_2034_);
v___x_2036_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2020_, v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2037_, lean_object* v_a_2038_){
_start:
{
uint8_t v_res_2039_; lean_object* v_r_2040_; 
v_res_2039_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_m_2037_);
v_r_2040_ = lean_box(v_res_2039_);
return v_r_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2041_, lean_object* v_as_2042_, size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v_a_2047_; uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2051_ == 0)
{
return v_b_2045_;
}
else
{
lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2068_; 
v_fst_2052_ = lean_ctor_get(v_b_2045_, 0);
v_snd_2053_ = lean_ctor_get(v_b_2045_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_b_2045_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2055_ = v_b_2045_;
v_isShared_2056_ = v_isSharedCheck_2068_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_snd_2053_);
lean_inc(v_fst_2052_);
lean_dec(v_b_2045_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2068_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_a_2057_; lean_object* v_recArgPos_2058_; uint8_t v___x_2059_; 
v_a_2057_ = lean_array_uget_borrowed(v_as_2042_, v_i_2044_);
v_recArgPos_2058_ = lean_ctor_get(v_a_2057_, 2);
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2041_, v_recArgPos_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_inc(v_a_2057_);
v___x_2060_ = lean_array_push(v_snd_2053_, v_a_2057_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v___x_2060_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_fst_2052_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_2047_ = v___x_2062_;
goto v___jp_2046_;
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_inc(v_a_2057_);
v___x_2064_ = lean_array_push(v_fst_2052_, v_a_2057_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2064_);
v___x_2066_ = v___x_2055_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_snd_2053_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_a_2047_ = v___x_2066_;
goto v___jp_2046_;
}
}
}
}
v___jp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; 
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2044_, v___x_2048_);
v_i_2044_ = v___x_2049_;
v_b_2045_ = v_a_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2069_, lean_object* v_as_2070_, lean_object* v_sz_2071_, lean_object* v_i_2072_, lean_object* v_b_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2071_);
lean_dec(v_sz_2071_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2072_);
lean_dec(v_i_2072_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2069_, v_as_2070_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2073_);
lean_dec_ref(v_as_2070_);
lean_dec_ref(v___x_2069_);
return v_res_2076_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_unsigned_to_nat(16u);
v___x_2079_ = lean_mk_array(v___x_2078_, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_indicesPos_2082_; 
v___x_2080_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2081_ = lean_unsigned_to_nat(0u);
v_indicesPos_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2082_, 0, v___x_2081_);
lean_ctor_set(v_indicesPos_2082_, 1, v___x_2080_);
return v_indicesPos_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2085_){
_start:
{
lean_object* v_indicesPos_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_fst_2092_; lean_object* v_snd_2093_; lean_object* v___x_2094_; 
v_indicesPos_2086_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2087_ = lean_array_size(v_recArgInfos_2085_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2085_, v_sz_2087_, v___x_2088_, v_indicesPos_2086_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2089_, v_recArgInfos_2085_, v_sz_2087_, v___x_2088_, v___x_2090_);
lean_dec_ref(v___x_2089_);
v_fst_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_fst_2092_);
v_snd_2093_ = lean_ctor_get(v___x_2091_, 1);
lean_inc(v_snd_2093_);
lean_dec_ref(v___x_2091_);
v___x_2094_ = l_Array_append___redArg(v_snd_2093_, v_fst_2092_);
lean_dec(v_fst_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2095_);
lean_dec_ref(v_recArgInfos_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2097_, lean_object* v_m_2098_, lean_object* v_a_2099_, lean_object* v_b_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2098_, v_a_2099_, v_b_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2102_, lean_object* v_m_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2103_, v_a_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2106_, lean_object* v_m_2107_, lean_object* v_a_2108_){
_start:
{
uint8_t v_res_2109_; lean_object* v_r_2110_; 
v_res_2109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2106_, v_m_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_m_2107_);
v_r_2110_ = lean_box(v_res_2109_);
return v_r_2110_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2111_, lean_object* v_a_2112_, lean_object* v_x_2113_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2112_, v_x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2115_, lean_object* v_a_2116_, lean_object* v_x_2117_){
_start:
{
uint8_t v_res_2118_; lean_object* v_r_2119_; 
v_res_2118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2115_, v_a_2116_, v_x_2117_);
lean_dec(v_x_2117_);
lean_dec(v_a_2116_);
v_r_2119_ = lean_box(v_res_2118_);
return v_r_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2120_, lean_object* v_data_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2123_, lean_object* v_i_2124_, lean_object* v_source_2125_, lean_object* v_target_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2124_, v_source_2125_, v_target_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2129_, v_x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2132_, lean_object* v_a_2133_, lean_object* v_toPure_2134_, uint8_t v_____do__lift_2135_){
_start:
{
if (v_____do__lift_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_array_push(v___y_2132_, v_a_2133_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
v___x_2138_ = lean_apply_2(v_toPure_2134_, lean_box(0), v___x_2137_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v_a_2133_);
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2132_);
v___x_2140_ = lean_apply_2(v_toPure_2134_, lean_box(0), v___x_2139_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2141_, lean_object* v_a_2142_, lean_object* v_toPure_2143_, lean_object* v_____do__lift_2144_){
_start:
{
uint8_t v_____do__lift_159__boxed_2145_; lean_object* v_res_2146_; 
v_____do__lift_159__boxed_2145_ = lean_unbox(v_____do__lift_2144_);
v_res_2146_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2141_, v_a_2142_, v_toPure_2143_, v_____do__lift_159__boxed_2145_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2147_, lean_object* v_a_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_apply_2(v_eq_2147_, v_x_2149_, v_a_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2151_, lean_object* v___x_2152_, lean_object* v_toBind_2153_, lean_object* v_eq_2154_, lean_object* v_inst_2155_, lean_object* v_a_2156_, lean_object* v_x_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___f_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
lean_inc(v_toPure_2151_);
lean_inc(v_a_2156_);
lean_inc_ref(v___y_2158_);
v___f_2159_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2159_, 0, v___y_2158_);
lean_closure_set(v___f_2159_, 1, v_a_2156_);
lean_closure_set(v___f_2159_, 2, v_toPure_2151_);
v___x_2160_ = lean_array_get_size(v___y_2158_);
v___x_2161_ = lean_nat_dec_lt(v___x_2152_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v___y_2158_);
lean_dec(v_a_2156_);
lean_dec_ref(v_inst_2155_);
lean_dec(v_eq_2154_);
v___x_2162_ = lean_box(v___x_2161_);
v___x_2163_ = lean_apply_2(v_toPure_2151_, lean_box(0), v___x_2162_);
v___x_2164_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v___x_2163_, v___f_2159_);
return v___x_2164_;
}
else
{
if (v___x_2161_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v___y_2158_);
lean_dec(v_a_2156_);
lean_dec_ref(v_inst_2155_);
lean_dec(v_eq_2154_);
v___x_2165_ = lean_box(v___x_2161_);
v___x_2166_ = lean_apply_2(v_toPure_2151_, lean_box(0), v___x_2165_);
v___x_2167_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v___x_2166_, v___f_2159_);
return v___x_2167_;
}
else
{
lean_object* v___f_2168_; size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_toPure_2151_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2168_, 0, v_eq_2154_);
lean_closure_set(v___f_2168_, 1, v_a_2156_);
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_of_nat(v___x_2160_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2155_, v___f_2168_, v___y_2158_, v___x_2169_, v___x_2170_);
v___x_2172_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v___x_2171_, v___f_2159_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2173_, lean_object* v___x_2174_, lean_object* v_toBind_2175_, lean_object* v_eq_2176_, lean_object* v_inst_2177_, lean_object* v_a_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2173_, v___x_2174_, v_toBind_2175_, v_eq_2176_, v_inst_2177_, v_a_2178_, v_x_2179_, v___y_2180_);
lean_dec(v___x_2174_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2182_, lean_object* v_____s_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_apply_2(v_toPure_2182_, lean_box(0), v_____s_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2187_, lean_object* v_eq_2188_, lean_object* v_xs_2189_){
_start:
{
lean_object* v_toApplicative_2190_; lean_object* v_toBind_2191_; lean_object* v_toPure_2192_; lean_object* v___x_2193_; lean_object* v_ret_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_toApplicative_2190_ = lean_ctor_get(v_inst_2187_, 0);
v_toBind_2191_ = lean_ctor_get(v_inst_2187_, 1);
lean_inc_n(v_toBind_2191_, 2);
v_toPure_2192_ = lean_ctor_get(v_toApplicative_2190_, 1);
v___x_2193_ = lean_unsigned_to_nat(0u);
v_ret_2194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2187_);
lean_inc_n(v_toPure_2192_, 2);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2195_, 0, v_toPure_2192_);
lean_closure_set(v___f_2195_, 1, v___x_2193_);
lean_closure_set(v___f_2195_, 2, v_toBind_2191_);
lean_closure_set(v___f_2195_, 3, v_eq_2188_);
lean_closure_set(v___f_2195_, 4, v_inst_2187_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2196_, 0, v_toPure_2192_);
v_sz_2197_ = lean_array_size(v_xs_2189_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2187_, v_xs_2189_, v___f_2195_, v_sz_2197_, v___x_2198_, v_ret_2194_);
v___x_2200_ = lean_apply_4(v_toBind_2191_, lean_box(0), lean_box(0), v___x_2199_, v___f_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2201_, lean_object* v_00_u03b1_2202_, lean_object* v_inst_2203_, lean_object* v_eq_2204_, lean_object* v_xs_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2203_, v_eq_2204_, v_xs_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2207_, size_t v_i_2208_, lean_object* v_bs_2209_){
_start:
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_usize_dec_lt(v_i_2208_, v_sz_2207_);
if (v___x_2210_ == 0)
{
return v_bs_2209_;
}
else
{
lean_object* v_v_2211_; lean_object* v_indGroupInst_2212_; lean_object* v___x_2213_; lean_object* v_bs_x27_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v_v_2211_ = lean_array_uget_borrowed(v_bs_2209_, v_i_2208_);
v_indGroupInst_2212_ = lean_ctor_get(v_v_2211_, 4);
lean_inc_ref(v_indGroupInst_2212_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v_bs_x27_2214_ = lean_array_uset(v_bs_2209_, v_i_2208_, v___x_2213_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_add(v_i_2208_, v___x_2215_);
v___x_2217_ = lean_array_uset(v_bs_x27_2214_, v_i_2208_, v_indGroupInst_2212_);
v_i_2208_ = v___x_2216_;
v_bs_2209_ = v___x_2217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2219_, lean_object* v_i_2220_, lean_object* v_bs_2221_){
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2219_);
lean_dec(v_sz_2219_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2220_);
lean_dec(v_i_2220_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2222_, v_i_boxed_2223_, v_bs_2221_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2225_, lean_object* v_a_2226_, lean_object* v_as_2227_, size_t v_i_2228_, size_t v_stop_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_usize_dec_eq(v_i_2228_, v_stop_2229_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = 1;
v___x_2237_ = lean_array_uget_borrowed(v_as_2227_, v_i_2228_);
lean_inc_ref(v_eq_2225_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v_a_2226_);
lean_inc(v___x_2237_);
v___x_2238_ = lean_apply_7(v_eq_2225_, v___x_2237_, v_a_2226_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, lean_box(0));
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2251_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_unbox(v_a_2239_);
lean_dec(v_a_2239_);
if (v___x_2243_ == 0)
{
size_t v___x_2244_; size_t v___x_2245_; 
lean_del_object(v___x_2241_);
v___x_2244_ = ((size_t)1ULL);
v___x_2245_ = lean_usize_add(v_i_2228_, v___x_2244_);
v_i_2228_ = v___x_2245_;
goto _start;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec(v_a_2226_);
lean_dec_ref(v_eq_2225_);
v___x_2247_ = lean_box(v___x_2236_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2247_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
else
{
lean_dec(v_a_2226_);
lean_dec_ref(v_eq_2225_);
return v___x_2238_;
}
}
else
{
uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec(v_a_2226_);
lean_dec_ref(v_eq_2225_);
v___x_2252_ = 0;
v___x_2253_ = lean_box(v___x_2252_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2255_, lean_object* v_a_2256_, lean_object* v_as_2257_, lean_object* v_i_2258_, lean_object* v_stop_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
size_t v_i_boxed_2265_; size_t v_stop_boxed_2266_; lean_object* v_res_2267_; 
v_i_boxed_2265_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_stop_boxed_2266_ = lean_unbox_usize(v_stop_2259_);
lean_dec(v_stop_2259_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2255_, v_a_2256_, v_as_2257_, v_i_boxed_2265_, v_stop_boxed_2266_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_as_2257_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2268_, lean_object* v_a_2269_, uint8_t v_____do__lift_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
if (v_____do__lift_2270_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_array_push(v_b_2268_, v_a_2269_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v_a_2269_);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_b_2268_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2281_, lean_object* v_a_2282_, lean_object* v_____do__lift_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v_____do__lift_1276__boxed_2289_; lean_object* v_res_2290_; 
v_____do__lift_1276__boxed_2289_ = lean_unbox(v_____do__lift_2283_);
v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2281_, v_a_2282_, v_____do__lift_1276__boxed_2289_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2291_, lean_object* v_as_2292_, size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_b_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___y_2302_; uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
lean_dec_ref(v_eq_2291_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_b_2295_);
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; lean_object* v_a_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v_a_2327_ = lean_array_uget_borrowed(v_as_2292_, v_i_2294_);
v___x_2328_ = lean_array_get_size(v_b_2295_);
v___x_2329_ = lean_nat_dec_lt(v___x_2326_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_a_2327_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2295_, v_a_2327_, v___x_2329_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
v___y_2302_ = v___x_2330_;
goto v___jp_2301_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2328_);
lean_inc(v_a_2327_);
lean_inc_ref(v_eq_2291_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2291_, v_a_2327_, v_b_2295_, v___x_2331_, v___x_2332_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = lean_unbox(v_a_2334_);
lean_dec(v_a_2334_);
lean_inc(v_a_2327_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2295_, v_a_2327_, v___x_2335_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
v___y_2302_ = v___x_2336_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_b_2295_);
lean_dec_ref(v_eq_2291_);
v_a_2337_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2333_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2333_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
v___jp_2301_:
{
if (lean_obj_tag(v___y_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2315_; 
v_a_2303_ = lean_ctor_get(v___y_2302_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___y_2302_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2305_ = v___y_2302_;
v_isShared_2306_ = v_isSharedCheck_2315_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___y_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2315_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
if (lean_obj_tag(v_a_2303_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; 
lean_dec_ref(v_eq_2291_);
v_a_2307_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v_a_2303_, 1);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_a_2307_);
v___x_2309_ = v___x_2305_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
else
{
lean_object* v_a_2311_; size_t v___x_2312_; size_t v___x_2313_; 
lean_del_object(v___x_2305_);
v_a_2311_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v_a_2303_, 1);
v___x_2312_ = ((size_t)1ULL);
v___x_2313_ = lean_usize_add(v_i_2294_, v___x_2312_);
v_i_2294_ = v___x_2313_;
v_b_2295_ = v_a_2311_;
goto _start;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_eq_2291_);
v_a_2316_ = lean_ctor_get(v___y_2302_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___y_2302_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___y_2302_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___y_2302_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2345_, lean_object* v_as_2346_, lean_object* v_sz_2347_, lean_object* v_i_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
size_t v_sz_boxed_2355_; size_t v_i_boxed_2356_; lean_object* v_res_2357_; 
v_sz_boxed_2355_ = lean_unbox_usize(v_sz_2347_);
lean_dec(v_sz_2347_);
v_i_boxed_2356_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2345_, v_as_2346_, v_sz_boxed_2355_, v_i_boxed_2356_, v_b_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v_as_2346_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2358_, lean_object* v_xs_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_ret_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v_ret_2365_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2366_ = lean_array_size(v_xs_2359_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2358_, v_xs_2359_, v_sz_2366_, v___x_2367_, v_ret_2365_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2369_, lean_object* v_xs_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2369_, v_xs_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_xs_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2384_; size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2384_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2385_ = lean_array_size(v_recArgInfos_2378_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2385_, v___x_2386_, v_recArgInfos_2378_);
v___x_2388_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2384_, v___x_2387_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec_ref(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2396_, lean_object* v_eq_2397_, lean_object* v_xs_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2397_, v_xs_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_eq_2406_, lean_object* v_xs_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2405_, v_eq_2406_, v_xs_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_xs_2407_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2414_, lean_object* v_eq_2415_, lean_object* v_a_2416_, lean_object* v_as_2417_, size_t v_i_2418_, size_t v_stop_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2415_, v_a_2416_, v_as_2417_, v_i_2418_, v_stop_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_eq_2427_, lean_object* v_a_2428_, lean_object* v_as_2429_, lean_object* v_i_2430_, lean_object* v_stop_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
size_t v_i_boxed_2437_; size_t v_stop_boxed_2438_; lean_object* v_res_2439_; 
v_i_boxed_2437_ = lean_unbox_usize(v_i_2430_);
lean_dec(v_i_2430_);
v_stop_boxed_2438_ = lean_unbox_usize(v_stop_2431_);
lean_dec(v_stop_2431_);
v_res_2439_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2426_, v_eq_2427_, v_a_2428_, v_as_2429_, v_i_boxed_2437_, v_stop_boxed_2438_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec_ref(v_as_2429_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2440_, lean_object* v_eq_2441_, lean_object* v_as_2442_, size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2441_, v_as_2442_, v_sz_2443_, v_i_2444_, v_b_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_eq_2453_, lean_object* v_as_2454_, lean_object* v_sz_2455_, lean_object* v_i_2456_, lean_object* v_b_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
size_t v_sz_boxed_2463_; size_t v_i_boxed_2464_; lean_object* v_res_2465_; 
v_sz_boxed_2463_ = lean_unbox_usize(v_sz_2455_);
lean_dec(v_sz_2455_);
v_i_boxed_2464_ = lean_unbox_usize(v_i_2456_);
lean_dec(v_i_2456_);
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2452_, v_eq_2453_, v_as_2454_, v_sz_boxed_2463_, v_i_boxed_2464_, v_b_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec_ref(v_as_2454_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2466_, lean_object* v___y_2467_){
_start:
{
uint8_t v___x_2469_; 
v___x_2469_ = l_Lean_Expr_hasMVar(v_e_2466_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_e_2466_);
return v___x_2470_;
}
else
{
lean_object* v___x_2471_; lean_object* v_mctx_2472_; lean_object* v___x_2473_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; lean_object* v_cache_2477_; lean_object* v_zetaDeltaFVarIds_2478_; lean_object* v_postponed_2479_; lean_object* v_diag_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2489_; 
v___x_2471_ = lean_st_ref_get(v___y_2467_);
v_mctx_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc_ref(v_mctx_2472_);
lean_dec(v___x_2471_);
v___x_2473_ = l_Lean_instantiateMVarsCore(v_mctx_2472_, v_e_2466_);
v_fst_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_fst_2474_);
v_snd_2475_ = lean_ctor_get(v___x_2473_, 1);
lean_inc(v_snd_2475_);
lean_dec_ref(v___x_2473_);
v___x_2476_ = lean_st_ref_take(v___y_2467_);
v_cache_2477_ = lean_ctor_get(v___x_2476_, 1);
v_zetaDeltaFVarIds_2478_ = lean_ctor_get(v___x_2476_, 2);
v_postponed_2479_ = lean_ctor_get(v___x_2476_, 3);
v_diag_2480_ = lean_ctor_get(v___x_2476_, 4);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2490_);
v___x_2482_ = v___x_2476_;
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_diag_2480_);
lean_inc(v_postponed_2479_);
lean_inc(v_zetaDeltaFVarIds_2478_);
lean_inc(v_cache_2477_);
lean_dec(v___x_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v_snd_2475_);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_snd_2475_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_cache_2477_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_zetaDeltaFVarIds_2478_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_postponed_2479_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_diag_2480_);
v___x_2485_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_st_ref_put(v___y_2467_, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_fst_2474_);
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2491_, v___y_2492_);
lean_dec(v___y_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2495_, v___y_2497_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2511_ = lean_unsigned_to_nat(109u);
v___x_2512_ = lean_unsigned_to_nat(216u);
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2515_ = l_mkPanicMessageWithDecl(v___x_2514_, v___x_2513_, v___x_2512_, v___x_2511_, v___x_2510_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2520_ == 0)
{
return v_bs_2519_;
}
else
{
lean_object* v_v_2521_; lean_object* v___x_2522_; lean_object* v_bs_x27_2523_; lean_object* v___y_2525_; lean_object* v___x_2530_; 
v_v_2521_ = lean_array_uget(v_bs_2519_, v_i_2518_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v_bs_x27_2523_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2522_);
v___x_2530_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2516_, v_v_2521_);
lean_dec(v_v_2521_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2532_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2531_);
v___y_2525_ = v___x_2532_;
goto v___jp_2524_;
}
else
{
lean_object* v_val_2533_; 
v_val_2533_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v___x_2530_, 1);
v___y_2525_ = v_val_2533_;
goto v___jp_2524_;
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2518_, v___x_2526_);
v___x_2528_ = lean_array_uset(v_bs_x27_2523_, v_i_2518_, v___y_2525_);
v_i_2518_ = v___x_2527_;
v_bs_2519_ = v___x_2528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2534_, lean_object* v_sz_2535_, lean_object* v_i_2536_, lean_object* v_bs_2537_){
_start:
{
size_t v_sz_boxed_2538_; size_t v_i_boxed_2539_; lean_object* v_res_2540_; 
v_sz_boxed_2538_ = lean_unbox_usize(v_sz_2535_);
lean_dec(v_sz_2535_);
v_i_boxed_2539_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_res_2540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2534_, v_sz_boxed_2538_, v_i_boxed_2539_, v_bs_2537_);
lean_dec_ref(v___x_2534_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2541_, size_t v_i_2542_, lean_object* v_bs_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_usize_dec_lt(v_i_2542_, v_sz_2541_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_bs_2543_);
return v___x_2550_;
}
else
{
lean_object* v_v_2551_; lean_object* v___x_2552_; lean_object* v_bs_x27_2553_; lean_object* v___x_2554_; 
v_v_2551_ = lean_array_uget(v_bs_2543_, v_i_2542_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v_bs_x27_2553_ = lean_array_uset(v_bs_2543_, v_i_2542_, v___x_2552_);
v___x_2554_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2551_, v___y_2545_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2542_, v___x_2556_);
v___x_2558_ = lean_array_uset(v_bs_x27_2553_, v_i_2542_, v_a_2555_);
v_i_2542_ = v___x_2557_;
v_bs_2543_ = v___x_2558_;
goto _start;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref(v_bs_x27_2553_);
v_a_2560_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2554_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2554_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2568_, lean_object* v_i_2569_, lean_object* v_bs_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
size_t v_sz_boxed_2576_; size_t v_i_boxed_2577_; lean_object* v_res_2578_; 
v_sz_boxed_2576_ = lean_unbox_usize(v_sz_2568_);
lean_dec(v_sz_2568_);
v_i_boxed_2577_ = lean_unbox_usize(v_i_2569_);
lean_dec(v_i_2569_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2576_, v_i_boxed_2577_, v_bs_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
return v_res_2578_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2579_, lean_object* v___x_2580_, lean_object* v_as_2581_, size_t v_i_2582_, size_t v_stop_2583_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_usize_dec_eq(v_i_2582_, v_stop_2583_);
if (v___x_2584_ == 0)
{
uint8_t v___x_2585_; uint8_t v___y_2587_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2585_ = 1;
v___x_2591_ = lean_array_uget_borrowed(v_as_2581_, v_i_2582_);
v___x_2592_ = l_Lean_Expr_isFVar(v___x_2591_);
if (v___x_2592_ == 0)
{
v___y_2587_ = v_a_2579_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = lean_nat_dec_eq(v___x_2580_, v___x_2593_);
v___y_2587_ = v___x_2594_;
goto v___jp_2586_;
}
v___jp_2586_:
{
if (v___y_2587_ == 0)
{
size_t v___x_2588_; size_t v___x_2589_; 
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2582_, v___x_2588_);
v_i_2582_ = v___x_2589_;
goto _start;
}
else
{
return v___x_2585_;
}
}
}
else
{
uint8_t v___x_2595_; 
v___x_2595_ = 0;
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2596_, lean_object* v___x_2597_, lean_object* v_as_2598_, lean_object* v_i_2599_, lean_object* v_stop_2600_){
_start:
{
uint8_t v_a_7784__boxed_2601_; size_t v_i_boxed_2602_; size_t v_stop_boxed_2603_; uint8_t v_res_2604_; lean_object* v_r_2605_; 
v_a_7784__boxed_2601_ = lean_unbox(v_a_2596_);
v_i_boxed_2602_ = lean_unbox_usize(v_i_2599_);
lean_dec(v_i_2599_);
v_stop_boxed_2603_ = lean_unbox_usize(v_stop_2600_);
lean_dec(v_stop_2600_);
v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7784__boxed_2601_, v___x_2597_, v_as_2598_, v_i_boxed_2602_, v_stop_boxed_2603_);
lean_dec_ref(v_as_2598_);
lean_dec(v___x_2597_);
v_r_2605_ = lean_box(v_res_2604_);
return v_r_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2606_, lean_object* v_ys_2607_, lean_object* v___x_2608_, lean_object* v_recArgInfo_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v_group_2612_, lean_object* v___x_2613_, lean_object* v_as_2614_, size_t v_sz_2615_, size_t v_i_2616_, lean_object* v_b_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_a_2624_; uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_lt(v_i_2616_, v_sz_2615_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_b_2617_);
return v___x_2629_;
}
else
{
lean_object* v_snd_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2786_; 
v_snd_2630_ = lean_ctor_get(v_b_2617_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_b_2617_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v_b_2617_, 0);
lean_dec(v_unused_2787_);
v___x_2632_ = v_b_2617_;
v_isShared_2633_ = v_isSharedCheck_2786_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_snd_2630_);
lean_dec(v_b_2617_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2786_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_next_2634_; lean_object* v_upperBound_2635_; lean_object* v___x_2636_; 
v_next_2634_ = lean_ctor_get(v_snd_2630_, 0);
lean_inc(v_next_2634_);
v_upperBound_2635_ = lean_ctor_get(v_snd_2630_, 1);
v___x_2636_ = lean_box(0);
if (lean_obj_tag(v_next_2634_) == 0)
{
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
goto v___jp_2637_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2785_; 
v_val_2642_ = lean_ctor_get(v_next_2634_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_next_2634_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2644_ = v_next_2634_;
v_isShared_2645_ = v_isSharedCheck_2785_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v_next_2634_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2785_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_lt(v_val_2642_, v_upperBound_2635_);
if (v___x_2646_ == 0)
{
lean_del_object(v___x_2644_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
goto v___jp_2637_;
}
else
{
lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_upperBound_2635_);
lean_del_object(v___x_2632_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_snd_2630_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; 
v_unused_2783_ = lean_ctor_get(v_snd_2630_, 1);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_snd_2630_, 0);
lean_dec(v_unused_2784_);
v___x_2648_ = v_snd_2630_;
v_isShared_2649_ = v_isSharedCheck_2782_;
goto v_resetjp_2647_;
}
else
{
lean_dec(v_snd_2630_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2782_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v_a_2650_ = lean_array_uget_borrowed(v_as_2614_, v_i_2616_);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_nat_add(v_val_2642_, v___x_2651_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2652_);
v___x_2654_ = v___x_2644_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2654_);
v___x_2656_ = v___x_2648_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_upperBound_2635_);
v___x_2656_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; 
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc_ref(v___x_2606_);
v___x_2657_ = lean_infer_type(v___x_2606_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Meta_whnfD(v_a_2658_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = 0;
lean_inc(v_a_2650_);
v___x_2662_ = l_Lean_Meta_forallMetaTelescope(v_a_2650_, v___x_2661_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_snd_2664_; lean_object* v_fst_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2755_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v_snd_2664_ = lean_ctor_get(v_a_2663_, 1);
v_fst_2665_ = lean_ctor_get(v_a_2663_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2667_ = v_a_2663_;
v_isShared_2668_ = v_isSharedCheck_2755_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_snd_2664_);
lean_inc(v_fst_2665_);
lean_dec(v_a_2663_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2755_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_snd_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2753_; 
v_snd_2669_ = lean_ctor_get(v_snd_2664_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_snd_2664_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v_snd_2664_, 0);
lean_dec(v_unused_2754_);
v___x_2671_ = v_snd_2664_;
v_isShared_2672_ = v_isSharedCheck_2753_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_snd_2669_);
lean_dec(v_snd_2664_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2753_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2669_, v_a_2660_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; uint8_t v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_unbox(v_a_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2677_; 
lean_dec(v_a_2674_);
lean_del_object(v___x_2667_);
lean_dec(v_fst_2665_);
lean_dec(v_val_2642_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2656_);
lean_ctor_set(v___x_2671_, 0, v___x_2636_);
v___x_2677_ = v___x_2671_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2656_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
v_a_2624_ = v___x_2677_;
goto v___jp_2623_;
}
}
else
{
size_t v_sz_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v_sz_2679_ = lean_array_size(v_fst_2665_);
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2679_, v___x_2680_, v_fst_2665_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_array_get_size(v_a_2682_);
v___x_2730_ = lean_nat_dec_lt(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_dec(v_a_2674_);
lean_del_object(v___x_2667_);
goto v___jp_2683_;
}
else
{
if (v___x_2730_ == 0)
{
lean_dec(v_a_2674_);
lean_del_object(v___x_2667_);
goto v___jp_2683_;
}
else
{
size_t v___x_2731_; uint8_t v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = lean_usize_of_nat(v___x_2729_);
v___x_2732_ = lean_unbox(v_a_2674_);
lean_dec(v_a_2674_);
v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2732_, v___x_2613_, v_a_2682_, v___x_2680_, v___x_2731_);
if (v___x_2733_ == 0)
{
lean_del_object(v___x_2667_);
goto v___jp_2683_;
}
else
{
lean_object* v___x_2735_; 
lean_dec(v_a_2682_);
lean_del_object(v___x_2671_);
lean_dec(v_val_2642_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2656_);
lean_ctor_set(v___x_2667_, 0, v___x_2636_);
v___x_2735_ = v___x_2667_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2656_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v_a_2624_ = v___x_2735_;
goto v___jp_2623_;
}
}
}
}
v___jp_2683_:
{
uint8_t v___x_2684_; 
v___x_2684_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2682_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2686_; 
lean_dec(v_a_2682_);
lean_dec(v_val_2642_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2656_);
lean_ctor_set(v___x_2671_, 0, v___x_2636_);
v___x_2686_ = v___x_2671_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2656_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
v_a_2624_ = v___x_2686_;
goto v___jp_2623_;
}
}
else
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2607_, v_a_2682_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2719_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2719_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2719_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
if (lean_obj_tag(v_a_2689_) == 1)
{
lean_object* v___x_2694_; 
lean_dec_ref_known(v_a_2689_, 1);
lean_del_object(v___x_2691_);
lean_dec(v_a_2682_);
lean_dec(v_val_2642_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2656_);
lean_ctor_set(v___x_2671_, 0, v___x_2636_);
v___x_2694_ = v___x_2671_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2656_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v_a_2624_ = v___x_2694_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_fnName_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_a_2689_);
lean_dec_ref(v___x_2606_);
v_fnName_2696_ = lean_ctor_get(v_recArgInfo_2609_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_recArgInfo_2609_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; 
v_unused_2714_ = lean_ctor_get(v_recArgInfo_2609_, 5);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_recArgInfo_2609_, 4);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_recArgInfo_2609_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_recArgInfo_2609_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2609_, 1);
lean_dec(v_unused_2718_);
v___x_2698_ = v_recArgInfo_2609_;
v_isShared_2699_ = v_isSharedCheck_2713_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_fnName_2696_);
lean_dec(v_recArgInfo_2609_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2713_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
size_t v_sz_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v_sz_2700_ = lean_array_size(v_a_2682_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2608_, v_sz_2700_, v___x_2680_, v_a_2682_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 5, v_val_2642_);
lean_ctor_set(v___x_2698_, 4, v_group_2612_);
lean_ctor_set(v___x_2698_, 3, v___x_2701_);
lean_ctor_set(v___x_2698_, 2, v___x_2611_);
lean_ctor_set(v___x_2698_, 1, v___x_2610_);
v___x_2703_ = v___x_2698_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_fnName_2696_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v_group_2612_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_val_2642_);
v___x_2703_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2656_);
lean_ctor_set(v___x_2671_, 0, v___x_2705_);
v___x_2707_ = v___x_2671_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2656_);
v___x_2707_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2707_);
v___x_2709_ = v___x_2691_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2682_);
lean_del_object(v___x_2671_);
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2720_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2688_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2688_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_a_2674_);
lean_del_object(v___x_2671_);
lean_del_object(v___x_2667_);
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2737_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2681_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2681_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_del_object(v___x_2671_);
lean_del_object(v___x_2667_);
lean_dec(v_fst_2665_);
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2745_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2673_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2673_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_a_2660_);
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2756_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2662_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2662_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2764_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2659_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2659_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v___x_2656_);
lean_dec(v_val_2642_);
lean_dec_ref(v_group_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_recArgInfo_2609_);
lean_dec_ref(v___x_2606_);
v_a_2772_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2657_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2657_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2639_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___x_2636_);
v___x_2639_ = v___x_2632_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2630_);
v___x_2639_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
}
}
v___jp_2623_:
{
size_t v___x_2625_; size_t v___x_2626_; 
v___x_2625_ = ((size_t)1ULL);
v___x_2626_ = lean_usize_add(v_i_2616_, v___x_2625_);
v_i_2616_ = v___x_2626_;
v_b_2617_ = v_a_2624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2788_ = _args[0];
lean_object* v_ys_2789_ = _args[1];
lean_object* v___x_2790_ = _args[2];
lean_object* v_recArgInfo_2791_ = _args[3];
lean_object* v___x_2792_ = _args[4];
lean_object* v___x_2793_ = _args[5];
lean_object* v_group_2794_ = _args[6];
lean_object* v___x_2795_ = _args[7];
lean_object* v_as_2796_ = _args[8];
lean_object* v_sz_2797_ = _args[9];
lean_object* v_i_2798_ = _args[10];
lean_object* v_b_2799_ = _args[11];
lean_object* v___y_2800_ = _args[12];
lean_object* v___y_2801_ = _args[13];
lean_object* v___y_2802_ = _args[14];
lean_object* v___y_2803_ = _args[15];
lean_object* v___y_2804_ = _args[16];
_start:
{
size_t v_sz_boxed_2805_; size_t v_i_boxed_2806_; lean_object* v_res_2807_; 
v_sz_boxed_2805_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2806_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2788_, v_ys_2789_, v___x_2790_, v_recArgInfo_2791_, v___x_2792_, v___x_2793_, v_group_2794_, v___x_2795_, v_as_2796_, v_sz_boxed_2805_, v_i_boxed_2806_, v_b_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v_as_2796_);
lean_dec(v___x_2795_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_ys_2789_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_ys_2810_, lean_object* v___x_2811_, lean_object* v_recArgInfo_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_group_2815_, lean_object* v_as_2816_, size_t v_sz_2817_, size_t v_i_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_a_2826_; uint8_t v___x_2830_; 
v___x_2830_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_b_2819_);
return v___x_2831_;
}
else
{
lean_object* v_snd_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2988_; 
v_snd_2832_ = lean_ctor_get(v_b_2819_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_b_2819_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v_b_2819_, 0);
lean_dec(v_unused_2989_);
v___x_2834_ = v_b_2819_;
v_isShared_2835_ = v_isSharedCheck_2988_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snd_2832_);
lean_dec(v_b_2819_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2988_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_next_2836_; lean_object* v_upperBound_2837_; lean_object* v___x_2838_; 
v_next_2836_ = lean_ctor_get(v_snd_2832_, 0);
lean_inc(v_next_2836_);
v_upperBound_2837_ = lean_ctor_get(v_snd_2832_, 1);
v___x_2838_ = lean_box(0);
if (lean_obj_tag(v_next_2836_) == 0)
{
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
goto v___jp_2839_;
}
else
{
lean_object* v_val_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2987_; 
v_val_2844_ = lean_ctor_get(v_next_2836_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_next_2836_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2846_ = v_next_2836_;
v_isShared_2847_ = v_isSharedCheck_2987_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_val_2844_);
lean_dec(v_next_2836_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2987_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_nat_dec_lt(v_val_2844_, v_upperBound_2837_);
if (v___x_2848_ == 0)
{
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
goto v___jp_2839_;
}
else
{
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2984_; 
lean_inc(v_upperBound_2837_);
lean_del_object(v___x_2834_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_snd_2832_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; 
v_unused_2985_ = lean_ctor_get(v_snd_2832_, 1);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_snd_2832_, 0);
lean_dec(v_unused_2986_);
v___x_2850_ = v_snd_2832_;
v_isShared_2851_ = v_isSharedCheck_2984_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v_snd_2832_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2984_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v_a_2852_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
v___x_2853_ = lean_unsigned_to_nat(1u);
v___x_2854_ = lean_nat_add(v_val_2844_, v___x_2853_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2854_);
v___x_2856_ = v___x_2846_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2856_);
v___x_2858_ = v___x_2850_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_upperBound_2837_);
v___x_2858_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; 
lean_inc(v___y_2823_);
lean_inc_ref(v___y_2822_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc_ref(v___x_2808_);
v___x_2859_ = lean_infer_type(v___x_2808_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Meta_whnfD(v_a_2860_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = 0;
lean_inc(v_a_2852_);
v___x_2864_ = l_Lean_Meta_forallMetaTelescope(v_a_2852_, v___x_2863_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v_snd_2866_; lean_object* v_fst_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2957_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v_snd_2866_ = lean_ctor_get(v_a_2865_, 1);
v_fst_2867_ = lean_ctor_get(v_a_2865_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_a_2865_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2869_ = v_a_2865_;
v_isShared_2870_ = v_isSharedCheck_2957_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_snd_2866_);
lean_inc(v_fst_2867_);
lean_dec(v_a_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2957_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_snd_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2955_; 
v_snd_2871_ = lean_ctor_get(v_snd_2866_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_snd_2866_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v_snd_2866_, 0);
lean_dec(v_unused_2956_);
v___x_2873_ = v_snd_2866_;
v_isShared_2874_ = v_isSharedCheck_2955_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_snd_2871_);
lean_dec(v_snd_2866_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2955_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2871_, v_a_2862_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; uint8_t v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = lean_unbox(v_a_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_a_2876_);
lean_del_object(v___x_2869_);
lean_dec(v_fst_2867_);
lean_dec(v_val_2844_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2858_);
lean_ctor_set(v___x_2873_, 0, v___x_2838_);
v___x_2879_ = v___x_2873_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2858_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
v_a_2826_ = v___x_2879_;
goto v___jp_2825_;
}
}
else
{
size_t v_sz_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v_sz_2881_ = lean_array_size(v_fst_2867_);
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2881_, v___x_2882_, v_fst_2867_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_array_get_size(v_a_2884_);
v___x_2932_ = lean_nat_dec_lt(v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_dec(v_a_2876_);
lean_del_object(v___x_2869_);
goto v___jp_2885_;
}
else
{
if (v___x_2932_ == 0)
{
lean_dec(v_a_2876_);
lean_del_object(v___x_2869_);
goto v___jp_2885_;
}
else
{
size_t v___x_2933_; uint8_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2933_ = lean_usize_of_nat(v___x_2931_);
v___x_2934_ = lean_unbox(v_a_2876_);
lean_dec(v_a_2876_);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2934_, v___x_2809_, v_a_2884_, v___x_2882_, v___x_2933_);
if (v___x_2935_ == 0)
{
lean_del_object(v___x_2869_);
goto v___jp_2885_;
}
else
{
lean_object* v___x_2937_; 
lean_dec(v_a_2884_);
lean_del_object(v___x_2873_);
lean_dec(v_val_2844_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v___x_2858_);
lean_ctor_set(v___x_2869_, 0, v___x_2838_);
v___x_2937_ = v___x_2869_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2858_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
v_a_2826_ = v___x_2937_;
goto v___jp_2825_;
}
}
}
}
v___jp_2885_:
{
uint8_t v___x_2886_; 
v___x_2886_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2884_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2888_; 
lean_dec(v_a_2884_);
lean_dec(v_val_2844_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2858_);
lean_ctor_set(v___x_2873_, 0, v___x_2838_);
v___x_2888_ = v___x_2873_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2858_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
v_a_2826_ = v___x_2888_;
goto v___jp_2825_;
}
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2810_, v_a_2884_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2921_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2921_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
if (lean_obj_tag(v_a_2891_) == 1)
{
lean_object* v___x_2896_; 
lean_dec_ref_known(v_a_2891_, 1);
lean_del_object(v___x_2893_);
lean_dec(v_a_2884_);
lean_dec(v_val_2844_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2858_);
lean_ctor_set(v___x_2873_, 0, v___x_2838_);
v___x_2896_ = v___x_2873_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2858_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
v_a_2826_ = v___x_2896_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_fnName_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_a_2891_);
lean_dec_ref(v___x_2808_);
v_fnName_2898_ = lean_ctor_get(v_recArgInfo_2812_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_recArgInfo_2812_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; lean_object* v_unused_2919_; lean_object* v_unused_2920_; 
v_unused_2916_ = lean_ctor_get(v_recArgInfo_2812_, 5);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_recArgInfo_2812_, 4);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_recArgInfo_2812_, 3);
lean_dec(v_unused_2918_);
v_unused_2919_ = lean_ctor_get(v_recArgInfo_2812_, 2);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_recArgInfo_2812_, 1);
lean_dec(v_unused_2920_);
v___x_2900_ = v_recArgInfo_2812_;
v_isShared_2901_ = v_isSharedCheck_2915_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_fnName_2898_);
lean_dec(v_recArgInfo_2812_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2915_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
size_t v_sz_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v_sz_2902_ = lean_array_size(v_a_2884_);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2811_, v_sz_2902_, v___x_2882_, v_a_2884_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 5, v_val_2844_);
lean_ctor_set(v___x_2900_, 4, v_group_2815_);
lean_ctor_set(v___x_2900_, 3, v___x_2903_);
lean_ctor_set(v___x_2900_, 2, v___x_2814_);
lean_ctor_set(v___x_2900_, 1, v___x_2813_);
v___x_2905_ = v___x_2900_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_fnName_2898_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_group_2815_);
lean_ctor_set(v_reuseFailAlloc_2914_, 5, v_val_2844_);
v___x_2905_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2858_);
lean_ctor_set(v___x_2873_, 0, v___x_2907_);
v___x_2909_ = v___x_2873_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2858_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2909_);
v___x_2911_ = v___x_2893_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2884_);
lean_del_object(v___x_2873_);
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2922_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2890_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2890_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_a_2876_);
lean_del_object(v___x_2873_);
lean_del_object(v___x_2869_);
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2939_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2883_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2883_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_del_object(v___x_2873_);
lean_del_object(v___x_2869_);
lean_dec(v_fst_2867_);
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2947_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2875_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2875_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_a_2862_);
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2958_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2864_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2864_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2966_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2861_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2861_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v___x_2858_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2974_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2859_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2859_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
}
}
}
v___jp_2839_:
{
lean_object* v___x_2841_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2838_);
v___x_2841_ = v___x_2834_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_snd_2832_);
v___x_2841_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
}
}
}
v___jp_2825_:
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2818_, v___x_2827_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2808_, v_ys_2810_, v___x_2811_, v_recArgInfo_2812_, v___x_2813_, v___x_2814_, v_group_2815_, v___x_2809_, v_as_2816_, v_sz_2817_, v___x_2828_, v_a_2826_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2990_ = _args[0];
lean_object* v___x_2991_ = _args[1];
lean_object* v_ys_2992_ = _args[2];
lean_object* v___x_2993_ = _args[3];
lean_object* v_recArgInfo_2994_ = _args[4];
lean_object* v___x_2995_ = _args[5];
lean_object* v___x_2996_ = _args[6];
lean_object* v_group_2997_ = _args[7];
lean_object* v_as_2998_ = _args[8];
lean_object* v_sz_2999_ = _args[9];
lean_object* v_i_3000_ = _args[10];
lean_object* v_b_3001_ = _args[11];
lean_object* v___y_3002_ = _args[12];
lean_object* v___y_3003_ = _args[13];
lean_object* v___y_3004_ = _args[14];
lean_object* v___y_3005_ = _args[15];
lean_object* v___y_3006_ = _args[16];
_start:
{
size_t v_sz_boxed_3007_; size_t v_i_boxed_3008_; lean_object* v_res_3009_; 
v_sz_boxed_3007_ = lean_unbox_usize(v_sz_2999_);
lean_dec(v_sz_2999_);
v_i_boxed_3008_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2990_, v___x_2991_, v_ys_2992_, v___x_2993_, v_recArgInfo_2994_, v___x_2995_, v___x_2996_, v_group_2997_, v_as_2998_, v_sz_boxed_3007_, v_i_boxed_3008_, v_b_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_as_2998_);
lean_dec_ref(v___x_2993_);
lean_dec_ref(v_ys_2992_);
lean_dec(v___x_2991_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3010_, lean_object* v_fixedParamPerm_3011_, lean_object* v_xs_3012_, lean_object* v___x_3013_, lean_object* v_recArgPos_3014_, lean_object* v_a_3015_, lean_object* v___x_3016_, lean_object* v___x_3017_, lean_object* v_ys_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_toIndGroupInfo_3025_; lean_object* v_all_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3064_; 
v_toIndGroupInfo_3025_ = lean_ctor_get(v_group_3010_, 0);
lean_inc_ref(v_toIndGroupInfo_3025_);
v_all_3026_ = lean_ctor_get(v_toIndGroupInfo_3025_, 0);
lean_inc_ref(v_ys_3018_);
lean_inc_ref(v_fixedParamPerm_3011_);
v___x_3027_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3011_, v_xs_3012_, v_ys_3018_);
v___x_3028_ = lean_array_get(v___x_3013_, v___x_3027_, v_recArgPos_3014_);
v___x_3029_ = lean_array_get_size(v_all_3026_);
v___x_3030_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3025_);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_toIndGroupInfo_3025_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; lean_object* v_unused_3066_; 
v_unused_3065_ = lean_ctor_get(v_toIndGroupInfo_3025_, 1);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v_toIndGroupInfo_3025_, 0);
lean_dec(v_unused_3066_);
v___x_3032_ = v_toIndGroupInfo_3025_;
v_isShared_3033_ = v_isSharedCheck_3064_;
goto v_resetjp_3031_;
}
else
{
lean_dec(v_toIndGroupInfo_3025_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3064_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3029_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3030_);
lean_ctor_set(v___x_3032_, 0, v___x_3034_);
v___x_3036_ = v___x_3032_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3030_);
v___x_3036_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; size_t v_sz_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3036_);
v_sz_3039_ = lean_array_size(v_a_3015_);
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3028_, v___x_3016_, v_ys_3018_, v___x_3027_, v___x_3017_, v_fixedParamPerm_3011_, v_recArgPos_3014_, v_group_3010_, v_a_3015_, v_sz_3039_, v___x_3040_, v___x_3038_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec_ref(v___x_3027_);
lean_dec_ref(v_ys_3018_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3054_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3054_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3054_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_fst_3046_; 
v_fst_3046_ = lean_ctor_get(v_a_3042_, 0);
lean_inc(v_fst_3046_);
lean_dec(v_a_3042_);
if (lean_obj_tag(v_fst_3046_) == 0)
{
lean_object* v___x_3048_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3037_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3037_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3052_; 
v_val_3050_ = lean_ctor_get(v_fst_3046_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v_fst_3046_, 1);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_val_3050_);
v___x_3052_ = v___x_3044_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_val_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3055_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3041_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3041_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3067_, lean_object* v_fixedParamPerm_3068_, lean_object* v_xs_3069_, lean_object* v___x_3070_, lean_object* v_recArgPos_3071_, lean_object* v_a_3072_, lean_object* v___x_3073_, lean_object* v___x_3074_, lean_object* v_ys_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3067_, v_fixedParamPerm_3068_, v_xs_3069_, v___x_3070_, v_recArgPos_3071_, v_a_3072_, v___x_3073_, v___x_3074_, v_ys_3075_, v_x_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v_x_3076_);
lean_dec(v___x_3073_);
lean_dec_ref(v_a_3072_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_xs_3069_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3083_, lean_object* v_a_3084_, lean_object* v_xs_3085_, lean_object* v_value_3086_, lean_object* v_as_3087_, size_t v_i_3088_, size_t v_stop_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_a_3097_; lean_object* v_val_3102_; uint8_t v___x_3104_; 
v___x_3104_ = lean_usize_dec_eq(v_i_3088_, v_stop_3089_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v_fixedParamPerm_3106_; lean_object* v_recArgPos_3107_; lean_object* v_indGroupInst_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3105_ = lean_array_uget_borrowed(v_as_3087_, v_i_3088_);
v_fixedParamPerm_3106_ = lean_ctor_get(v___x_3105_, 1);
v_recArgPos_3107_ = lean_ctor_get(v___x_3105_, 2);
v_indGroupInst_3108_ = lean_ctor_get(v___x_3105_, 4);
v___x_3109_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_indGroupInst_3108_);
lean_inc_ref(v_group_3083_);
v___x_3110_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3083_, v_indGroupInst_3108_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; uint8_t v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = lean_unbox(v_a_3111_);
lean_dec(v_a_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3113_ = lean_array_get_size(v_a_3084_);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_nat_dec_eq(v___x_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___f_3116_; lean_object* v___x_3117_; 
lean_inc(v___x_3105_);
lean_inc_ref(v_a_3084_);
lean_inc(v_recArgPos_3107_);
lean_inc_ref(v_xs_3085_);
lean_inc_ref(v_fixedParamPerm_3106_);
lean_inc_ref(v_group_3083_);
v___f_3116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3116_, 0, v_group_3083_);
lean_closure_set(v___f_3116_, 1, v_fixedParamPerm_3106_);
lean_closure_set(v___f_3116_, 2, v_xs_3085_);
lean_closure_set(v___f_3116_, 3, v___x_3109_);
lean_closure_set(v___f_3116_, 4, v_recArgPos_3107_);
lean_closure_set(v___f_3116_, 5, v_a_3084_);
lean_closure_set(v___f_3116_, 6, v___x_3113_);
lean_closure_set(v___f_3116_, 7, v___x_3105_);
lean_inc_ref(v_value_3086_);
v___x_3117_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3086_, v___f_3116_, v___x_3115_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
if (lean_obj_tag(v_a_3118_) == 0)
{
v_a_3097_ = v_b_3090_;
goto v___jp_3096_;
}
else
{
lean_object* v_val_3119_; 
v_val_3119_ = lean_ctor_get(v_a_3118_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_a_3118_, 1);
v_val_3102_ = v_val_3119_;
goto v___jp_3101_;
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_b_3090_);
lean_dec_ref(v_value_3086_);
lean_dec_ref(v_xs_3085_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_group_3083_);
v_a_3120_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3117_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3117_);
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
else
{
v_a_3097_ = v_b_3090_;
goto v___jp_3096_;
}
}
else
{
lean_inc(v___x_3105_);
v_val_3102_ = v___x_3105_;
goto v___jp_3101_;
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_b_3090_);
lean_dec_ref(v_value_3086_);
lean_dec_ref(v_xs_3085_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_group_3083_);
v_a_3128_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3110_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3110_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v___x_3136_; 
lean_dec_ref(v_value_3086_);
lean_dec_ref(v_xs_3085_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_group_3083_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3090_);
return v___x_3136_;
}
v___jp_3096_:
{
size_t v___x_3098_; size_t v___x_3099_; 
v___x_3098_ = ((size_t)1ULL);
v___x_3099_ = lean_usize_add(v_i_3088_, v___x_3098_);
v_i_3088_ = v___x_3099_;
v_b_3090_ = v_a_3097_;
goto _start;
}
v___jp_3101_:
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_array_push(v_b_3090_, v_val_3102_);
v_a_3097_ = v___x_3103_;
goto v___jp_3096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3137_, lean_object* v_a_3138_, lean_object* v_xs_3139_, lean_object* v_value_3140_, lean_object* v_as_3141_, lean_object* v_i_3142_, lean_object* v_stop_3143_, lean_object* v_b_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
size_t v_i_boxed_3150_; size_t v_stop_boxed_3151_; lean_object* v_res_3152_; 
v_i_boxed_3150_ = lean_unbox_usize(v_i_3142_);
lean_dec(v_i_3142_);
v_stop_boxed_3151_ = lean_unbox_usize(v_stop_3143_);
lean_dec(v_stop_3143_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3137_, v_a_3138_, v_xs_3139_, v_value_3140_, v_as_3141_, v_i_boxed_3150_, v_stop_boxed_3151_, v_b_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec_ref(v_as_3141_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3153_, lean_object* v_a_3154_, lean_object* v_xs_3155_, lean_object* v_value_3156_, lean_object* v_as_3157_, lean_object* v_start_3158_, lean_object* v_stop_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3166_ = lean_nat_dec_lt(v_start_3158_, v_stop_3159_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
lean_dec_ref(v_value_3156_);
lean_dec_ref(v_xs_3155_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_group_3153_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_array_get_size(v_as_3157_);
v___x_3169_ = lean_nat_dec_le(v_stop_3159_, v___x_3168_);
if (v___x_3169_ == 0)
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_nat_dec_lt(v_start_3158_, v___x_3168_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
lean_dec_ref(v_value_3156_);
lean_dec_ref(v_xs_3155_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_group_3153_);
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3165_);
return v___x_3171_;
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_usize_of_nat(v_start_3158_);
v___x_3173_ = lean_usize_of_nat(v___x_3168_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3153_, v_a_3154_, v_xs_3155_, v_value_3156_, v_as_3157_, v___x_3172_, v___x_3173_, v___x_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3174_;
}
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_usize_of_nat(v_start_3158_);
v___x_3176_ = lean_usize_of_nat(v_stop_3159_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3153_, v_a_3154_, v_xs_3155_, v_value_3156_, v_as_3157_, v___x_3175_, v___x_3176_, v___x_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3178_, lean_object* v_a_3179_, lean_object* v_xs_3180_, lean_object* v_value_3181_, lean_object* v_as_3182_, lean_object* v_start_3183_, lean_object* v_stop_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3178_, v_a_3179_, v_xs_3180_, v_value_3181_, v_as_3182_, v_start_3183_, v_stop_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v_stop_3184_);
lean_dec(v_start_3183_);
lean_dec_ref(v_as_3182_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3191_, lean_object* v_xs_3192_, lean_object* v_value_3193_, lean_object* v_recArgInfos_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
lean_inc_ref(v_group_3191_);
v___x_3200_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3191_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_array_get_size(v_recArgInfos_3194_);
v___x_3204_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3191_, v_a_3201_, v_xs_3192_, v_value_3193_, v_recArgInfos_3194_, v___x_3202_, v___x_3203_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
return v___x_3204_;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_value_3193_);
lean_dec_ref(v_xs_3192_);
lean_dec_ref(v_group_3191_);
v_a_3205_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3200_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3200_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3213_, lean_object* v_xs_3214_, lean_object* v_value_3215_, lean_object* v_recArgInfos_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Elab_Structural_argsInGroup(v_group_3213_, v_xs_3214_, v_value_3215_, v_recArgInfos_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec_ref(v_recArgInfos_3216_);
return v_res_3222_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_unsigned_to_nat(10u);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3226_, lean_object* v_i_3227_, lean_object* v_acc_3228_){
_start:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = lean_array_get_size(v_xss_3226_);
v___x_3230_ = lean_nat_dec_lt(v_i_3227_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_mk_empty_array_with_capacity(v___x_3231_);
v___x_3233_ = lean_array_push(v___x_3232_, v_acc_3228_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3234_ = lean_array_fget_borrowed(v_xss_3226_, v_i_3227_);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3237_ = lean_array_get_size(v___x_3234_);
v___x_3238_ = lean_nat_dec_lt(v___x_3235_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_dec_ref(v_acc_3228_);
return v___x_3236_;
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((size_t)0ULL);
v___x_3240_ = lean_usize_of_nat(v___x_3237_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3227_, v_acc_3228_, v_xss_3226_, v___x_3234_, v___x_3239_, v___x_3240_, v___x_3236_);
return v___x_3241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3242_, lean_object* v_acc_3243_, lean_object* v_xss_3244_, lean_object* v_as_3245_, size_t v_i_3246_, size_t v_stop_3247_, lean_object* v_b_3248_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_usize_dec_eq(v_i_3246_, v_stop_3247_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; size_t v___x_3256_; size_t v___x_3257_; 
v___x_3250_ = lean_array_uget_borrowed(v_as_3245_, v_i_3246_);
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_add(v_i_3242_, v___x_3251_);
lean_inc(v___x_3250_);
lean_inc_ref(v_acc_3243_);
v___x_3253_ = lean_array_push(v_acc_3243_, v___x_3250_);
v___x_3254_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3244_, v___x_3252_, v___x_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = l_Array_append___redArg(v_b_3248_, v___x_3254_);
lean_dec_ref(v___x_3254_);
v___x_3256_ = ((size_t)1ULL);
v___x_3257_ = lean_usize_add(v_i_3246_, v___x_3256_);
v_i_3246_ = v___x_3257_;
v_b_3248_ = v___x_3255_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3243_);
return v_b_3248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3259_, lean_object* v_acc_3260_, lean_object* v_xss_3261_, lean_object* v_as_3262_, lean_object* v_i_3263_, lean_object* v_stop_3264_, lean_object* v_b_3265_){
_start:
{
size_t v_i_boxed_3266_; size_t v_stop_boxed_3267_; lean_object* v_res_3268_; 
v_i_boxed_3266_ = lean_unbox_usize(v_i_3263_);
lean_dec(v_i_3263_);
v_stop_boxed_3267_ = lean_unbox_usize(v_stop_3264_);
lean_dec(v_stop_3264_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3259_, v_acc_3260_, v_xss_3261_, v_as_3262_, v_i_boxed_3266_, v_stop_boxed_3267_, v_b_3265_);
lean_dec_ref(v_as_3262_);
lean_dec_ref(v_xss_3261_);
lean_dec(v_i_3259_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3269_, lean_object* v_i_3270_, lean_object* v_acc_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3269_, v_i_3270_, v_acc_3271_);
lean_dec(v_i_3270_);
lean_dec_ref(v_xss_3269_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3273_, lean_object* v_xss_3274_, lean_object* v_i_3275_, lean_object* v_acc_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3274_, v_i_3275_, v_acc_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3278_, lean_object* v_xss_3279_, lean_object* v_i_3280_, lean_object* v_acc_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3278_, v_xss_3279_, v_i_3280_, v_acc_3281_);
lean_dec(v_i_3280_);
lean_dec_ref(v_xss_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3283_, lean_object* v_i_3284_, lean_object* v_acc_3285_, lean_object* v_xss_3286_, lean_object* v_as_3287_, size_t v_i_3288_, size_t v_stop_3289_, lean_object* v_b_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3284_, v_acc_3285_, v_xss_3286_, v_as_3287_, v_i_3288_, v_stop_3289_, v_b_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_i_3293_, lean_object* v_acc_3294_, lean_object* v_xss_3295_, lean_object* v_as_3296_, lean_object* v_i_3297_, lean_object* v_stop_3298_, lean_object* v_b_3299_){
_start:
{
size_t v_i_boxed_3300_; size_t v_stop_boxed_3301_; lean_object* v_res_3302_; 
v_i_boxed_3300_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_stop_boxed_3301_ = lean_unbox_usize(v_stop_3298_);
lean_dec(v_stop_3298_);
v_res_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3292_, v_i_3293_, v_acc_3294_, v_xss_3295_, v_as_3296_, v_i_boxed_3300_, v_stop_boxed_3301_, v_b_3299_);
lean_dec_ref(v_as_3296_);
lean_dec_ref(v_xss_3295_);
lean_dec(v_i_3293_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3303_, size_t v_i_3304_, size_t v_stop_3305_, lean_object* v_b_3306_){
_start:
{
uint8_t v___x_3307_; 
v___x_3307_ = lean_usize_dec_eq(v_i_3304_, v_stop_3305_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; size_t v___x_3311_; size_t v___x_3312_; 
v___x_3308_ = lean_array_uget_borrowed(v_as_3303_, v_i_3304_);
v___x_3309_ = lean_array_get_size(v___x_3308_);
v___x_3310_ = lean_nat_mul(v_b_3306_, v___x_3309_);
lean_dec(v_b_3306_);
v___x_3311_ = ((size_t)1ULL);
v___x_3312_ = lean_usize_add(v_i_3304_, v___x_3311_);
v_i_3304_ = v___x_3312_;
v_b_3306_ = v___x_3310_;
goto _start;
}
else
{
return v_b_3306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3314_, lean_object* v_i_3315_, lean_object* v_stop_3316_, lean_object* v_b_3317_){
_start:
{
size_t v_i_boxed_3318_; size_t v_stop_boxed_3319_; lean_object* v_res_3320_; 
v_i_boxed_3318_ = lean_unbox_usize(v_i_3315_);
lean_dec(v_i_3315_);
v_stop_boxed_3319_ = lean_unbox_usize(v_stop_3316_);
lean_dec(v_stop_3316_);
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3314_, v_i_boxed_3318_, v_stop_boxed_3319_, v_b_3317_);
lean_dec_ref(v_as_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3321_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___y_3326_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3322_ = lean_unsigned_to_nat(10u);
v___x_3323_ = lean_unsigned_to_nat(1u);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_array_get_size(v_xss_3321_);
v___x_3333_ = lean_nat_dec_lt(v___x_3324_, v___x_3332_);
if (v___x_3333_ == 0)
{
v___y_3326_ = v___x_3323_;
goto v___jp_3325_;
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3332_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3321_, v___x_3334_, v___x_3335_, v___x_3323_);
v___y_3326_ = v___x_3336_;
goto v___jp_3325_;
}
v___jp_3325_:
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_nat_dec_lt(v___x_3322_, v___y_3326_);
lean_dec(v___y_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3329_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3321_, v___x_3324_, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_box(0);
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3337_);
lean_dec_ref(v_xss_3337_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3339_, lean_object* v_xss_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_xss_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3342_, v_xss_3343_);
lean_dec_ref(v_xss_3343_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3345_, lean_object* v_as_3346_, size_t v_i_3347_, size_t v_stop_3348_, lean_object* v_b_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3346_, v_i_3347_, v_stop_3348_, v_b_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3351_, lean_object* v_as_3352_, lean_object* v_i_3353_, lean_object* v_stop_3354_, lean_object* v_b_3355_){
_start:
{
size_t v_i_boxed_3356_; size_t v_stop_boxed_3357_; lean_object* v_res_3358_; 
v_i_boxed_3356_ = lean_unbox_usize(v_i_3353_);
lean_dec(v_i_3353_);
v_stop_boxed_3357_ = lean_unbox_usize(v_stop_3354_);
lean_dec(v_stop_3354_);
v_res_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3351_, v_as_3352_, v_i_boxed_3356_, v_stop_boxed_3357_, v_b_3355_);
lean_dec_ref(v_as_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3359_, size_t v_i_3360_, size_t v_stop_3361_, lean_object* v_b_3362_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_usize_dec_eq(v_i_3360_, v_stop_3361_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; size_t v___x_3366_; size_t v___x_3367_; 
v___x_3364_ = lean_array_uget_borrowed(v_as_3359_, v_i_3360_);
v___x_3365_ = l_Array_append___redArg(v_b_3362_, v___x_3364_);
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3360_, v___x_3366_);
v_i_3360_ = v___x_3367_;
v_b_3362_ = v___x_3365_;
goto _start;
}
else
{
return v_b_3362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3369_, lean_object* v_i_3370_, lean_object* v_stop_3371_, lean_object* v_b_3372_){
_start:
{
size_t v_i_boxed_3373_; size_t v_stop_boxed_3374_; lean_object* v_res_3375_; 
v_i_boxed_3373_ = lean_unbox_usize(v_i_3370_);
lean_dec(v_i_3370_);
v_stop_boxed_3374_ = lean_unbox_usize(v_stop_3371_);
lean_dec(v_stop_3371_);
v_res_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3369_, v_i_boxed_3373_, v_stop_boxed_3374_, v_b_3372_);
lean_dec_ref(v_as_3369_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
if (lean_obj_tag(v_a_3376_) == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l_List_reverse___redArg(v_a_3377_);
return v___x_3378_;
}
else
{
lean_object* v_head_3379_; lean_object* v_tail_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3390_; 
v_head_3379_ = lean_ctor_get(v_a_3376_, 0);
v_tail_3380_ = lean_ctor_get(v_a_3376_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3382_ = v_a_3376_;
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_tail_3380_);
lean_inc(v_head_3379_);
lean_dec(v_a_3376_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3384_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3379_);
v___x_3385_ = l_Lean_MessageData_ofFormat(v___x_3384_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v_a_3377_);
lean_ctor_set(v___x_3382_, 0, v___x_3385_);
v___x_3387_ = v___x_3382_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3377_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
v_a_3376_ = v_tail_3380_;
v_a_3377_ = v___x_3387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3391_, size_t v_i_3392_, lean_object* v_bs_3393_){
_start:
{
uint8_t v___x_3394_; 
v___x_3394_ = lean_usize_dec_lt(v_i_3392_, v_sz_3391_);
if (v___x_3394_ == 0)
{
return v_bs_3393_;
}
else
{
lean_object* v_v_3395_; lean_object* v___x_3396_; lean_object* v_bs_x27_3397_; lean_object* v___x_3398_; size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
v_v_3395_ = lean_array_uget(v_bs_3393_, v_i_3392_);
v___x_3396_ = lean_unsigned_to_nat(0u);
v_bs_x27_3397_ = lean_array_uset(v_bs_3393_, v_i_3392_, v___x_3396_);
v___x_3398_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3395_);
lean_dec(v_v_3395_);
v___x_3399_ = ((size_t)1ULL);
v___x_3400_ = lean_usize_add(v_i_3392_, v___x_3399_);
v___x_3401_ = lean_array_uset(v_bs_x27_3397_, v_i_3392_, v___x_3398_);
v_i_3392_ = v___x_3400_;
v_bs_3393_ = v___x_3401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3403_, lean_object* v_i_3404_, lean_object* v_bs_3405_){
_start:
{
size_t v_sz_boxed_3406_; size_t v_i_boxed_3407_; lean_object* v_res_3408_; 
v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3403_);
lean_dec(v_sz_3403_);
v_i_boxed_3407_ = lean_unbox_usize(v_i_3404_);
lean_dec(v_i_3404_);
v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3406_, v_i_boxed_3407_, v_bs_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3409_, lean_object* v_as_3410_, size_t v_sz_3411_, size_t v_i_3412_, lean_object* v_b_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_usize_dec_lt(v_i_3412_, v_sz_3411_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v_xs_3409_);
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v_b_3413_);
return v___x_3420_;
}
else
{
lean_object* v_snd_3421_; lean_object* v_snd_3422_; lean_object* v_snd_3423_; lean_object* v_snd_3424_; lean_object* v_fst_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3569_; 
v_snd_3421_ = lean_ctor_get(v_b_3413_, 1);
lean_inc(v_snd_3421_);
v_snd_3422_ = lean_ctor_get(v_snd_3421_, 1);
lean_inc(v_snd_3422_);
v_snd_3423_ = lean_ctor_get(v_snd_3422_, 1);
lean_inc(v_snd_3423_);
v_snd_3424_ = lean_ctor_get(v_snd_3423_, 1);
lean_inc(v_snd_3424_);
v_fst_3425_ = lean_ctor_get(v_b_3413_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_b_3413_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v_b_3413_, 1);
lean_dec(v_unused_3570_);
v___x_3427_ = v_b_3413_;
v_isShared_3428_ = v_isSharedCheck_3569_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_fst_3425_);
lean_dec(v_b_3413_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3569_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_fst_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3567_; 
v_fst_3429_ = lean_ctor_get(v_snd_3421_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_snd_3421_, 1);
lean_dec(v_unused_3568_);
v___x_3431_ = v_snd_3421_;
v_isShared_3432_ = v_isSharedCheck_3567_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_fst_3429_);
lean_dec(v_snd_3421_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3567_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_fst_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3565_; 
v_fst_3433_ = lean_ctor_get(v_snd_3422_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v_snd_3422_, 1);
lean_dec(v_unused_3566_);
v___x_3435_ = v_snd_3422_;
v_isShared_3436_ = v_isSharedCheck_3565_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_fst_3433_);
lean_dec(v_snd_3422_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3565_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_fst_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3563_; 
v_fst_3437_ = lean_ctor_get(v_snd_3423_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_snd_3423_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v_snd_3423_, 1);
lean_dec(v_unused_3564_);
v___x_3439_ = v_snd_3423_;
v_isShared_3440_ = v_isSharedCheck_3563_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_fst_3437_);
lean_dec(v_snd_3423_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3563_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_array_3441_; lean_object* v_start_3442_; lean_object* v_stop_3443_; uint8_t v___x_3444_; 
v_array_3441_ = lean_ctor_get(v_snd_3424_, 0);
v_start_3442_ = lean_ctor_get(v_snd_3424_, 1);
v_stop_3443_ = lean_ctor_get(v_snd_3424_, 2);
v___x_3444_ = lean_nat_dec_lt(v_start_3442_, v_stop_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref(v_xs_3409_);
if (v_isShared_3440_ == 0)
{
v___x_3446_ = v___x_3439_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_snd_3424_);
v___x_3446_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3446_);
v___x_3448_ = v___x_3435_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3448_);
v___x_3450_ = v___x_3431_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3429_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3450_);
v___x_3452_ = v___x_3427_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3425_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
}
}
else
{
lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3559_; 
lean_inc(v_stop_3443_);
lean_inc(v_start_3442_);
lean_inc_ref(v_array_3441_);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_snd_3424_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; 
v_unused_3560_ = lean_ctor_get(v_snd_3424_, 2);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_snd_3424_, 1);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_snd_3424_, 0);
lean_dec(v_unused_3562_);
v___x_3459_ = v_snd_3424_;
v_isShared_3460_ = v_isSharedCheck_3559_;
goto v_resetjp_3458_;
}
else
{
lean_dec(v_snd_3424_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3559_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_array_3461_; lean_object* v_start_3462_; lean_object* v_stop_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v_array_3461_ = lean_ctor_get(v_fst_3437_, 0);
v_start_3462_ = lean_ctor_get(v_fst_3437_, 1);
v_stop_3463_ = lean_ctor_get(v_fst_3437_, 2);
v___x_3464_ = lean_array_fget(v_array_3441_, v_start_3442_);
v___x_3465_ = lean_unsigned_to_nat(1u);
v___x_3466_ = lean_nat_add(v_start_3442_, v___x_3465_);
lean_dec(v_start_3442_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3466_);
v___x_3468_ = v___x_3459_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_array_3441_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_stop_3443_);
v___x_3468_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_nat_dec_lt(v_start_3462_, v_stop_3463_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v___x_3464_);
lean_dec_ref(v_xs_3409_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3468_);
v___x_3471_ = v___x_3439_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3468_);
v___x_3471_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3471_);
v___x_3473_ = v___x_3435_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3473_);
v___x_3475_ = v___x_3431_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_fst_3429_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3475_);
v___x_3477_ = v___x_3427_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_fst_3425_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
return v___x_3478_;
}
}
}
}
}
else
{
lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3554_; 
lean_inc(v_stop_3463_);
lean_inc(v_start_3462_);
lean_inc_ref(v_array_3461_);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_fst_3437_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; lean_object* v_unused_3556_; lean_object* v_unused_3557_; 
v_unused_3555_ = lean_ctor_get(v_fst_3437_, 2);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_fst_3437_, 1);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_fst_3437_, 0);
lean_dec(v_unused_3557_);
v___x_3484_ = v_fst_3437_;
v_isShared_3485_ = v_isSharedCheck_3554_;
goto v_resetjp_3483_;
}
else
{
lean_dec(v_fst_3437_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3554_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_array_3486_; lean_object* v_start_3487_; lean_object* v_stop_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v_array_3486_ = lean_ctor_get(v_fst_3433_, 0);
v_start_3487_ = lean_ctor_get(v_fst_3433_, 1);
v_stop_3488_ = lean_ctor_get(v_fst_3433_, 2);
v___x_3489_ = lean_array_fget(v_array_3461_, v_start_3462_);
v___x_3490_ = lean_nat_add(v_start_3462_, v___x_3465_);
lean_dec(v_start_3462_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v___x_3490_);
v___x_3492_ = v___x_3484_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_array_3461_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_stop_3463_);
v___x_3492_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_nat_dec_lt(v_start_3487_, v_stop_3488_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3495_; 
lean_dec(v___x_3489_);
lean_dec(v___x_3464_);
lean_dec_ref(v_xs_3409_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3468_);
lean_ctor_set(v___x_3439_, 0, v___x_3492_);
v___x_3495_ = v___x_3439_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3468_);
v___x_3495_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3495_);
v___x_3497_ = v___x_3435_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3497_);
v___x_3499_ = v___x_3431_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3429_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3499_);
v___x_3501_ = v___x_3427_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3425_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
}
}
}
else
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3549_; 
lean_inc(v_stop_3488_);
lean_inc(v_start_3487_);
lean_inc_ref(v_array_3486_);
lean_del_object(v___x_3427_);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_fst_3433_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; lean_object* v_unused_3551_; lean_object* v_unused_3552_; 
v_unused_3550_ = lean_ctor_get(v_fst_3433_, 2);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_fst_3433_, 1);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_fst_3433_, 0);
lean_dec(v_unused_3552_);
v___x_3508_ = v_fst_3433_;
v_isShared_3509_ = v_isSharedCheck_3549_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_fst_3433_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3549_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v_a_3510_ = lean_array_uget_borrowed(v_as_3410_, v_i_3412_);
v___x_3511_ = lean_array_fget(v_array_3486_, v_start_3487_);
v___x_3512_ = lean_nat_add(v_start_3487_, v___x_3465_);
lean_dec(v_start_3487_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3512_);
v___x_3514_ = v___x_3508_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_array_3486_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_stop_3488_);
v___x_3514_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; 
lean_inc_ref(v_xs_3409_);
lean_inc(v_a_3510_);
v___x_3515_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3510_, v___x_3464_, v_xs_3409_, v___x_3511_, v___x_3489_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_fst_3517_; lean_object* v_snd_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3539_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v_fst_3517_ = lean_ctor_get(v_a_3516_, 0);
v_snd_3518_ = lean_ctor_get(v_a_3516_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3520_ = v_a_3516_;
v_isShared_3521_ = v_isSharedCheck_3539_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_snd_3518_);
lean_inc(v_fst_3517_);
lean_dec(v_a_3516_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3539_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_fst_3425_);
lean_ctor_set(v___x_3522_, 1, v_snd_3518_);
v___x_3523_ = lean_array_push(v_fst_3429_, v_fst_3517_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 1, v___x_3468_);
lean_ctor_set(v___x_3520_, 0, v___x_3492_);
v___x_3525_ = v___x_3520_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3468_);
v___x_3525_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3525_);
lean_ctor_set(v___x_3439_, 0, v___x_3514_);
v___x_3527_ = v___x_3439_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3527_);
lean_ctor_set(v___x_3435_, 0, v___x_3523_);
v___x_3529_ = v___x_3435_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3529_);
lean_ctor_set(v___x_3431_, 0, v___x_3522_);
v___x_3531_ = v___x_3431_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
size_t v___x_3532_; size_t v___x_3533_; 
v___x_3532_ = ((size_t)1ULL);
v___x_3533_ = lean_usize_add(v_i_3412_, v___x_3532_);
v_i_3412_ = v___x_3533_;
v_b_3413_ = v___x_3531_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v___x_3514_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v___x_3468_);
lean_del_object(v___x_3439_);
lean_del_object(v___x_3435_);
lean_del_object(v___x_3431_);
lean_dec(v_fst_3429_);
lean_dec(v_fst_3425_);
lean_dec_ref(v_xs_3409_);
v_a_3540_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3515_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3515_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3571_, lean_object* v_as_3572_, lean_object* v_sz_3573_, lean_object* v_i_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
size_t v_sz_boxed_3581_; size_t v_i_boxed_3582_; lean_object* v_res_3583_; 
v_sz_boxed_3581_ = lean_unbox_usize(v_sz_3573_);
lean_dec(v_sz_3573_);
v_i_boxed_3582_ = lean_unbox_usize(v_i_3574_);
lean_dec(v_i_3574_);
v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3571_, v_as_3572_, v_sz_boxed_3581_, v_i_boxed_3582_, v_b_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec_ref(v_as_3572_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
if (lean_obj_tag(v_a_3584_) == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = l_List_reverse___redArg(v_a_3585_);
return v___x_3586_;
}
else
{
lean_object* v_head_3587_; lean_object* v_tail_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3597_; 
v_head_3587_ = lean_ctor_get(v_a_3584_, 0);
v_tail_3588_ = lean_ctor_get(v_a_3584_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3590_ = v_a_3584_;
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_tail_3588_);
lean_inc(v_head_3587_);
lean_dec(v_a_3584_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3587_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v_a_3585_);
lean_ctor_set(v___x_3590_, 0, v___x_3592_);
v___x_3594_ = v___x_3590_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3585_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
v_a_3584_ = v_tail_3588_;
v_a_3585_ = v___x_3594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3598_, lean_object* v_j_3599_){
_start:
{
lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3600_ = lean_array_get_size(v_as_3598_);
v___x_3601_ = lean_nat_dec_lt(v_j_3599_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_dec(v_j_3599_);
v___x_3602_ = lean_box(0);
return v___x_3602_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3603_ = lean_array_fget_borrowed(v_as_3598_, v_j_3599_);
v___x_3604_ = lean_array_get_size(v___x_3603_);
v___x_3605_ = lean_unsigned_to_nat(0u);
v___x_3606_ = lean_nat_dec_eq(v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = lean_nat_add(v_j_3599_, v___x_3607_);
lean_dec(v_j_3599_);
v_j_3599_ = v___x_3608_;
goto _start;
}
else
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_j_3599_);
return v___x_3610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3611_, lean_object* v_j_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3611_, v_j_3612_);
lean_dec_ref(v_as_3611_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3614_, lean_object* v_as_3615_, size_t v_sz_3616_, size_t v_i_3617_, lean_object* v_b_3618_){
_start:
{
uint8_t v___x_3620_; 
v___x_3620_ = lean_usize_dec_lt(v_i_3617_, v_sz_3616_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref(v_a_3614_);
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v_b_3618_);
return v___x_3621_;
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; size_t v___x_3625_; size_t v___x_3626_; 
v_a_3622_ = lean_array_uget_borrowed(v_as_3615_, v_i_3617_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3614_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_a_3614_);
lean_ctor_set(v___x_3623_, 1, v_a_3622_);
v___x_3624_ = lean_array_push(v_b_3618_, v___x_3623_);
v___x_3625_ = ((size_t)1ULL);
v___x_3626_ = lean_usize_add(v_i_3617_, v___x_3625_);
v_i_3617_ = v___x_3626_;
v_b_3618_ = v___x_3624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3628_, lean_object* v_as_3629_, lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v_i_boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3635_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3628_, v_as_3629_, v_sz_boxed_3634_, v_i_boxed_3635_, v_b_3632_);
lean_dec_ref(v_as_3629_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3637_, lean_object* v_xs_3638_, lean_object* v_as_3639_, size_t v_sz_3640_, size_t v_i_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_lt(v_i_3641_, v_sz_3640_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref(v_xs_3638_);
lean_dec_ref(v_a_3637_);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v_b_3642_);
return v___x_3649_;
}
else
{
lean_object* v_snd_3650_; lean_object* v_fst_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3694_; 
v_snd_3650_ = lean_ctor_get(v_b_3642_, 1);
v_fst_3651_ = lean_ctor_get(v_b_3642_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_b_3642_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3653_ = v_b_3642_;
v_isShared_3654_ = v_isSharedCheck_3694_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_snd_3650_);
lean_inc(v_fst_3651_);
lean_dec(v_b_3642_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3694_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_array_3655_; lean_object* v_start_3656_; lean_object* v_stop_3657_; uint8_t v___x_3658_; 
v_array_3655_ = lean_ctor_get(v_snd_3650_, 0);
v_start_3656_ = lean_ctor_get(v_snd_3650_, 1);
v_stop_3657_ = lean_ctor_get(v_snd_3650_, 2);
v___x_3658_ = lean_nat_dec_lt(v_start_3656_, v_stop_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref(v_xs_3638_);
lean_dec_ref(v_a_3637_);
if (v_isShared_3654_ == 0)
{
v___x_3660_ = v___x_3653_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_fst_3651_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_snd_3650_);
v___x_3660_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
}
else
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3690_; 
lean_inc(v_stop_3657_);
lean_inc(v_start_3656_);
lean_inc_ref(v_array_3655_);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_snd_3650_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3691_ = lean_ctor_get(v_snd_3650_, 2);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_snd_3650_, 1);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_snd_3650_, 0);
lean_dec(v_unused_3693_);
v___x_3664_ = v_snd_3650_;
v_isShared_3665_ = v_isSharedCheck_3690_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_snd_3650_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3690_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v_a_3666_ = lean_array_uget_borrowed(v_as_3639_, v_i_3641_);
v___x_3667_ = lean_array_fget(v_array_3655_, v_start_3656_);
v___x_3668_ = lean_unsigned_to_nat(1u);
v___x_3669_ = lean_nat_add(v_start_3656_, v___x_3668_);
lean_dec(v_start_3656_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3669_);
v___x_3671_ = v___x_3664_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_array_3655_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_stop_3657_);
v___x_3671_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; 
lean_inc(v_a_3666_);
lean_inc_ref(v_xs_3638_);
lean_inc_ref(v_a_3637_);
v___x_3672_ = l_Lean_Elab_Structural_argsInGroup(v_a_3637_, v_xs_3638_, v_a_3666_, v___x_3667_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___x_3667_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = lean_array_push(v_fst_3651_, v_a_3673_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v___x_3671_);
lean_ctor_set(v___x_3653_, 0, v___x_3674_);
v___x_3676_ = v___x_3653_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3671_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
size_t v___x_3677_; size_t v___x_3678_; 
v___x_3677_ = ((size_t)1ULL);
v___x_3678_ = lean_usize_add(v_i_3641_, v___x_3677_);
v_i_3641_ = v___x_3678_;
v_b_3642_ = v___x_3676_;
goto _start;
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___x_3671_);
lean_del_object(v___x_3653_);
lean_dec(v_fst_3651_);
lean_dec_ref(v_xs_3638_);
lean_dec_ref(v_a_3637_);
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3695_, lean_object* v_xs_3696_, lean_object* v_as_3697_, lean_object* v_sz_3698_, lean_object* v_i_3699_, lean_object* v_b_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
size_t v_sz_boxed_3706_; size_t v_i_boxed_3707_; lean_object* v_res_3708_; 
v_sz_boxed_3706_ = lean_unbox_usize(v_sz_3698_);
lean_dec(v_sz_3698_);
v_i_boxed_3707_ = lean_unbox_usize(v_i_3699_);
lean_dec(v_i_3699_);
v_res_3708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3695_, v_xs_3696_, v_as_3697_, v_sz_boxed_3706_, v_i_boxed_3707_, v_b_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v_as_3697_);
return v_res_3708_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
return v___x_3713_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
return v___x_3716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
return v___x_3719_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
return v___x_3725_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3729_, lean_object* v_values_3730_, lean_object* v_xs_3731_, lean_object* v_fnNames_3732_, lean_object* v_as_3733_, size_t v_sz_3734_, size_t v_i_3735_, lean_object* v_b_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_a_3743_; uint8_t v___x_3747_; 
v___x_3747_ = lean_usize_dec_lt(v_i_3735_, v_sz_3734_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; 
lean_dec_ref(v_xs_3731_);
lean_dec_ref(v___x_3729_);
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v_b_3736_);
return v___x_3748_;
}
else
{
lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3824_; 
v_fst_3749_ = lean_ctor_get(v_b_3736_, 0);
v_snd_3750_ = lean_ctor_get(v_b_3736_, 1);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_b_3736_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3752_ = v_b_3736_;
v_isShared_3753_ = v_isSharedCheck_3824_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_snd_3750_);
lean_inc(v_fst_3749_);
lean_dec(v_b_3736_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3824_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v_recArgInfoss_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3756_ = lean_box(0);
v_a_3757_ = lean_array_uget_borrowed(v_as_3733_, v_i_3735_);
v___x_3758_ = lean_array_get_size(v___x_3729_);
lean_inc_ref(v___x_3729_);
v___x_3759_ = l_Array_toSubarray___redArg(v___x_3729_, v___x_3754_, v___x_3758_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v___x_3759_);
lean_ctor_set(v___x_3752_, 0, v_recArgInfoss_3755_);
v___x_3761_ = v___x_3752_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_recArgInfoss_3755_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
size_t v_sz_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v_sz_3762_ = lean_array_size(v_values_3730_);
v___x_3763_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3731_);
lean_inc(v_a_3757_);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3757_, v_xs_3731_, v_values_3730_, v_sz_3762_, v___x_3763_, v___x_3761_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v_fst_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3813_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v_fst_3766_ = lean_ctor_get(v_a_3765_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v_a_3765_, 1);
lean_dec(v_unused_3814_);
v___x_3768_ = v_a_3765_;
v_isShared_3769_ = v_isSharedCheck_3813_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_fst_3766_);
lean_dec(v_a_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3813_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3766_, v___x_3754_);
if (lean_obj_tag(v___x_3770_) == 1)
{
lean_object* v_val_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3784_; 
lean_dec(v_fst_3766_);
v_val_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3757_);
v___x_3773_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3757_);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = lean_array_get_borrowed(v___x_3756_, v_fnNames_3732_, v_val_3771_);
lean_dec(v_val_3771_);
lean_inc(v___x_3777_);
v___x_3778_ = l_Lean_MessageData_ofName(v___x_3777_);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3776_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v_fst_3749_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v_snd_3750_);
lean_ctor_set(v___x_3768_, 0, v___x_3782_);
v___x_3784_ = v___x_3768_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_snd_3750_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
v_a_3743_ = v___x_3784_;
goto v___jp_3742_;
}
}
else
{
lean_object* v___x_3786_; 
lean_dec(v___x_3770_);
v___x_3786_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3766_);
lean_dec(v_fst_3766_);
if (lean_obj_tag(v___x_3786_) == 1)
{
lean_object* v_val_3787_; size_t v_sz_3788_; lean_object* v___x_3789_; 
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_val_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v_sz_3788_ = lean_array_size(v_val_3787_);
lean_inc(v_a_3757_);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3757_, v_val_3787_, v_sz_3788_, v___x_3763_, v_snd_3750_);
lean_dec(v_val_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v_a_3790_);
lean_ctor_set(v___x_3768_, 0, v_fst_3749_);
v___x_3792_ = v___x_3768_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fst_3749_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_a_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
v_a_3743_ = v___x_3792_;
goto v___jp_3742_;
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3768_);
lean_dec(v_fst_3749_);
lean_dec_ref(v_xs_3731_);
lean_dec_ref(v___x_3729_);
v_a_3794_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3789_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3789_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec(v___x_3786_);
v___x_3802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3757_);
v___x_3803_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3757_);
v___x_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_fst_3749_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v_snd_3750_);
lean_ctor_set(v___x_3768_, 0, v___x_3809_);
v___x_3811_ = v___x_3768_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_snd_3750_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v_a_3743_ = v___x_3811_;
goto v___jp_3742_;
}
}
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_snd_3750_);
lean_dec(v_fst_3749_);
lean_dec_ref(v_xs_3731_);
lean_dec_ref(v___x_3729_);
v_a_3815_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3764_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3764_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
}
v___jp_3742_:
{
size_t v___x_3744_; size_t v___x_3745_; 
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_add(v_i_3735_, v___x_3744_);
v_i_3735_ = v___x_3745_;
v_b_3736_ = v_a_3743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3825_, lean_object* v_values_3826_, lean_object* v_xs_3827_, lean_object* v_fnNames_3828_, lean_object* v_as_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3825_, v_values_3826_, v_xs_3827_, v_fnNames_3828_, v_as_3829_, v_sz_boxed_3838_, v_i_boxed_3839_, v_b_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v_as_3829_);
lean_dec_ref(v_fnNames_3828_);
lean_dec_ref(v_values_3826_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3841_, lean_object* v___x_3842_, lean_object* v_values_3843_, lean_object* v_fnNames_3844_, lean_object* v_as_3845_, size_t v_sz_3846_, size_t v_i_3847_, lean_object* v_b_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_a_3855_; uint8_t v___x_3859_; 
v___x_3859_ = lean_usize_dec_lt(v_i_3847_, v_sz_3846_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref(v___x_3842_);
lean_dec_ref(v_xs_3841_);
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v_b_3848_);
return v___x_3860_;
}
else
{
lean_object* v_fst_3861_; lean_object* v_snd_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3936_; 
v_fst_3861_ = lean_ctor_get(v_b_3848_, 0);
v_snd_3862_ = lean_ctor_get(v_b_3848_, 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_b_3848_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3864_ = v_b_3848_;
v_isShared_3865_ = v_isSharedCheck_3936_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_snd_3862_);
lean_inc(v_fst_3861_);
lean_dec(v_b_3848_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3936_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v_recArgInfoss_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3868_ = lean_box(0);
v_a_3869_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
v___x_3870_ = lean_array_get_size(v___x_3842_);
lean_inc_ref(v___x_3842_);
v___x_3871_ = l_Array_toSubarray___redArg(v___x_3842_, v___x_3866_, v___x_3870_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v___x_3871_);
lean_ctor_set(v___x_3864_, 0, v_recArgInfoss_3867_);
v___x_3873_ = v___x_3864_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_recArgInfoss_3867_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
size_t v_sz_3874_; size_t v___x_3875_; lean_object* v___x_3876_; 
v_sz_3874_ = lean_array_size(v_values_3843_);
v___x_3875_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3841_);
lean_inc(v_a_3869_);
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3869_, v_xs_3841_, v_values_3843_, v_sz_3874_, v___x_3875_, v___x_3873_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v_fst_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3925_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v_fst_3878_ = lean_ctor_get(v_a_3877_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_a_3877_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; 
v_unused_3926_ = lean_ctor_get(v_a_3877_, 1);
lean_dec(v_unused_3926_);
v___x_3880_ = v_a_3877_;
v_isShared_3881_ = v_isSharedCheck_3925_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_fst_3878_);
lean_dec(v_a_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3925_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3878_, v___x_3866_);
if (lean_obj_tag(v___x_3882_) == 1)
{
lean_object* v_val_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_dec(v_fst_3878_);
v_val_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_val_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___x_3884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3869_);
v___x_3885_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3869_);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_array_get_borrowed(v___x_3868_, v_fnNames_3844_, v_val_3883_);
lean_dec(v_val_3883_);
lean_inc(v___x_3889_);
v___x_3890_ = l_Lean_MessageData_ofName(v___x_3889_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3888_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_fst_3861_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_snd_3862_);
lean_ctor_set(v___x_3880_, 0, v___x_3894_);
v___x_3896_ = v___x_3880_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_snd_3862_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
v_a_3855_ = v___x_3896_;
goto v___jp_3854_;
}
}
else
{
lean_object* v___x_3898_; 
lean_dec(v___x_3882_);
v___x_3898_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3878_);
lean_dec(v_fst_3878_);
if (lean_obj_tag(v___x_3898_) == 1)
{
lean_object* v_val_3899_; size_t v_sz_3900_; lean_object* v___x_3901_; 
v_val_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v___x_3898_, 1);
v_sz_3900_ = lean_array_size(v_val_3899_);
lean_inc(v_a_3869_);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3869_, v_val_3899_, v_sz_3900_, v___x_3875_, v_snd_3862_);
lean_dec(v_val_3899_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_a_3902_);
lean_ctor_set(v___x_3880_, 0, v_fst_3861_);
v___x_3904_ = v___x_3880_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_fst_3861_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_a_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
v_a_3855_ = v___x_3904_;
goto v___jp_3854_;
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_del_object(v___x_3880_);
lean_dec(v_fst_3861_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v_xs_3841_);
v_a_3906_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3901_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3901_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_dec(v___x_3898_);
v___x_3914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3869_);
v___x_3915_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3869_);
v___x_3916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v_fst_3861_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_snd_3862_);
lean_ctor_set(v___x_3880_, 0, v___x_3921_);
v___x_3923_ = v___x_3880_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_snd_3862_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
v_a_3855_ = v___x_3923_;
goto v___jp_3854_;
}
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v_snd_3862_);
lean_dec(v_fst_3861_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v_xs_3841_);
v_a_3927_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3876_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3876_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
v___jp_3854_:
{
size_t v___x_3856_; size_t v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_add(v_i_3847_, v___x_3856_);
v___x_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3842_, v_values_3843_, v_xs_3841_, v_fnNames_3844_, v_as_3845_, v_sz_3846_, v___x_3857_, v_a_3855_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3937_, lean_object* v___x_3938_, lean_object* v_values_3939_, lean_object* v_fnNames_3940_, lean_object* v_as_3941_, lean_object* v_sz_3942_, lean_object* v_i_3943_, lean_object* v_b_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
size_t v_sz_boxed_3950_; size_t v_i_boxed_3951_; lean_object* v_res_3952_; 
v_sz_boxed_3950_ = lean_unbox_usize(v_sz_3942_);
lean_dec(v_sz_3942_);
v_i_boxed_3951_ = lean_unbox_usize(v_i_3943_);
lean_dec(v_i_3943_);
v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3937_, v___x_3938_, v_values_3939_, v_fnNames_3940_, v_as_3941_, v_sz_boxed_3950_, v_i_boxed_3951_, v_b_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec_ref(v_as_3941_);
lean_dec_ref(v_fnNames_3940_);
lean_dec_ref(v_values_3939_);
return v_res_3952_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__2));
v___x_3959_ = l_Lean_MessageData_ofFormat(v___x_3958_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__4));
v___x_3962_ = l_Lean_stringToMessageData(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__7));
v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = lean_box(1);
v___x_3969_ = l_Lean_MessageData_ofFormat(v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3970_, lean_object* v_fixedParamPerms_3971_, lean_object* v_xs_3972_, lean_object* v_values_3973_, lean_object* v_termMeasure_x3fs_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v___x_3980_; lean_object* v_candidates_3981_; lean_object* v___x_3982_; lean_object* v_perms_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_report_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3980_ = lean_unsigned_to_nat(0u);
v_candidates_3981_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__0));
v___x_3982_ = lean_array_get_size(v_values_3973_);
v_perms_3983_ = lean_ctor_get(v_fixedParamPerms_3971_, 1);
lean_inc_ref(v_perms_3983_);
lean_dec_ref(v_fixedParamPerms_3971_);
lean_inc_ref(v_values_3973_);
v___x_3984_ = l_Array_toSubarray___redArg(v_values_3973_, v___x_3980_, v___x_3982_);
v___x_3985_ = lean_array_get_size(v_termMeasure_x3fs_3974_);
v_report_3986_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3987_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3974_, v___x_3980_, v___x_3985_);
v___x_3988_ = lean_array_get_size(v_perms_3983_);
v___x_3989_ = l_Array_toSubarray___redArg(v_perms_3983_, v___x_3980_, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3987_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3984_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v_candidates_3981_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_report_3986_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v_sz_3994_ = lean_array_size(v_fnNames_3970_);
v___x_3995_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3972_);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3972_, v_fnNames_3970_, v_sz_3994_, v___x_3995_, v___x_3993_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v_snd_3998_; lean_object* v_toCold_3999_; lean_object* v_options_4000_; lean_object* v_fst_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4139_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v_snd_3998_ = lean_ctor_get(v_a_3997_, 1);
lean_inc(v_snd_3998_);
v_toCold_3999_ = lean_ctor_get(v_a_3977_, 0);
v_options_4000_ = lean_ctor_get(v_toCold_3999_, 2);
v_fst_4001_ = lean_ctor_get(v_a_3997_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_a_3997_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v_a_3997_, 1);
lean_dec(v_unused_4140_);
v___x_4003_ = v_a_3997_;
v_isShared_4004_ = v_isSharedCheck_4139_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_fst_4001_);
lean_dec(v_a_3997_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4139_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v_fst_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4137_; 
v_fst_4005_ = lean_ctor_get(v_snd_3998_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_snd_3998_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v_snd_3998_, 1);
lean_dec(v_unused_4138_);
v___x_4007_ = v_snd_3998_;
v_isShared_4008_ = v_isSharedCheck_4137_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_fst_4005_);
lean_dec(v_snd_3998_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4137_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_inheritedTraceOptions_4009_; uint8_t v_hasTrace_4010_; size_t v_sz_4011_; lean_object* v___x_4012_; lean_object* v___y_4014_; lean_object* v_report_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___x_4062_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; 
v_inheritedTraceOptions_4009_ = lean_ctor_get(v_toCold_3999_, 11);
v_hasTrace_4010_ = lean_ctor_get_uint8(v_options_4000_, sizeof(void*)*1);
v_sz_4011_ = lean_array_size(v_fst_4005_);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4011_, v___x_3995_, v_fst_4005_);
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4010_ == 0)
{
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
goto v___jp_4101_;
}
else
{
lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4111_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4009_, v_options_4000_, v___x_4111_);
if (v___x_4112_ == 0)
{
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
goto v___jp_4101_;
}
else
{
lean_object* v___x_4113_; lean_object* v___y_4115_; lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4113_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4133_ = lean_array_get_size(v___x_4012_);
v___x_4134_ = lean_nat_dec_lt(v___x_3980_, v___x_4133_);
if (v___x_4134_ == 0)
{
v___y_4115_ = v___x_4132_;
goto v___jp_4114_;
}
else
{
size_t v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_usize_of_nat(v___x_4133_);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4012_, v___x_3995_, v___x_4135_, v___x_4132_);
v___y_4115_ = v___x_4136_;
goto v___jp_4114_;
}
v___jp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4116_ = lean_array_to_list(v___y_4115_);
v___x_4117_ = lean_box(0);
v___x_4118_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4116_, v___x_4117_);
v___x_4119_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__9, &l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9);
v___x_4120_ = l_Lean_MessageData_joinSep(v___x_4118_, v___x_4119_);
v___x_4121_ = l_Lean_indentD(v___x_4120_);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4113_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4062_, v___x_4122_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_dec_ref_known(v___x_4123_, 1);
v___y_4102_ = v_a_3975_;
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
goto v___jp_4101_;
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___x_4012_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4003_);
lean_dec(v_fst_4001_);
lean_dec_ref(v_values_3973_);
lean_dec_ref(v_xs_3972_);
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4123_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4123_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
}
v___jp_4013_:
{
lean_object* v___x_4021_; 
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 1, v_candidates_3981_);
lean_ctor_set(v___x_4007_, 0, v_report_4015_);
v___x_4021_ = v___x_4007_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_report_4015_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_candidates_3981_);
v___x_4021_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
size_t v_sz_4022_; lean_object* v___x_4023_; 
v_sz_4022_ = lean_array_size(v___y_4014_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3972_, v___x_4012_, v_values_3973_, v_fnNames_3970_, v___y_4014_, v_sz_4022_, v___x_3995_, v___x_4021_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec_ref(v___y_4014_);
lean_dec_ref(v_values_3973_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4040_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4040_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4040_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_fst_4028_; lean_object* v_snd_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4039_; 
v_fst_4028_ = lean_ctor_get(v_a_4024_, 0);
v_snd_4029_ = lean_ctor_get(v_a_4024_, 1);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_a_4024_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4031_ = v_a_4024_;
v_isShared_4032_ = v_isSharedCheck_4039_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_snd_4029_);
lean_inc(v_fst_4028_);
lean_dec(v_a_4024_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4039_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 1, v_fst_4028_);
lean_ctor_set(v___x_4031_, 0, v_snd_4029_);
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_snd_4029_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v_fst_4028_);
v___x_4034_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4036_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4034_);
v___x_4036_ = v___x_4026_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
v_a_4041_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4023_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4023_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
v___jp_4050_:
{
lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4056_ = lean_array_get_size(v___y_4051_);
v___x_4057_ = lean_nat_dec_eq(v___x_4056_, v___x_3980_);
if (v___x_4057_ == 0)
{
lean_del_object(v___x_4003_);
v___y_4014_ = v___y_4051_;
v_report_4015_ = v_fst_4001_;
v___y_4016_ = v___y_4052_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4058_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__3, &l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3);
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 7);
lean_ctor_set(v___x_4003_, 1, v___x_4058_);
v___x_4060_ = v___x_4003_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_fst_4001_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
v___y_4014_ = v___y_4051_;
v_report_4015_ = v___x_4060_;
v___y_4016_ = v___y_4052_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
goto v___jp_4013_;
}
}
}
v___jp_4063_:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4068_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_toCold_4070_; lean_object* v_options_4071_; uint8_t v_hasTrace_4072_; 
v_toCold_4070_ = lean_ctor_get(v___y_4066_, 0);
v_options_4071_ = lean_ctor_get(v_toCold_4070_, 2);
v_hasTrace_4072_ = lean_ctor_get_uint8(v_options_4071_, sizeof(void*)*1);
if (v_hasTrace_4072_ == 0)
{
lean_object* v_a_4073_; 
v_a_4073_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4069_, 1);
v___y_4051_ = v_a_4073_;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4067_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4074_; lean_object* v_inheritedTraceOptions_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_a_4074_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4069_, 1);
v_inheritedTraceOptions_4075_ = lean_ctor_get(v_toCold_4070_, 11);
v___x_4076_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4075_, v_options_4071_, v___x_4076_);
if (v___x_4077_ == 0)
{
v___y_4051_ = v_a_4074_;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4067_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4078_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__5, &l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5);
lean_inc(v_a_4074_);
v___x_4079_ = lean_array_to_list(v_a_4074_);
v___x_4080_ = lean_box(0);
v___x_4081_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4079_, v___x_4080_);
v___x_4082_ = l_Lean_MessageData_ofList(v___x_4081_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4078_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4062_, v___x_4083_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_dec_ref_known(v___x_4084_, 1);
v___y_4051_ = v_a_4074_;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4067_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v_a_4074_);
lean_dec_ref(v___x_4012_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4003_);
lean_dec(v_fst_4001_);
lean_dec_ref(v_values_3973_);
lean_dec_ref(v_xs_3972_);
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec_ref(v___x_4012_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4003_);
lean_dec(v_fst_4001_);
lean_dec_ref(v_values_3973_);
lean_dec_ref(v_xs_3972_);
v_a_4093_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4069_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4069_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
v___jp_4101_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4107_ = lean_array_get_size(v___x_4012_);
v___x_4108_ = lean_nat_dec_lt(v___x_3980_, v___x_4107_);
if (v___x_4108_ == 0)
{
v___y_4064_ = v___y_4102_;
v___y_4065_ = v___y_4103_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___x_4106_;
goto v___jp_4063_;
}
else
{
size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_usize_of_nat(v___x_4107_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4012_, v___x_3995_, v___x_4109_, v___x_4106_);
v___y_4064_ = v___y_4102_;
v___y_4065_ = v___y_4103_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___x_4110_;
goto v___jp_4063_;
}
}
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v_values_3973_);
lean_dec_ref(v_xs_3972_);
v_a_4141_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_3996_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_3996_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4149_, lean_object* v_fixedParamPerms_4150_, lean_object* v_xs_4151_, lean_object* v_values_4152_, lean_object* v_termMeasure_x3fs_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4149_, v_fixedParamPerms_4150_, v_xs_4151_, v_values_4152_, v_termMeasure_x3fs_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec_ref(v_fnNames_4149_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4160_, lean_object* v_as_4161_, size_t v_sz_4162_, size_t v_i_4163_, lean_object* v_b_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4160_, v_as_4161_, v_sz_4162_, v_i_4163_, v_b_4164_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4171_, lean_object* v_as_4172_, lean_object* v_sz_4173_, lean_object* v_i_4174_, lean_object* v_b_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
size_t v_sz_boxed_4181_; size_t v_i_boxed_4182_; lean_object* v_res_4183_; 
v_sz_boxed_4181_ = lean_unbox_usize(v_sz_4173_);
lean_dec(v_sz_4173_);
v_i_boxed_4182_ = lean_unbox_usize(v_i_4174_);
lean_dec(v_i_4174_);
v_res_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4171_, v_as_4172_, v_sz_boxed_4181_, v_i_boxed_4182_, v_b_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec_ref(v_as_4172_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4184_, uint8_t v_skipRealize_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v_env_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4188_ = lean_st_ref_get(v___y_4186_);
v_env_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc_ref(v_env_4189_);
lean_dec(v___x_4188_);
v___x_4190_ = l_Lean_Environment_contains(v_env_4189_, v_constName_4184_, v_skipRealize_4185_);
v___x_4191_ = lean_box(v___x_4190_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4193_, lean_object* v_skipRealize_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
uint8_t v_skipRealize_boxed_4197_; lean_object* v_res_4198_; 
v_skipRealize_boxed_4197_ = lean_unbox(v_skipRealize_4194_);
v_res_4198_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4193_, v_skipRealize_boxed_4197_, v___y_4195_);
lean_dec(v___y_4195_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4199_, uint8_t v_skipRealize_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4199_, v_skipRealize_4200_, v___y_4204_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4207_, lean_object* v_skipRealize_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_skipRealize_boxed_4214_; lean_object* v_res_4215_; 
v_skipRealize_boxed_4214_ = lean_unbox(v_skipRealize_4208_);
v_res_4215_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4207_, v_skipRealize_boxed_4214_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_Meta_saveState___redArg(v___y_4218_, v___y_4220_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
lean_inc(v___y_4218_);
lean_inc_ref(v___y_4217_);
v___x_4224_ = lean_apply_5(v_x_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, lean_box(0));
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_dec(v_a_4223_);
return v___x_4224_;
}
else
{
lean_object* v_a_4225_; uint8_t v___x_4226_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
v___x_4226_ = l_Lean_Exception_isInterrupt(v_a_4225_);
if (v___x_4226_ == 0)
{
uint8_t v___x_4227_; 
lean_inc(v_a_4225_);
v___x_4227_ = l_Lean_Exception_isRuntime(v_a_4225_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; 
lean_dec_ref_known(v___x_4224_, 1);
v___x_4228_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4223_, v___y_4218_, v___y_4220_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4235_ == 0)
{
lean_object* v_unused_4236_; 
v_unused_4236_ = lean_ctor_get(v___x_4228_, 0);
lean_dec(v_unused_4236_);
v___x_4230_ = v___x_4228_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_dec(v___x_4228_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set_tag(v___x_4230_, 1);
lean_ctor_set(v___x_4230_, 0, v_a_4225_);
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4225_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec(v_a_4225_);
v_a_4237_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4228_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4228_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_dec(v_a_4225_);
lean_dec(v_a_4223_);
return v___x_4224_;
}
}
else
{
lean_dec(v_a_4225_);
lean_dec(v_a_4223_);
return v___x_4224_;
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref(v_x_4216_);
v_a_4245_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4222_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4222_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4268_, lean_object* v_x_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4268_, v_x_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
return v_res_4275_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4278_ = l_Lean_stringToMessageData(v___x_4277_);
return v___x_4278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4281_ = l_Lean_stringToMessageData(v___x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4282_, uint8_t v___x_4283_, lean_object* v_group_4284_, lean_object* v_k_4285_, lean_object* v_comb_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4282_, v___x_4283_, v___y_4290_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; uint8_t v___x_4294_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref_known(v___x_4292_, 1);
v___x_4294_ = lean_unbox(v_a_4293_);
lean_dec(v_a_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4295_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4296_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4284_);
v___x_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4299_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v___x_4301_; 
lean_dec_ref_known(v___x_4300_, 1);
v___x_4301_ = lean_apply_6(v_k_4285_, v_comb_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, lean_box(0));
return v___x_4301_;
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v_comb_4286_);
lean_dec_ref(v_k_4285_);
v_a_4302_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4300_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4300_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
lean_object* v___x_4310_; 
lean_dec_ref(v_group_4284_);
v___x_4310_ = lean_apply_6(v_k_4285_, v_comb_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, lean_box(0));
return v___x_4310_;
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v_comb_4286_);
lean_dec_ref(v_k_4285_);
lean_dec_ref(v_group_4284_);
v_a_4311_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4292_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4292_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4319_, lean_object* v___x_4320_, lean_object* v_group_4321_, lean_object* v_k_4322_, lean_object* v_comb_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
uint8_t v___x_4299__boxed_4329_; lean_object* v_res_4330_; 
v___x_4299__boxed_4329_ = lean_unbox(v___x_4320_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4319_, v___x_4299__boxed_4329_, v_group_4321_, v_k_4322_, v_comb_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
return v_res_4330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4333_ = l_Lean_stringToMessageData(v___x_4332_);
return v___x_4333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4335_ = l_Lean_stringToMessageData(v___x_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4336_, lean_object* v_fnNames_4337_, lean_object* v_xs_4338_, lean_object* v_values_4339_, lean_object* v_as_4340_, size_t v_sz_4341_, size_t v_i_4342_, lean_object* v_b_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
uint8_t v___x_4349_; 
v___x_4349_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_dec_ref(v_values_4339_);
lean_dec_ref(v_xs_4338_);
lean_dec_ref(v_k_4336_);
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_b_4343_);
return v___x_4350_;
}
else
{
lean_object* v_snd_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4422_; 
v_snd_4351_ = lean_ctor_get(v_b_4343_, 1);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_b_4343_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; 
v_unused_4423_ = lean_ctor_get(v_b_4343_, 0);
lean_dec(v_unused_4423_);
v___x_4353_ = v_b_4343_;
v_isShared_4354_ = v_isSharedCheck_4422_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_snd_4351_);
lean_dec(v_b_4343_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4422_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_a_4355_; lean_object* v_group_4356_; lean_object* v_comb_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4421_; 
v_a_4355_ = lean_array_uget(v_as_4340_, v_i_4342_);
v_group_4356_ = lean_ctor_get(v_a_4355_, 0);
v_comb_4357_ = lean_ctor_get(v_a_4355_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_a_4355_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4359_ = v_a_4355_;
v_isShared_4360_ = v_isSharedCheck_4421_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_comb_4357_);
lean_inc(v_group_4356_);
lean_dec(v_a_4355_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4421_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v_toIndGroupInfo_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; 
v_toIndGroupInfo_4361_ = lean_ctor_get(v_group_4356_, 0);
v___x_4362_ = lean_box(0);
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4361_, v___x_4363_);
v___x_4365_ = lean_box(v___x_4349_);
lean_inc_ref(v_comb_4357_);
lean_inc_ref(v_k_4336_);
v___f_4366_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4366_, 0, v___x_4364_);
lean_closure_set(v___f_4366_, 1, v___x_4365_);
lean_closure_set(v___f_4366_, 2, v_group_4356_);
lean_closure_set(v___f_4366_, 3, v_k_4336_);
lean_closure_set(v___f_4366_, 4, v_comb_4357_);
v___x_4367_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4366_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4359_);
lean_dec_ref(v_comb_4357_);
lean_dec_ref(v_values_4339_);
lean_dec_ref(v_xs_4338_);
lean_dec_ref(v_k_4336_);
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4379_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4379_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4372_, 0, v_a_4368_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4372_);
v___x_4374_ = v___x_4353_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_snd_4351_);
v___x_4374_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4376_; 
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4374_);
v___x_4376_ = v___x_4370_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4420_; 
v_a_4380_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4382_ = v___x_4367_;
v_isShared_4383_ = v_isSharedCheck_4420_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4367_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4420_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint8_t v___x_4384_; 
v___x_4384_ = l_Lean_Exception_isInterrupt(v_a_4380_);
if (v___x_4384_ == 0)
{
uint8_t v___x_4385_; 
lean_inc(v_a_4380_);
v___x_4385_ = l_Lean_Exception_isRuntime(v_a_4380_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; 
lean_del_object(v___x_4382_);
lean_inc_ref(v_values_4339_);
lean_inc_ref(v_xs_4338_);
v___x_4386_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4337_, v_xs_4338_, v_values_4339_, v_comb_4357_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
v___x_4388_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 7);
lean_ctor_set(v___x_4359_, 1, v_a_4387_);
lean_ctor_set(v___x_4359_, 0, v___x_4388_);
v___x_4390_ = v___x_4359_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_a_4387_);
v___x_4390_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4391_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l_Lean_Exception_toMessageData(v_a_4380_);
v___x_4394_ = l_Lean_indentD(v___x_4393_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4392_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v_snd_4351_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 1, v___x_4398_);
lean_ctor_set(v___x_4353_, 0, v___x_4362_);
v___x_4400_ = v___x_4353_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4362_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
size_t v___x_4401_; size_t v___x_4402_; 
v___x_4401_ = ((size_t)1ULL);
v___x_4402_ = lean_usize_add(v_i_4342_, v___x_4401_);
v_i_4342_ = v___x_4402_;
v_b_4343_ = v___x_4400_;
goto _start;
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec(v_a_4380_);
lean_del_object(v___x_4359_);
lean_del_object(v___x_4353_);
lean_dec(v_snd_4351_);
lean_dec_ref(v_values_4339_);
lean_dec_ref(v_xs_4338_);
lean_dec_ref(v_k_4336_);
v_a_4406_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4386_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4386_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
else
{
lean_object* v___x_4415_; 
lean_del_object(v___x_4359_);
lean_dec_ref(v_comb_4357_);
lean_del_object(v___x_4353_);
lean_dec(v_snd_4351_);
lean_dec_ref(v_values_4339_);
lean_dec_ref(v_xs_4338_);
lean_dec_ref(v_k_4336_);
if (v_isShared_4383_ == 0)
{
v___x_4415_ = v___x_4382_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4380_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
else
{
lean_object* v___x_4418_; 
lean_del_object(v___x_4359_);
lean_dec_ref(v_comb_4357_);
lean_del_object(v___x_4353_);
lean_dec(v_snd_4351_);
lean_dec_ref(v_values_4339_);
lean_dec_ref(v_xs_4338_);
lean_dec_ref(v_k_4336_);
if (v_isShared_4383_ == 0)
{
v___x_4418_ = v___x_4382_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4380_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4424_, lean_object* v_fnNames_4425_, lean_object* v_xs_4426_, lean_object* v_values_4427_, lean_object* v_as_4428_, lean_object* v_sz_4429_, lean_object* v_i_4430_, lean_object* v_b_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
size_t v_sz_boxed_4437_; size_t v_i_boxed_4438_; lean_object* v_res_4439_; 
v_sz_boxed_4437_ = lean_unbox_usize(v_sz_4429_);
lean_dec(v_sz_4429_);
v_i_boxed_4438_ = lean_unbox_usize(v_i_4430_);
lean_dec(v_i_4430_);
v_res_4439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4424_, v_fnNames_4425_, v_xs_4426_, v_values_4427_, v_as_4428_, v_sz_boxed_4437_, v_i_boxed_4438_, v_b_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec_ref(v_as_4428_);
lean_dec_ref(v_fnNames_4425_);
return v_res_4439_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4442_ = l_Lean_stringToMessageData(v___x_4441_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4445_ = l_Lean_stringToMessageData(v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4446_, lean_object* v_xs_4447_, lean_object* v_values_4448_, lean_object* v_candidates_4449_, lean_object* v_k_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_candidates_4456_; lean_object* v_report_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4517_; 
v_candidates_4456_ = lean_ctor_get(v_candidates_4449_, 0);
v_report_4457_ = lean_ctor_get(v_candidates_4449_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_candidates_4449_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4459_ = v_candidates_4449_;
v_isShared_4460_ = v_isSharedCheck_4517_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_report_4457_);
lean_inc(v_candidates_4456_);
lean_dec(v_candidates_4449_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4517_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4461_; lean_object* v___x_4463_; 
v___x_4461_ = lean_box(0);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4461_);
v___x_4463_ = v___x_4459_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4461_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v_report_4457_);
v___x_4463_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
size_t v_sz_4464_; size_t v___x_4465_; lean_object* v___x_4466_; 
v_sz_4464_ = lean_array_size(v_candidates_4456_);
v___x_4465_ = ((size_t)0ULL);
v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4450_, v_fnNames_4446_, v_xs_4447_, v_values_4448_, v_candidates_4456_, v_sz_4464_, v___x_4465_, v___x_4463_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec_ref(v_candidates_4456_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4507_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4507_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4507_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v_fst_4471_; 
v_fst_4471_ = lean_ctor_get(v_a_4467_, 0);
if (lean_obj_tag(v_fst_4471_) == 0)
{
lean_object* v_toCold_4472_; lean_object* v_options_4473_; lean_object* v_snd_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4501_; 
lean_del_object(v___x_4469_);
v_toCold_4472_ = lean_ctor_get(v_a_4453_, 0);
v_options_4473_ = lean_ctor_get(v_toCold_4472_, 2);
v_snd_4474_ = lean_ctor_get(v_a_4467_, 1);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v_a_4467_, 0);
lean_dec(v_unused_4502_);
v___x_4476_ = v_a_4467_;
v_isShared_4477_ = v_isSharedCheck_4501_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_snd_4474_);
lean_dec(v_a_4467_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4501_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v_inheritedTraceOptions_4478_; uint8_t v_hasTrace_4479_; lean_object* v___x_4480_; lean_object* v___x_4482_; 
v_inheritedTraceOptions_4478_ = lean_ctor_get(v_toCold_4472_, 11);
v_hasTrace_4479_ = lean_ctor_get_uint8(v_options_4473_, sizeof(void*)*1);
v___x_4480_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 7);
lean_ctor_set(v___x_4476_, 0, v___x_4480_);
v___x_4482_ = v___x_4476_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_snd_4474_);
v___x_4482_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
if (v_hasTrace_4479_ == 0)
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4482_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4483_;
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4484_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4485_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4478_, v_options_4473_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4482_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4482_);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
lean_ctor_set(v___x_4489_, 1, v___x_4482_);
v___x_4490_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4484_, v___x_4489_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v___x_4491_; 
lean_dec_ref_known(v___x_4490_, 1);
v___x_4491_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4482_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v___x_4482_);
v_a_4492_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4490_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4490_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
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
lean_object* v_val_4503_; lean_object* v___x_4505_; 
lean_inc_ref(v_fst_4471_);
lean_dec(v_a_4467_);
v_val_4503_ = lean_ctor_get(v_fst_4471_, 0);
lean_inc(v_val_4503_);
lean_dec_ref_known(v_fst_4471_, 1);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v_val_4503_);
v___x_4505_ = v___x_4469_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_val_4503_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_a_4508_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4466_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4466_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4518_, lean_object* v_xs_4519_, lean_object* v_values_4520_, lean_object* v_candidates_4521_, lean_object* v_k_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4518_, v_xs_4519_, v_values_4520_, v_candidates_4521_, v_k_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec_ref(v_fnNames_4518_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4529_, lean_object* v_fnNames_4530_, lean_object* v_xs_4531_, lean_object* v_values_4532_, lean_object* v_candidates_4533_, lean_object* v_k_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4530_, v_xs_4531_, v_values_4532_, v_candidates_4533_, v_k_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4541_, lean_object* v_fnNames_4542_, lean_object* v_xs_4543_, lean_object* v_values_4544_, lean_object* v_candidates_4545_, lean_object* v_k_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4541_, v_fnNames_4542_, v_xs_4543_, v_values_4544_, v_candidates_4545_, v_k_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec_ref(v_fnNames_4542_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4553_, lean_object* v_k_4554_, lean_object* v_fnNames_4555_, lean_object* v_xs_4556_, lean_object* v_values_4557_, lean_object* v_as_4558_, size_t v_sz_4559_, size_t v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4554_, v_fnNames_4555_, v_xs_4556_, v_values_4557_, v_as_4558_, v_sz_4559_, v_i_4560_, v_b_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4568_, lean_object* v_k_4569_, lean_object* v_fnNames_4570_, lean_object* v_xs_4571_, lean_object* v_values_4572_, lean_object* v_as_4573_, lean_object* v_sz_4574_, lean_object* v_i_4575_, lean_object* v_b_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
size_t v_sz_boxed_4582_; size_t v_i_boxed_4583_; lean_object* v_res_4584_; 
v_sz_boxed_4582_ = lean_unbox_usize(v_sz_4574_);
lean_dec(v_sz_4574_);
v_i_boxed_4583_ = lean_unbox_usize(v_i_4575_);
lean_dec(v_i_4575_);
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4568_, v_k_4569_, v_fnNames_4570_, v_xs_4571_, v_values_4572_, v_as_4573_, v_sz_boxed_4582_, v_i_boxed_4583_, v_b_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_as_4573_);
lean_dec_ref(v_fnNames_4570_);
return v_res_4584_;
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
