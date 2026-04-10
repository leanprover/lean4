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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Skipping arguments of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", as "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " has no compatible argument.\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Too many possible combinations of parameters of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " (or "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "please indicate the recursive argument explicitly using `termination_by structural`).\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_36_);
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
lean_object* v_recArgPos_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_recArgPos_152_ = lean_ctor_get(v_recArgInfo_143_, 2);
v___x_153_ = l_Array_append___redArg(v_xs_144_, v_ys_145_);
v___x_154_ = l_Lean_Elab_Structural_prettyParam(v___x_153_, v_recArgPos_152_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec_ref(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object* v_recArgInfo_155_, lean_object* v_xs_156_, lean_object* v_ys_157_, lean_object* v_x_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_155_, v_xs_156_, v_ys_157_, v_x_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v_ys_157_);
lean_dec_ref(v_recArgInfo_155_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object* v_xs_165_, lean_object* v_value_166_, lean_object* v_recArgInfo_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___f_173_; uint8_t v___x_174_; lean_object* v___x_175_; 
v___f_173_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_173_, 0, v_recArgInfo_167_);
lean_closure_set(v___f_173_, 1, v_xs_165_);
v___x_174_ = 0;
v___x_175_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_166_, v___f_173_, v___x_174_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object* v_xs_176_, lean_object* v_value_177_, lean_object* v_recArgInfo_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_176_, v_value_177_, v_recArgInfo_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0));
v___x_187_ = l_Lean_stringToMessageData(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object* v_xs_188_, lean_object* v_as_189_, size_t v_sz_190_, size_t v_i_191_, lean_object* v_b_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_lt(v_i_191_, v_sz_190_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v_xs_188_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v_b_192_);
return v___x_199_;
}
else
{
lean_object* v_snd_200_; lean_object* v_snd_201_; lean_object* v_fst_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_284_; 
v_snd_200_ = lean_ctor_get(v_b_192_, 1);
lean_inc(v_snd_200_);
v_snd_201_ = lean_ctor_get(v_snd_200_, 1);
lean_inc(v_snd_201_);
v_fst_202_ = lean_ctor_get(v_b_192_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_b_192_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_b_192_, 1);
lean_dec(v_unused_285_);
v___x_204_ = v_b_192_;
v_isShared_205_ = v_isSharedCheck_284_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_fst_202_);
lean_dec(v_b_192_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_284_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_fst_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_282_; 
v_fst_206_ = lean_ctor_get(v_snd_200_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_snd_200_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v_snd_200_, 1);
lean_dec(v_unused_283_);
v___x_208_ = v_snd_200_;
v_isShared_209_ = v_isSharedCheck_282_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_fst_206_);
lean_dec(v_snd_200_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_282_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_array_210_; lean_object* v_start_211_; lean_object* v_stop_212_; uint8_t v___x_213_; 
v_array_210_ = lean_ctor_get(v_snd_201_, 0);
v_start_211_ = lean_ctor_get(v_snd_201_, 1);
v_stop_212_ = lean_ctor_get(v_snd_201_, 2);
v___x_213_ = lean_nat_dec_lt(v_start_211_, v_stop_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v_xs_188_);
if (v_isShared_209_ == 0)
{
v___x_215_ = v___x_208_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_201_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_215_);
v___x_217_ = v___x_204_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_fst_202_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
else
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_278_; 
lean_inc(v_stop_212_);
lean_inc(v_start_211_);
lean_inc_ref(v_array_210_);
v_isSharedCheck_278_ = !lean_is_exclusive(v_snd_201_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_279_ = lean_ctor_get(v_snd_201_, 2);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_snd_201_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_snd_201_, 0);
lean_dec(v_unused_281_);
v___x_222_ = v_snd_201_;
v_isShared_223_ = v_isSharedCheck_278_;
goto v_resetjp_221_;
}
else
{
lean_dec(v_snd_201_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_278_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_array_224_; lean_object* v_start_225_; lean_object* v_stop_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v_array_224_ = lean_ctor_get(v_fst_206_, 0);
v_start_225_ = lean_ctor_get(v_fst_206_, 1);
v_stop_226_ = lean_ctor_get(v_fst_206_, 2);
v___x_227_ = lean_array_fget(v_array_210_, v_start_211_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_start_211_, v___x_228_);
lean_dec(v_start_211_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_229_);
v___x_231_ = v___x_222_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_array_210_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_stop_212_);
v___x_231_ = v_reuseFailAlloc_277_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
uint8_t v___x_232_; 
v___x_232_ = lean_nat_dec_lt(v_start_225_, v_stop_226_);
if (v___x_232_ == 0)
{
lean_object* v___x_234_; 
lean_dec(v___x_227_);
lean_dec_ref(v_xs_188_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_231_);
v___x_234_ = v___x_208_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_231_);
v___x_234_ = v_reuseFailAlloc_239_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_234_);
v___x_236_ = v___x_204_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_fst_202_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
else
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_273_; 
lean_inc(v_stop_226_);
lean_inc(v_start_225_);
lean_inc_ref(v_array_224_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_fst_206_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_274_ = lean_ctor_get(v_fst_206_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_fst_206_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_fst_206_, 0);
lean_dec(v_unused_276_);
v___x_241_ = v_fst_206_;
v_isShared_242_ = v_isSharedCheck_273_;
goto v_resetjp_240_;
}
else
{
lean_dec(v_fst_206_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_273_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_array_fget_borrowed(v_array_224_, v_start_225_);
lean_inc(v___x_243_);
lean_inc_ref(v_xs_188_);
v___x_244_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_188_, v___x_243_, v___x_227_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
v_a_246_ = lean_array_uget_borrowed(v_as_189_, v_i_191_);
v___x_247_ = lean_nat_add(v_start_225_, v___x_228_);
lean_dec(v_start_225_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_247_);
v___x_249_ = v___x_241_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_array_224_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_stop_226_);
v___x_249_ = v_reuseFailAlloc_264_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_250_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v_a_245_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc(v_a_246_);
v___x_252_ = l_Lean_MessageData_ofName(v_a_246_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_array_push(v_fst_202_, v___x_253_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_231_);
lean_ctor_set(v___x_208_, 0, v___x_249_);
v___x_256_ = v___x_208_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_231_);
v___x_256_ = v_reuseFailAlloc_263_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_256_);
lean_ctor_set(v___x_204_, 0, v___x_254_);
v___x_258_ = v___x_204_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
size_t v___x_259_; size_t v___x_260_; 
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_add(v_i_191_, v___x_259_);
v_i_191_ = v___x_260_;
v_b_192_ = v___x_258_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_del_object(v___x_241_);
lean_dec_ref(v___x_231_);
lean_dec(v_stop_226_);
lean_dec(v_start_225_);
lean_dec_ref(v_array_224_);
lean_del_object(v___x_208_);
lean_del_object(v___x_204_);
lean_dec(v_fst_202_);
lean_dec_ref(v_xs_188_);
v_a_265_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_244_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_244_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object* v_xs_286_, lean_object* v_as_287_, lean_object* v_sz_288_, lean_object* v_i_289_, lean_object* v_b_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
size_t v_sz_boxed_296_; size_t v_i_boxed_297_; lean_object* v_res_298_; 
v_sz_boxed_296_ = lean_unbox_usize(v_sz_288_);
lean_dec(v_sz_288_);
v_i_boxed_297_ = lean_unbox_usize(v_i_289_);
lean_dec(v_i_289_);
v_res_298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_286_, v_as_287_, v_sz_boxed_296_, v_i_boxed_297_, v_b_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec_ref(v_as_287_);
return v_res_298_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__1));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__3));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object* v_fnNames_307_, lean_object* v_xs_308_, lean_object* v_values_309_, lean_object* v_recArgInfos_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_array_get_size(v_fnNames_307_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_dec_eq(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v_l_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; size_t v_sz_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v_l_320_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_321_ = lean_array_get_size(v_values_309_);
v___x_322_ = l_Array_toSubarray___redArg(v_values_309_, v___x_319_, v___x_321_);
v___x_323_ = lean_array_get_size(v_recArgInfos_310_);
v___x_324_ = l_Array_toSubarray___redArg(v_recArgInfos_310_, v___x_319_, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_322_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_l_320_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v_sz_327_ = lean_array_size(v_fnNames_307_);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_308_, v_fnNames_307_, v_sz_327_, v___x_328_, v___x_326_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_349_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_349_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_349_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_349_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fst_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_347_; 
v_fst_334_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_a_330_, 1);
lean_dec(v_unused_348_);
v___x_336_ = v_a_330_;
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_fst_334_);
lean_dec(v_a_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_338_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__2, &l_Lean_Elab_Structural_prettyParameterSet___closed__2_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2);
v___x_339_ = lean_array_to_list(v_fst_334_);
v___x_340_ = l_Lean_MessageData_andList(v___x_339_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 7);
lean_ctor_set(v___x_336_, 1, v___x_340_);
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_342_ = v___x_336_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_342_);
v___x_344_ = v___x_332_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_329_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_329_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_358_ = l_Lean_instInhabitedExpr;
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get(v___x_358_, v_values_309_, v___x_359_);
lean_dec_ref(v_values_309_);
v___x_361_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_362_ = lean_array_get(v___x_361_, v_recArgInfos_310_, v___x_359_);
lean_dec_ref(v_recArgInfos_310_);
v___x_363_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_308_, v___x_360_, v___x_362_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__4, &l_Lean_Elab_Structural_prettyParameterSet___closed__4_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_a_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object* v_fnNames_374_, lean_object* v_xs_375_, lean_object* v_values_376_, lean_object* v_recArgInfos_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_374_, v_xs_375_, v_values_376_, v_recArgInfos_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec_ref(v_fnNames_374_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object* v_xs_384_, lean_object* v_v_385_, lean_object* v_i_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = lean_array_get_size(v_xs_384_);
v___x_388_ = lean_nat_dec_lt(v_i_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v_i_386_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_fget_borrowed(v_xs_384_, v_i_386_);
v___x_391_ = lean_expr_eqv(v___x_390_, v_v_385_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_i_386_, v___x_392_);
lean_dec(v_i_386_);
v_i_386_ = v___x_393_;
goto _start;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_i_386_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_396_, lean_object* v_v_397_, lean_object* v_i_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_396_, v_v_397_, v_i_398_);
lean_dec_ref(v_v_397_);
lean_dec_ref(v_xs_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object* v_xs_400_, lean_object* v_v_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_400_, v_v_401_, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object* v_xs_404_, lean_object* v_v_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_404_, v_v_405_);
lean_dec_ref(v_v_405_);
lean_dec_ref(v_xs_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object* v_xs_407_, lean_object* v_v_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_407_, v_v_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_val_411_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_409_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_val_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object* v_xs_419_, lean_object* v_v_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_419_, v_v_420_);
lean_dec_ref(v_v_420_);
lean_dec_ref(v_xs_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object* v_xs_422_, lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_a_428_; uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_432_ == 0)
{
return v_b_426_;
}
else
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
v___x_434_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_422_, v_a_433_);
if (lean_obj_tag(v___x_434_) == 1)
{
lean_object* v_val_435_; uint8_t v___x_436_; 
v_val_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v___x_434_);
v___x_436_ = lean_nat_dec_lt(v_val_435_, v_b_426_);
if (v___x_436_ == 0)
{
lean_dec(v_val_435_);
v_a_428_ = v_b_426_;
goto v___jp_427_;
}
else
{
lean_dec(v_b_426_);
v_a_428_ = v_val_435_;
goto v___jp_427_;
}
}
else
{
lean_dec(v___x_434_);
v_a_428_ = v_b_426_;
goto v___jp_427_;
}
}
v___jp_427_:
{
size_t v___x_429_; size_t v___x_430_; 
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_i_425_, v___x_429_);
v_i_425_ = v___x_430_;
v_b_426_ = v_a_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object* v_xs_437_, lean_object* v_as_438_, lean_object* v_sz_439_, lean_object* v_i_440_, lean_object* v_b_441_){
_start:
{
size_t v_sz_boxed_442_; size_t v_i_boxed_443_; lean_object* v_res_444_; 
v_sz_boxed_442_ = lean_unbox_usize(v_sz_439_);
lean_dec(v_sz_439_);
v_i_boxed_443_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_437_, v_as_438_, v_sz_boxed_442_, v_i_boxed_443_, v_b_441_);
lean_dec_ref(v_as_438_);
lean_dec_ref(v_xs_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object* v_xs_445_, lean_object* v_indices_446_){
_start:
{
lean_object* v_minPos_447_; size_t v_sz_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_minPos_447_ = lean_array_get_size(v_xs_445_);
v_sz_448_ = lean_array_size(v_indices_446_);
v___x_449_ = ((size_t)0ULL);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_445_, v_indices_446_, v_sz_448_, v___x_449_, v_minPos_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* v_xs_451_, lean_object* v_indices_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_451_, v_indices_452_);
lean_dec_ref(v_indices_452_);
lean_dec_ref(v_xs_451_);
return v_res_453_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object* v_x_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_456_);
lean_dec(v_x_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object* v_fvarId_459_, lean_object* v_x_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_instBEqFVarId_beq(v_fvarId_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_462_, lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_fvarId_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_box(0);
v___x_468_ = lean_unsigned_to_nat(16u);
v___x_469_ = lean_mk_array(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_473_, lean_object* v_fvarId_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; uint8_t v_fst_479_; lean_object* v_mctx_480_; lean_object* v___y_498_; lean_object* v_mctx_503_; lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_477_ = lean_st_ref_get(v___y_475_);
v_mctx_503_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref_n(v_mctx_503_, 2);
lean_dec(v___x_477_);
v___f_504_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_505_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_505_, 0, v_fvarId_474_);
v___x_506_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_mctx_503_);
v___x_508_ = l_Lean_Expr_hasFVar(v_e_473_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = l_Lean_Expr_hasMVar(v_e_473_);
if (v___x_509_ == 0)
{
lean_dec_ref(v___x_507_);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_e_473_);
v_fst_479_ = v___x_509_;
v_mctx_480_ = v_mctx_503_;
goto v___jp_478_;
}
else
{
lean_object* v___x_510_; 
lean_dec_ref(v_mctx_503_);
v___x_510_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_505_, v___f_504_, v_e_473_, v___x_507_);
v___y_498_ = v___x_510_;
goto v___jp_497_;
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_mctx_503_);
v___x_511_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_505_, v___f_504_, v_e_473_, v___x_507_);
v___y_498_ = v___x_511_;
goto v___jp_497_;
}
v___jp_478_:
{
lean_object* v___x_481_; lean_object* v_cache_482_; lean_object* v_zetaDeltaFVarIds_483_; lean_object* v_postponed_484_; lean_object* v_diag_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_495_; 
v___x_481_ = lean_st_ref_take(v___y_475_);
v_cache_482_ = lean_ctor_get(v___x_481_, 1);
v_zetaDeltaFVarIds_483_ = lean_ctor_get(v___x_481_, 2);
v_postponed_484_ = lean_ctor_get(v___x_481_, 3);
v_diag_485_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v___x_481_, 0);
lean_dec(v_unused_496_);
v___x_487_ = v___x_481_;
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_diag_485_);
lean_inc(v_postponed_484_);
lean_inc(v_zetaDeltaFVarIds_483_);
lean_inc(v_cache_482_);
lean_dec(v___x_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_mctx_480_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_mctx_480_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_cache_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_zetaDeltaFVarIds_483_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_postponed_484_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_diag_485_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_st_ref_set(v___y_475_, v___x_490_);
v___x_492_ = lean_box(v_fst_479_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
}
v___jp_497_:
{
lean_object* v_snd_499_; lean_object* v_fst_500_; lean_object* v_mctx_501_; uint8_t v___x_502_; 
v_snd_499_ = lean_ctor_get(v___y_498_, 1);
lean_inc(v_snd_499_);
v_fst_500_ = lean_ctor_get(v___y_498_, 0);
lean_inc(v_fst_500_);
lean_dec_ref(v___y_498_);
v_mctx_501_ = lean_ctor_get(v_snd_499_, 1);
lean_inc_ref(v_mctx_501_);
lean_dec(v_snd_499_);
v___x_502_ = lean_unbox(v_fst_500_);
lean_dec(v_fst_500_);
v_fst_479_ = v___x_502_;
v_mctx_480_ = v_mctx_501_;
goto v___jp_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_512_, lean_object* v_fvarId_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_512_, v_fvarId_513_, v___y_514_);
lean_dec(v___y_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_517_, lean_object* v_fvarId_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_517_, v_fvarId_518_, v___y_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_525_, lean_object* v_fvarId_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_525_, v_fvarId_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_533_, lean_object* v_as_534_, size_t v_i_535_, size_t v_stop_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_usize_dec_eq(v_i_535_, v_stop_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_uget_borrowed(v_as_534_, v_i_535_);
v___x_539_ = lean_expr_eqv(v_a_533_, v___x_538_);
if (v___x_539_ == 0)
{
size_t v___x_540_; size_t v___x_541_; 
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_535_, v___x_540_);
v_i_535_ = v___x_541_;
goto _start;
}
else
{
return v___x_539_;
}
}
else
{
uint8_t v___x_543_; 
v___x_543_ = 0;
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_544_, lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_stop_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; uint8_t v_res_550_; lean_object* v_r_551_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_547_);
lean_dec(v_stop_547_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_544_, v_as_545_, v_i_boxed_548_, v_stop_boxed_549_);
lean_dec_ref(v_as_545_);
lean_dec_ref(v_a_544_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v_as_552_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_555_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_553_, v_as_552_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_560_, lean_object* v_a_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_560_, v_a_561_);
lean_dec_ref(v_a_561_);
lean_dec_ref(v_as_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_567_, lean_object* v_indices_568_, lean_object* v_a_569_, lean_object* v_as_570_, size_t v_sz_571_, size_t v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_lt(v_i_572_, v_sz_571_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_dec_ref(v_a_569_);
lean_dec_ref(v_a_567_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v_b_573_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_b_573_);
v_a_581_ = lean_array_uget_borrowed(v_as_570_, v_i_572_);
v___x_582_ = l_Lean_Expr_fvarId_x21(v_a_581_);
lean_inc_ref(v_a_567_);
v___x_583_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_567_, v___x_582_, v___y_575_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_a_589_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_box(0);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_595_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_568_, v_a_581_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_596_ == 0)
{
lean_del_object(v___x_586_);
v_a_589_ = v___x_594_;
goto v___jp_588_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec_ref(v_a_567_);
lean_inc(v_a_581_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_a_569_);
lean_ctor_set(v___x_597_, 1, v_a_581_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_593_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_600_);
v___x_602_ = v___x_586_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
v_a_589_ = v___x_594_;
goto v___jp_588_;
}
v___jp_588_:
{
size_t v___x_590_; size_t v___x_591_; 
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_i_572_, v___x_590_);
lean_inc_ref(v_a_589_);
v_i_572_ = v___x_591_;
v_b_573_ = v_a_589_;
goto _start;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_a_569_);
lean_dec_ref(v_a_567_);
v_a_605_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_583_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_583_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_613_, lean_object* v_indices_614_, lean_object* v_a_615_, lean_object* v_as_616_, lean_object* v_sz_617_, lean_object* v_i_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_sz_boxed_625_; size_t v_i_boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_617_);
lean_dec(v_sz_617_);
v_i_boxed_626_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_613_, v_indices_614_, v_a_615_, v_as_616_, v_sz_boxed_625_, v_i_boxed_626_, v_b_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_as_616_);
lean_dec_ref(v_indices_614_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_628_, lean_object* v_indices_629_, lean_object* v_as_630_, size_t v_sz_631_, size_t v_i_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_lt(v_i_632_, v_sz_631_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_b_633_);
return v___x_640_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; 
lean_dec_ref(v_b_633_);
v_a_641_ = lean_array_uget_borrowed(v_as_630_, v_i_632_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v_a_641_);
v___x_642_ = lean_infer_type(v_a_641_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_645_; size_t v_sz_646_; size_t v___x_647_; lean_object* v___x_648_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_646_ = lean_array_size(v_ys_628_);
v___x_647_ = ((size_t)0ULL);
lean_inc(v_a_641_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_643_, v_indices_629_, v_a_641_, v_ys_628_, v_sz_646_, v___x_647_, v___x_645_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_668_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_668_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_fst_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_666_; 
v_fst_653_ = lean_ctor_get(v_a_649_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_a_649_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_a_649_, 1);
lean_dec(v_unused_667_);
v___x_655_ = v_a_649_;
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_fst_653_);
lean_dec(v_a_649_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
if (lean_obj_tag(v_fst_653_) == 0)
{
size_t v___x_657_; size_t v___x_658_; 
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_add(v_i_632_, v___x_657_);
v_i_632_ = v___x_658_;
v_b_633_ = v___x_645_;
goto _start;
}
else
{
lean_object* v___x_661_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_644_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_fst_653_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_644_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_661_);
v___x_663_ = v___x_651_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
else
{
return v___x_648_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_642_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_642_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_677_, lean_object* v_indices_678_, lean_object* v_as_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
size_t v_sz_boxed_688_; size_t v_i_boxed_689_; lean_object* v_res_690_; 
v_sz_boxed_688_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_689_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_677_, v_indices_678_, v_as_679_, v_sz_boxed_688_, v_i_boxed_689_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v_as_679_);
lean_dec_ref(v_indices_678_);
lean_dec_ref(v_ys_677_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_691_, lean_object* v_ys_692_, lean_object* v_as_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_b_696_);
return v___x_703_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_705_; 
lean_dec_ref(v_b_696_);
v_a_704_ = lean_array_uget_borrowed(v_as_693_, v_i_695_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v_a_704_);
v___x_705_ = lean_infer_type(v_a_704_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; size_t v_sz_709_; size_t v___x_710_; lean_object* v___x_711_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = lean_box(0);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_709_ = lean_array_size(v_ys_692_);
v___x_710_ = ((size_t)0ULL);
lean_inc(v_a_704_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_706_, v_indices_691_, v_a_704_, v_ys_692_, v_sz_709_, v___x_710_, v___x_708_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_731_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_731_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_731_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_731_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_fst_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_729_; 
v_fst_716_ = lean_ctor_get(v_a_712_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_a_712_, 1);
lean_dec(v_unused_730_);
v___x_718_ = v_a_712_;
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_fst_716_);
lean_dec(v_a_712_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
if (lean_obj_tag(v_fst_716_) == 0)
{
size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
lean_del_object(v___x_718_);
lean_del_object(v___x_714_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_695_, v___x_720_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_692_, v_indices_691_, v_as_693_, v_sz_694_, v___x_721_, v___x_708_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_722_;
}
else
{
lean_object* v___x_724_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_707_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_707_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_724_);
v___x_726_ = v___x_714_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
else
{
return v___x_711_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_705_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_705_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_740_, lean_object* v_ys_741_, lean_object* v_as_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
size_t v_sz_boxed_751_; size_t v_i_boxed_752_; lean_object* v_res_753_; 
v_sz_boxed_751_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_752_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_740_, v_ys_741_, v_as_742_, v_sz_boxed_751_, v_i_boxed_752_, v_b_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_as_742_);
lean_dec_ref(v_ys_741_);
lean_dec_ref(v_indices_740_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_754_, lean_object* v_indices_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; size_t v_sz_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_761_ = lean_box(0);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_763_ = lean_array_size(v_indices_755_);
v___x_764_ = ((size_t)0ULL);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_755_, v_ys_754_, v_indices_755_, v_sz_763_, v___x_764_, v___x_762_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_778_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_778_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_778_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_fst_770_; 
v_fst_770_ = lean_ctor_get(v_a_766_, 0);
lean_inc(v_fst_770_);
lean_dec(v_a_766_);
if (lean_obj_tag(v_fst_770_) == 0)
{
lean_object* v___x_772_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_761_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_761_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v_val_774_; lean_object* v___x_776_; 
v_val_774_ = lean_ctor_get(v_fst_770_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v_fst_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_val_774_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_val_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_765_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_765_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_787_, lean_object* v_indices_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_787_, v_indices_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec_ref(v_indices_788_);
lean_dec_ref(v_ys_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_795_, lean_object* v_as_796_, size_t v_sz_797_, size_t v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_lt(v_i_798_, v_sz_797_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_a_795_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_b_799_);
return v___x_803_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_b_799_);
v_a_804_ = lean_array_uget_borrowed(v_as_796_, v_i_798_);
v___x_805_ = l_Lean_Expr_fvarId_x21(v_a_804_);
lean_inc_ref(v_a_795_);
v___x_806_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_795_, v___x_805_, v___y_800_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; size_t v___x_814_; size_t v___x_815_; 
lean_del_object(v___x_809_);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_798_, v___x_814_);
v_i_798_ = v___x_815_;
v_b_799_ = v___x_813_;
goto _start;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc(v_a_804_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_a_795_);
lean_ctor_set(v___x_817_, 1, v_a_804_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_811_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_820_);
v___x_822_ = v___x_809_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_a_795_);
v_a_825_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_806_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_806_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_833_, lean_object* v_as_834_, lean_object* v_sz_835_, lean_object* v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
size_t v_sz_boxed_840_; size_t v_i_boxed_841_; lean_object* v_res_842_; 
v_sz_boxed_840_ = lean_unbox_usize(v_sz_835_);
lean_dec(v_sz_835_);
v_i_boxed_841_ = lean_unbox_usize(v_i_836_);
lean_dec(v_i_836_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_833_, v_as_834_, v_sz_boxed_840_, v_i_boxed_841_, v_b_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v_as_834_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_843_, lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_847_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_a_857_; size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v_b_847_);
v___x_855_ = lean_box(0);
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_857_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
v_sz_858_ = lean_array_size(v_ys_843_);
v___x_859_ = ((size_t)0ULL);
lean_inc(v_a_857_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_857_, v_ys_843_, v_sz_858_, v___x_859_, v___x_856_, v___y_849_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_880_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_880_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_fst_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_878_; 
v_fst_865_ = lean_ctor_get(v_a_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_a_861_, 1);
lean_dec(v_unused_879_);
v___x_867_ = v_a_861_;
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_fst_865_);
lean_dec(v_a_861_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
if (lean_obj_tag(v_fst_865_) == 0)
{
size_t v___x_869_; size_t v___x_870_; 
lean_del_object(v___x_867_);
lean_del_object(v___x_863_);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_846_, v___x_869_);
v_i_846_ = v___x_870_;
v_b_847_ = v___x_856_;
goto _start;
}
else
{
lean_object* v___x_873_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_855_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_fst_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_855_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_873_);
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
else
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_881_, lean_object* v_as_882_, lean_object* v_sz_883_, lean_object* v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
size_t v_sz_boxed_891_; size_t v_i_boxed_892_; lean_object* v_res_893_; 
v_sz_boxed_891_ = lean_unbox_usize(v_sz_883_);
lean_dec(v_sz_883_);
v_i_boxed_892_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_881_, v_as_882_, v_sz_boxed_891_, v_i_boxed_892_, v_b_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_as_882_);
lean_dec_ref(v_ys_881_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_894_, lean_object* v_indParams_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; size_t v_sz_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_901_ = lean_box(0);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_903_ = lean_array_size(v_indParams_895_);
v___x_904_ = ((size_t)0ULL);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_894_, v_indParams_895_, v_sz_903_, v___x_904_, v___x_902_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_918_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_918_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_fst_910_; 
v_fst_910_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_fst_910_);
lean_dec(v_a_906_);
if (lean_obj_tag(v_fst_910_) == 0)
{
lean_object* v___x_912_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_901_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_901_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v_val_914_; lean_object* v___x_916_; 
v_val_914_ = lean_ctor_get(v_fst_910_, 0);
lean_inc(v_val_914_);
lean_dec_ref(v_fst_910_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v_val_914_);
v___x_916_ = v___x_908_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_val_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_905_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_905_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_927_, lean_object* v_indParams_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_927_, v_indParams_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec_ref(v_indParams_928_);
lean_dec_ref(v_ys_927_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_935_, lean_object* v_as_936_, size_t v_sz_937_, size_t v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_935_, v_as_936_, v_sz_937_, v_i_938_, v_b_939_, v___y_941_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_946_, lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_957_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_946_, v_as_947_, v_sz_boxed_956_, v_i_boxed_957_, v_b_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_as_947_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_panic_fn_borrowed(v___x_960_, v_msg_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_6886__overap_970_; lean_object* v___x_971_; 
v___f_969_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6886__overap_970_ = lean_panic_fn_borrowed(v___f_969_, v_msg_963_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
v___x_971_ = lean_apply_5(v___x_6886__overap_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, lean_box(0));
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_msg_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_ref_985_; lean_object* v___x_986_; lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_ref_985_ = lean_ctor_get(v___y_982_, 5);
v___x_986_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_inc(v_ref_985_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_ref_985_);
lean_ctor_set(v___x_991_, 1, v_a_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 1);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_1007_ = lean_unsigned_to_nat(107u);
v___x_1008_ = lean_unsigned_to_nat(96u);
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1011_ = l_mkPanicMessageWithDecl(v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_, v___x_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1012_, size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_bs_1015_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1016_ == 0)
{
return v_bs_1015_;
}
else
{
lean_object* v_v_1017_; lean_object* v___x_1018_; lean_object* v_bs_x27_1019_; lean_object* v___y_1021_; lean_object* v___x_1026_; 
v_v_1017_ = lean_array_uget(v_bs_1015_, v_i_1014_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v_bs_x27_1019_ = lean_array_uset(v_bs_1015_, v_i_1014_, v___x_1018_);
v___x_1026_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_1012_, v_v_1017_);
lean_dec(v_v_1017_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3);
v___x_1028_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1027_);
v___y_1021_ = v___x_1028_;
goto v___jp_1020_;
}
else
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1029_);
lean_dec_ref(v___x_1026_);
v___y_1021_ = v_val_1029_;
goto v___jp_1020_;
}
v___jp_1020_:
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1014_, v___x_1022_);
v___x_1024_ = lean_array_uset(v_bs_x27_1019_, v_i_1014_, v___y_1021_);
v_i_1014_ = v___x_1023_;
v_bs_1015_ = v___x_1024_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1030_, lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_bs_1033_){
_start:
{
size_t v_sz_boxed_1034_; size_t v_i_boxed_1035_; lean_object* v_res_1036_; 
v_sz_boxed_1034_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1035_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1030_, v_sz_boxed_1034_, v_i_boxed_1035_, v_bs_1033_);
lean_dec_ref(v_xs_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(lean_object* v_as_1037_, lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v_zero_1040_; uint8_t v_isZero_1041_; 
v_zero_1040_ = lean_unsigned_to_nat(0u);
v_isZero_1041_ = lean_nat_dec_eq(v_x_1039_, v_zero_1040_);
if (v_isZero_1041_ == 1)
{
lean_dec(v_x_1039_);
return v_isZero_1041_;
}
else
{
lean_object* v_one_1042_; lean_object* v_n_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_one_1042_ = lean_unsigned_to_nat(1u);
v_n_1043_ = lean_nat_sub(v_x_1039_, v_one_1042_);
lean_dec(v_x_1039_);
v___x_1044_ = lean_array_fget_borrowed(v_as_1037_, v_n_1043_);
v___x_1045_ = lean_expr_eqv(v_a_1038_, v___x_1044_);
if (v___x_1045_ == 0)
{
v_x_1039_ = v_n_1043_;
goto _start;
}
else
{
lean_dec(v_n_1043_);
return v_isZero_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_as_1047_, lean_object* v_a_1048_, lean_object* v_x_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1047_, v_a_1048_, v_x_1049_);
lean_dec_ref(v_a_1048_);
lean_dec_ref(v_as_1047_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(lean_object* v_as_1052_, lean_object* v_i_1053_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_array_get_size(v_as_1052_);
v___x_1055_ = lean_nat_dec_lt(v_i_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; 
lean_dec(v_i_1053_);
v___x_1056_ = 1;
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_array_fget_borrowed(v_as_1052_, v_i_1053_);
lean_inc(v_i_1053_);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1052_, v___x_1057_, v_i_1053_);
if (v___x_1058_ == 0)
{
lean_dec(v_i_1053_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_i_1053_, v___x_1059_);
lean_dec(v_i_1053_);
v_i_1053_ = v___x_1060_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(lean_object* v_as_1062_, lean_object* v_i_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1062_, v_i_1063_);
lean_dec_ref(v_as_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_as_1066_){
_start:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1066_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_as_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_as_1069_);
lean_dec_ref(v_as_1069_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_as_1072_, size_t v_i_1073_, size_t v_stop_1074_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_eq(v_i_1073_, v_stop_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = 1;
v___x_1077_ = lean_array_uget_borrowed(v_as_1072_, v_i_1073_);
v___x_1078_ = l_Lean_Expr_isFVar(v___x_1077_);
if (v___x_1078_ == 0)
{
return v___x_1076_;
}
else
{
if (v___x_1075_ == 0)
{
size_t v___x_1079_; size_t v___x_1080_; 
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1073_, v___x_1079_);
v_i_1073_ = v___x_1080_;
goto _start;
}
else
{
return v___x_1076_;
}
}
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = 0;
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_as_1083_, lean_object* v_i_1084_, lean_object* v_stop_1085_){
_start:
{
size_t v_i_boxed_1086_; size_t v_stop_boxed_1087_; uint8_t v_res_1088_; lean_object* v_r_1089_; 
v_i_boxed_1086_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_stop_boxed_1087_ = lean_unbox_usize(v_stop_1085_);
lean_dec(v_stop_1085_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_as_1083_, v_i_boxed_1086_, v_stop_boxed_1087_);
lean_dec_ref(v_as_1083_);
v_r_1089_ = lean_box(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(lean_object* v_xs_1090_, lean_object* v_v_1091_, lean_object* v_i_1092_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_array_get_size(v_xs_1090_);
v___x_1094_ = lean_nat_dec_lt(v_i_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_i_1092_);
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_array_fget_borrowed(v_xs_1090_, v_i_1092_);
v___x_1097_ = lean_name_eq(v___x_1096_, v_v_1091_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_i_1092_, v___x_1098_);
lean_dec(v_i_1092_);
v_i_1092_ = v___x_1099_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_i_1092_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(lean_object* v_xs_1102_, lean_object* v_v_1103_, lean_object* v_i_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1102_, v_v_1103_, v_i_1104_);
lean_dec(v_v_1103_);
lean_dec_ref(v_xs_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(lean_object* v_xs_1106_, lean_object* v_v_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1106_, v_v_1107_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(lean_object* v_xs_1110_, lean_object* v_v_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1110_, v_v_1111_);
lean_dec(v_v_1111_);
lean_dec_ref(v_xs_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_xs_1113_, lean_object* v_v_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1113_, v_v_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_val_1117_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_val_1117_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_val_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_xs_1125_, lean_object* v_v_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_xs_1125_, v_v_1126_);
lean_dec(v_v_1126_);
lean_dec_ref(v_xs_1125_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1130_ = l_Lean_stringToMessageData(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1139_ = lean_unsigned_to_nat(59u);
v___x_1140_ = lean_unsigned_to_nat(95u);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1143_ = l_mkPanicMessageWithDecl(v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1168_; lean_object* v_dummy_1169_; 
v___x_1168_ = lean_box(0);
v_dummy_1169_ = l_Lean_Expr_sort___override(v___x_1168_);
return v_dummy_1169_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1175_ = lean_unsigned_to_nat(2u);
v___x_1176_ = lean_unsigned_to_nat(67u);
v___x_1177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1179_ = l_mkPanicMessageWithDecl(v___x_1178_, v___x_1177_, v___x_1176_, v___x_1175_, v___x_1174_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1192_, lean_object* v_fixedParamPerm_1193_, lean_object* v_xs_1194_, lean_object* v_i_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v_lower_1340_; lean_object* v_upper_1341_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_array_get_size(v_fixedParamPerm_1193_);
v___x_1427_ = lean_array_get_size(v_xs_1194_);
v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1429_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1430_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1429_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
return v___x_1430_;
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_lt(v_i_1195_, v___x_1427_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1432_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_nat_add(v_i_1195_, v___x_1433_);
lean_dec(v_i_1195_);
v___x_1435_ = l_Nat_reprFast(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = l_Lean_MessageData_ofFormat(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1432_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Nat_reprFast(v___x_1427_);
v___x_1442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = l_Lean_MessageData_ofFormat(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1446_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
return v___x_1447_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1193_, v_i_1195_);
if (v___x_1448_ == 0)
{
v___y_1399_ = v_a_1196_;
v___y_1400_ = v_a_1197_;
v___y_1401_ = v_a_1198_;
v___y_1402_ = v_a_1199_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1449_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1450_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1449_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
v___jp_1201_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1207_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1206_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
v___jp_1208_:
{
uint8_t v___x_1220_; 
v___x_1220_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1216_);
if (v___x_1220_ == 0)
{
lean_object* v_name_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1221_ = lean_ctor_get(v___y_1212_, 0);
lean_inc(v_name_1221_);
lean_dec_ref(v___y_1212_);
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1223_ = l_Lean_MessageData_ofName(v_name_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_indentExpr(v___y_1210_);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1228_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1193_, v_xs_1194_);
v___x_1231_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1230_, v___y_1216_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1230_, v___y_1215_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
lean_dec_ref(v___x_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1284_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1284_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1284_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
if (lean_obj_tag(v_a_1234_) == 0)
{
lean_object* v_name_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v___y_1210_);
v_name_1238_ = lean_ctor_get(v___y_1212_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___y_1212_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v___y_1212_, 2);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v___y_1212_, 1);
lean_dec(v_unused_1260_);
v___x_1240_ = v___y_1212_;
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_name_1238_);
lean_dec(v___y_1212_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_array_mk(v___y_1218_);
v___x_1243_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___x_1242_, v_name_1238_);
lean_dec(v_name_1238_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1243_);
v_sz_1245_ = lean_array_size(v___y_1216_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1194_, v_sz_1245_, v___x_1246_, v___y_1216_);
v___x_1248_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1217_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 2, v___y_1215_);
lean_ctor_set(v___x_1240_, 1, v___y_1209_);
lean_ctor_set(v___x_1240_, 0, v___x_1248_);
v___x_1250_ = v___x_1240_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___y_1209_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___y_1215_);
v___x_1250_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1251_, 0, v_fnName_1192_);
lean_ctor_set(v___x_1251_, 1, v_fixedParamPerm_1193_);
lean_ctor_set(v___x_1251_, 2, v_i_1195_);
lean_ctor_set(v___x_1251_, 3, v___x_1247_);
lean_ctor_set(v___x_1251_, 4, v___x_1250_);
lean_ctor_set(v___x_1251_, 5, v_val_1244_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1251_);
v___x_1253_ = v___x_1236_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec(v___x_1243_);
lean_del_object(v___x_1240_);
lean_del_object(v___x_1236_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1256_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1257_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1256_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
return v___x_1257_;
}
}
}
else
{
lean_object* v_val_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1236_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_val_1261_ = lean_ctor_get(v_a_1234_, 0);
lean_inc(v_val_1261_);
lean_dec_ref(v_a_1234_);
v_fst_1262_ = lean_ctor_get(v_val_1261_, 0);
v_snd_1263_ = lean_ctor_get(v_val_1261_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_val_1261_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1265_ = v_val_1261_;
v_isShared_1266_ = v_isSharedCheck_1283_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1263_);
lean_inc(v_fst_1262_);
lean_dec(v_val_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1283_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1267_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1268_ = l_Lean_indentExpr(v___y_1210_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 7);
lean_ctor_set(v___x_1265_, 1, v___x_1268_);
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1271_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_indentExpr(v_fst_1262_);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_indentExpr(v_snd_1263_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1280_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_a_1285_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1233_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1233_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_val_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v___x_1230_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_val_1293_ = lean_ctor_get(v_a_1232_, 0);
lean_inc(v_val_1293_);
lean_dec_ref(v_a_1232_);
v_fst_1294_ = lean_ctor_get(v_val_1293_, 0);
v_snd_1295_ = lean_ctor_get(v_val_1293_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_val_1293_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1297_ = v_val_1293_;
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_val_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_name_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v_name_1299_ = lean_ctor_get(v___y_1212_, 0);
lean_inc(v_name_1299_);
lean_dec_ref(v___y_1212_);
v___x_1300_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1301_ = l_Lean_MessageData_ofName(v_name_1299_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 7);
lean_ctor_set(v___x_1297_, 1, v___x_1301_);
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1303_ = v___x_1297_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1304_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = l_Lean_indentExpr(v___y_1210_);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Lean_indentExpr(v_fst_1294_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_indentExpr(v_snd_1295_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1315_, v___y_1213_, v___y_1219_, v___y_1211_, v___y_1214_);
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___x_1230_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_a_1319_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1231_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1231_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = l_Array_toSubarray___redArg(v___y_1330_, v_lower_1340_, v_upper_1341_);
v___x_1343_ = l_Subarray_copy___redArg(v___x_1342_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_nat_dec_lt(v___y_1329_, v___x_1344_);
lean_dec(v___y_1329_);
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1331_;
v___y_1211_ = v___y_1332_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1337_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1331_;
v___y_1211_ = v___y_1332_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1337_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
size_t v___x_1346_; size_t v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lean_usize_of_nat(v___x_1344_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v___x_1343_, v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1331_;
v___y_1211_ = v___y_1332_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1337_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
lean_object* v_name_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1343_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1328_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1349_ = lean_ctor_get(v___y_1333_, 0);
lean_inc(v_name_1349_);
lean_dec_ref(v___y_1333_);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1351_ = l_Lean_MessageData_ofName(v_name_1349_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_indentExpr(v___y_1331_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1356_, v___y_1334_, v___y_1339_, v___y_1332_, v___y_1335_);
return v___x_1357_;
}
}
}
}
v___jp_1358_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = l_Lean_LocalDecl_type(v___y_1359_);
lean_dec_ref(v___y_1359_);
v___x_1365_ = l_Lean_Meta_whnfD(v___x_1364_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l_Lean_Expr_getAppFn(v_a_1366_);
if (lean_obj_tag(v___x_1367_) == 4)
{
lean_object* v_declName_1368_; lean_object* v_us_1369_; lean_object* v___x_1370_; lean_object* v_env_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
v_declName_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_declName_1368_);
v_us_1369_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_us_1369_);
lean_dec_ref(v___x_1367_);
v___x_1370_ = lean_st_ref_get(v___y_1363_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = 0;
v___x_1373_ = l_Lean_Environment_find_x3f(v_env_1371_, v_declName_1368_, v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_dec(v_us_1369_);
lean_dec(v_a_1366_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___y_1202_ = v___y_1360_;
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
goto v___jp_1201_;
}
else
{
lean_object* v_val_1374_; 
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref(v___x_1373_);
if (lean_obj_tag(v_val_1374_) == 5)
{
lean_object* v_val_1375_; lean_object* v_toConstantVal_1376_; lean_object* v_numParams_1377_; lean_object* v_all_1378_; lean_object* v_nargs_1379_; lean_object* v_dummy_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_val_1375_ = lean_ctor_get(v_val_1374_, 0);
lean_inc_ref(v_val_1375_);
lean_dec_ref(v_val_1374_);
v_toConstantVal_1376_ = lean_ctor_get(v_val_1375_, 0);
lean_inc_ref(v_toConstantVal_1376_);
v_numParams_1377_ = lean_ctor_get(v_val_1375_, 1);
v_all_1378_ = lean_ctor_get(v_val_1375_, 3);
lean_inc(v_all_1378_);
v_nargs_1379_ = l_Lean_Expr_getAppNumArgs(v_a_1366_);
v_dummy_1380_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1379_);
v___x_1381_ = lean_mk_array(v_nargs_1379_, v_dummy_1380_);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_sub(v_nargs_1379_, v___x_1382_);
lean_dec(v_nargs_1379_);
lean_inc(v_a_1366_);
v___x_1384_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1366_, v___x_1381_, v___x_1383_);
v___x_1385_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1377_);
lean_inc_ref(v___x_1384_);
v___x_1386_ = l_Array_toSubarray___redArg(v___x_1384_, v___x_1385_, v_numParams_1377_);
v___x_1387_ = l_Subarray_copy___redArg(v___x_1386_);
v___x_1388_ = lean_array_get_size(v___x_1384_);
v___x_1389_ = lean_nat_dec_le(v_numParams_1377_, v___x_1385_);
if (v___x_1389_ == 0)
{
lean_inc(v_numParams_1377_);
v___y_1328_ = v_us_1369_;
v___y_1329_ = v___x_1385_;
v___y_1330_ = v___x_1384_;
v___y_1331_ = v_a_1366_;
v___y_1332_ = v___y_1362_;
v___y_1333_ = v_toConstantVal_1376_;
v___y_1334_ = v___y_1360_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v___x_1387_;
v___y_1337_ = v_val_1375_;
v___y_1338_ = v_all_1378_;
v___y_1339_ = v___y_1361_;
v_lower_1340_ = v_numParams_1377_;
v_upper_1341_ = v___x_1388_;
goto v___jp_1327_;
}
else
{
v___y_1328_ = v_us_1369_;
v___y_1329_ = v___x_1385_;
v___y_1330_ = v___x_1384_;
v___y_1331_ = v_a_1366_;
v___y_1332_ = v___y_1362_;
v___y_1333_ = v_toConstantVal_1376_;
v___y_1334_ = v___y_1360_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v___x_1387_;
v___y_1337_ = v_val_1375_;
v___y_1338_ = v_all_1378_;
v___y_1339_ = v___y_1361_;
v_lower_1340_ = v___x_1385_;
v_upper_1341_ = v___x_1388_;
goto v___jp_1327_;
}
}
else
{
lean_dec(v_val_1374_);
lean_dec(v_us_1369_);
lean_dec(v_a_1366_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___y_1202_ = v___y_1360_;
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
goto v___jp_1201_;
}
}
}
else
{
lean_dec_ref(v___x_1367_);
lean_dec(v_a_1366_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___y_1202_ = v___y_1360_;
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
goto v___jp_1201_;
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_a_1390_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1365_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1365_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
v___jp_1398_:
{
lean_object* v_x_1403_; lean_object* v___x_1404_; 
v_x_1403_ = lean_array_fget_borrowed(v_xs_1194_, v_i_1195_);
v___x_1404_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1403_, v___y_1399_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; uint8_t v___x_1406_; uint8_t v___x_1407_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = 0;
v___x_1407_ = l_Lean_LocalDecl_isLet(v_a_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
v___y_1359_ = v_a_1405_;
v___y_1360_ = v___y_1399_;
v___y_1361_ = v___y_1400_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1402_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v_a_1405_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1408_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1409_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1408_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_a_1418_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1404_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1404_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1459_, lean_object* v_fixedParamPerm_1460_, lean_object* v_xs_1461_, lean_object* v_i_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1459_, v_fixedParamPerm_1460_, v_xs_1461_, v_i_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec_ref(v_xs_1461_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1477_, v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(lean_object* v_as_1485_, lean_object* v_a_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1485_, v_a_1486_, v_x_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(lean_object* v_as_1490_, lean_object* v_a_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(v_as_1490_, v_a_1491_, v_x_1492_, v_x_1493_);
lean_dec_ref(v_a_1491_);
lean_dec_ref(v_as_1490_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1496_, lean_object* v_e_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l_Lean_indentD(v_e_1497_);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1496_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1500_, lean_object* v_fnName_1501_, lean_object* v_fixedParamPerm_1502_, lean_object* v_args_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1500_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1501_, v_fixedParamPerm_1502_, v_args_1503_, v_a_1510_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1511_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v_fixedParamPerm_1502_);
lean_dec(v_fnName_1501_);
v_a_1512_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1509_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1509_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1520_, lean_object* v_fnName_1521_, lean_object* v_fixedParamPerm_1522_, lean_object* v_args_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1520_, v_fnName_1521_, v_fixedParamPerm_1522_, v_args_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v_args_1523_);
return v_res_1529_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1540_ = l_Lean_MessageData_ofFormat(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1541_, lean_object* v_fnName_1542_, lean_object* v_fixedParamPerm_1543_, lean_object* v_args_1544_, lean_object* v_a_1545_, lean_object* v_b_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_fst_1553_; lean_object* v_snd_1554_; uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_lt(v_a_1545_, v_upperBound_1541_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec(v_a_1545_);
lean_dec_ref(v_fixedParamPerm_1543_);
lean_dec(v_fnName_1542_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_b_1546_);
return v___x_1560_;
}
else
{
lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1607_; 
v_fst_1561_ = lean_ctor_get(v_b_1546_, 0);
v_snd_1562_ = lean_ctor_get(v_b_1546_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_b_1546_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1564_ = v_b_1546_;
v_isShared_1565_ = v_isSharedCheck_1607_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_snd_1562_);
lean_inc(v_fst_1561_);
lean_dec(v_b_1546_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1607_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; 
lean_inc(v_a_1545_);
lean_inc_ref(v_fixedParamPerm_1543_);
lean_inc(v_fnName_1542_);
v___x_1566_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1542_, v_fixedParamPerm_1543_, v_args_1544_, v_a_1545_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
lean_del_object(v___x_1564_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = lean_array_push(v_fst_1561_, v_a_1567_);
v_fst_1553_ = v___x_1568_;
v_snd_1554_ = v_snd_1562_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1606_; 
v_a_1569_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1571_ = v___x_1566_;
v_isShared_1572_ = v_isSharedCheck_1606_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1566_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1606_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___y_1574_; uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Exception_isInterrupt(v_a_1569_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; 
lean_inc(v_a_1569_);
v___x_1605_ = l_Lean_Exception_isRuntime(v_a_1569_);
v___y_1574_ = v___x_1605_;
goto v___jp_1573_;
}
else
{
v___y_1574_ = v___x_1604_;
goto v___jp_1573_;
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_del_object(v___x_1571_);
v___x_1575_ = l_Lean_Elab_Structural_prettyParam(v_args_1544_, v_a_1545_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 7);
lean_ctor_set(v___x_1564_, 1, v_a_1576_);
lean_ctor_set(v___x_1564_, 0, v___x_1577_);
v___x_1579_ = v___x_1564_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1576_);
v___x_1579_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_inc(v_fnName_1542_);
v___x_1582_ = l_Lean_MessageData_ofName(v_fnName_1542_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_Exception_toMessageData(v_a_1569_);
v___x_1587_ = l_Lean_indentD(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1585_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_snd_1562_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v_fst_1553_ = v_fst_1561_;
v_snd_1554_ = v___x_1591_;
goto v___jp_1552_;
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1569_);
lean_del_object(v___x_1564_);
lean_dec(v_snd_1562_);
lean_dec(v_fst_1561_);
lean_dec(v_a_1545_);
lean_dec_ref(v_fixedParamPerm_1543_);
lean_dec(v_fnName_1542_);
v_a_1593_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1575_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1575_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v___x_1602_; 
lean_del_object(v___x_1564_);
lean_dec(v_snd_1562_);
lean_dec(v_fst_1561_);
lean_dec(v_a_1545_);
lean_dec_ref(v_fixedParamPerm_1543_);
lean_dec(v_fnName_1542_);
if (v_isShared_1572_ == 0)
{
v___x_1602_ = v___x_1571_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1569_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
}
v___jp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_fst_1553_);
lean_ctor_set(v___x_1555_, 1, v_snd_1554_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_a_1545_, v___x_1556_);
lean_dec(v_a_1545_);
v_a_1545_ = v___x_1557_;
v_b_1546_ = v___x_1555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1608_, lean_object* v_fnName_1609_, lean_object* v_fixedParamPerm_1610_, lean_object* v_args_1611_, lean_object* v_a_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1608_, v_fnName_1609_, v_fixedParamPerm_1610_, v_args_1611_, v_a_1612_, v_b_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_args_1611_);
lean_dec(v_upperBound_1608_);
return v_res_1619_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1620_; double v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_float_of_nat(v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1623_, lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_ref_1630_; lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1676_; 
v_ref_1630_ = lean_ctor_get(v___y_1627_, 5);
v___x_1631_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1676_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1676_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v_traceState_1637_; lean_object* v_env_1638_; lean_object* v_nextMacroScope_1639_; lean_object* v_ngen_1640_; lean_object* v_auxDeclNGen_1641_; lean_object* v_cache_1642_; lean_object* v_messages_1643_; lean_object* v_infoState_1644_; lean_object* v_snapshotTasks_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1675_; 
v___x_1636_ = lean_st_ref_take(v___y_1628_);
v_traceState_1637_ = lean_ctor_get(v___x_1636_, 4);
v_env_1638_ = lean_ctor_get(v___x_1636_, 0);
v_nextMacroScope_1639_ = lean_ctor_get(v___x_1636_, 1);
v_ngen_1640_ = lean_ctor_get(v___x_1636_, 2);
v_auxDeclNGen_1641_ = lean_ctor_get(v___x_1636_, 3);
v_cache_1642_ = lean_ctor_get(v___x_1636_, 5);
v_messages_1643_ = lean_ctor_get(v___x_1636_, 6);
v_infoState_1644_ = lean_ctor_get(v___x_1636_, 7);
v_snapshotTasks_1645_ = lean_ctor_get(v___x_1636_, 8);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1647_ = v___x_1636_;
v_isShared_1648_ = v_isSharedCheck_1675_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snapshotTasks_1645_);
lean_inc(v_infoState_1644_);
lean_inc(v_messages_1643_);
lean_inc(v_cache_1642_);
lean_inc(v_traceState_1637_);
lean_inc(v_auxDeclNGen_1641_);
lean_inc(v_ngen_1640_);
lean_inc(v_nextMacroScope_1639_);
lean_inc(v_env_1638_);
lean_dec(v___x_1636_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1675_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint64_t v_tid_1649_; lean_object* v_traces_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1674_; 
v_tid_1649_ = lean_ctor_get_uint64(v_traceState_1637_, sizeof(void*)*1);
v_traces_1650_ = lean_ctor_get(v_traceState_1637_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_traceState_1637_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1652_ = v_traceState_1637_;
v_isShared_1653_ = v_isSharedCheck_1674_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_traces_1650_);
lean_dec(v_traceState_1637_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1674_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; double v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1656_ = 0;
v___x_1657_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1658_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1658_, 0, v_cls_1623_);
lean_ctor_set(v___x_1658_, 1, v___x_1654_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
lean_ctor_set_float(v___x_1658_, sizeof(void*)*3, v___x_1655_);
lean_ctor_set_float(v___x_1658_, sizeof(void*)*3 + 8, v___x_1655_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 16, v___x_1656_);
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1660_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v_a_1632_);
lean_ctor_set(v___x_1660_, 2, v___x_1659_);
lean_inc(v_ref_1630_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_ref_1630_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = l_Lean_PersistentArray_push___redArg(v_traces_1650_, v___x_1661_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1662_);
v___x_1664_ = v___x_1652_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1662_);
lean_ctor_set_uint64(v_reuseFailAlloc_1673_, sizeof(void*)*1, v_tid_1649_);
v___x_1664_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 4, v___x_1664_);
v___x_1666_ = v___x_1647_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_env_1638_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_nextMacroScope_1639_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_ngen_1640_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_auxDeclNGen_1641_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1672_, 5, v_cache_1642_);
lean_ctor_set(v_reuseFailAlloc_1672_, 6, v_messages_1643_);
lean_ctor_set(v_reuseFailAlloc_1672_, 7, v_infoState_1644_);
lean_ctor_set(v_reuseFailAlloc_1672_, 8, v_snapshotTasks_1645_);
v___x_1666_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_st_ref_set(v___y_1628_, v___x_1666_);
v___x_1668_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1668_);
v___x_1670_ = v___x_1634_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1677_, lean_object* v_msg_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1677_, v_msg_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1684_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___f_1689_; 
v___x_1688_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1689_, 0, v___x_1688_);
return v___f_1689_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1694_; lean_object* v_recArgInfos_1695_; lean_object* v___x_1696_; 
v_report_1694_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1695_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_recArgInfos_1695_);
lean_ctor_set(v___x_1696_, 1, v_report_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1709_ = l_Lean_Name_append(v___x_1708_, v___x_1707_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1713_, lean_object* v_fixedParamPerm_1714_, lean_object* v_xs_1715_, lean_object* v_fnName_1716_, lean_object* v_ys_1717_, lean_object* v_x_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1713_) == 1)
{
lean_object* v_val_1724_; lean_object* v_ref_1725_; lean_object* v_fileName_1726_; lean_object* v_fileMap_1727_; lean_object* v_options_1728_; lean_object* v_currRecDepth_1729_; lean_object* v_maxRecDepth_1730_; lean_object* v_ref_1731_; lean_object* v_currNamespace_1732_; lean_object* v_openDecls_1733_; lean_object* v_initHeartbeats_1734_; lean_object* v_maxHeartbeats_1735_; lean_object* v_quotContext_1736_; lean_object* v_currMacroScope_1737_; uint8_t v_diag_1738_; lean_object* v_cancelTk_x3f_1739_; uint8_t v_suppressElabErrors_1740_; lean_object* v_inheritedTraceOptions_1741_; lean_object* v___f_1742_; lean_object* v_args_1743_; lean_object* v___f_1744_; lean_object* v_ref_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_val_1724_ = lean_ctor_get(v_termMeasure_x3f_1713_, 0);
lean_inc(v_val_1724_);
lean_dec_ref(v_termMeasure_x3f_1713_);
v_ref_1725_ = lean_ctor_get(v_val_1724_, 0);
lean_inc(v_ref_1725_);
v_fileName_1726_ = lean_ctor_get(v___y_1721_, 0);
v_fileMap_1727_ = lean_ctor_get(v___y_1721_, 1);
v_options_1728_ = lean_ctor_get(v___y_1721_, 2);
v_currRecDepth_1729_ = lean_ctor_get(v___y_1721_, 3);
v_maxRecDepth_1730_ = lean_ctor_get(v___y_1721_, 4);
v_ref_1731_ = lean_ctor_get(v___y_1721_, 5);
v_currNamespace_1732_ = lean_ctor_get(v___y_1721_, 6);
v_openDecls_1733_ = lean_ctor_get(v___y_1721_, 7);
v_initHeartbeats_1734_ = lean_ctor_get(v___y_1721_, 8);
v_maxHeartbeats_1735_ = lean_ctor_get(v___y_1721_, 9);
v_quotContext_1736_ = lean_ctor_get(v___y_1721_, 10);
v_currMacroScope_1737_ = lean_ctor_get(v___y_1721_, 11);
v_diag_1738_ = lean_ctor_get_uint8(v___y_1721_, sizeof(void*)*14);
v_cancelTk_x3f_1739_ = lean_ctor_get(v___y_1721_, 12);
v_suppressElabErrors_1740_ = lean_ctor_get_uint8(v___y_1721_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1741_ = lean_ctor_get(v___y_1721_, 13);
v___f_1742_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1714_);
v_args_1743_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1714_, v_xs_1715_, v_ys_1717_);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1744_, 0, v_val_1724_);
lean_closure_set(v___f_1744_, 1, v_fnName_1716_);
lean_closure_set(v___f_1744_, 2, v_fixedParamPerm_1714_);
lean_closure_set(v___f_1744_, 3, v_args_1743_);
v_ref_1745_ = l_Lean_replaceRef(v_ref_1725_, v_ref_1731_);
lean_dec(v_ref_1725_);
lean_inc_ref(v_inheritedTraceOptions_1741_);
lean_inc(v_cancelTk_x3f_1739_);
lean_inc(v_currMacroScope_1737_);
lean_inc(v_quotContext_1736_);
lean_inc(v_maxHeartbeats_1735_);
lean_inc(v_initHeartbeats_1734_);
lean_inc(v_openDecls_1733_);
lean_inc(v_currNamespace_1732_);
lean_inc(v_maxRecDepth_1730_);
lean_inc(v_currRecDepth_1729_);
lean_inc_ref(v_options_1728_);
lean_inc_ref(v_fileMap_1727_);
lean_inc_ref(v_fileName_1726_);
v___x_1746_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1746_, 0, v_fileName_1726_);
lean_ctor_set(v___x_1746_, 1, v_fileMap_1727_);
lean_ctor_set(v___x_1746_, 2, v_options_1728_);
lean_ctor_set(v___x_1746_, 3, v_currRecDepth_1729_);
lean_ctor_set(v___x_1746_, 4, v_maxRecDepth_1730_);
lean_ctor_set(v___x_1746_, 5, v_ref_1745_);
lean_ctor_set(v___x_1746_, 6, v_currNamespace_1732_);
lean_ctor_set(v___x_1746_, 7, v_openDecls_1733_);
lean_ctor_set(v___x_1746_, 8, v_initHeartbeats_1734_);
lean_ctor_set(v___x_1746_, 9, v_maxHeartbeats_1735_);
lean_ctor_set(v___x_1746_, 10, v_quotContext_1736_);
lean_ctor_set(v___x_1746_, 11, v_currMacroScope_1737_);
lean_ctor_set(v___x_1746_, 12, v_cancelTk_x3f_1739_);
lean_ctor_set(v___x_1746_, 13, v_inheritedTraceOptions_1741_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*14, v_diag_1738_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*14 + 1, v_suppressElabErrors_1740_);
v___x_1747_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1744_, v___f_1742_, v___y_1719_, v___y_1720_, v___x_1746_, v___y_1722_);
lean_dec_ref(v___x_1746_);
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
lean_dec(v_termMeasure_x3f_1713_);
lean_inc_ref(v_fixedParamPerm_1714_);
v_args_1769_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1714_, v_xs_1715_, v_ys_1717_);
v___x_1770_ = lean_array_get_size(v_args_1769_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1770_, v_fnName_1716_, v_fixedParamPerm_1714_, v_args_1769_, v___x_1771_, v___x_1772_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec_ref(v_args_1769_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1808_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1808_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1808_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1807_; 
v_fst_1778_ = lean_ctor_get(v_a_1774_, 0);
v_snd_1779_ = lean_ctor_get(v_a_1774_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1781_ = v_a_1774_;
v_isShared_1782_ = v_isSharedCheck_1807_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v_a_1774_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1807_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_options_1790_; uint8_t v_hasTrace_1791_; 
v_options_1790_ = lean_ctor_get(v___y_1721_, 2);
v_hasTrace_1791_ = lean_ctor_get_uint8(v_options_1790_, sizeof(void*)*1);
if (v_hasTrace_1791_ == 0)
{
goto v___jp_1783_;
}
else
{
lean_object* v_inheritedTraceOptions_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_inheritedTraceOptions_1792_ = lean_ctor_get(v___y_1721_, 13);
v___x_1793_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1792_, v_options_1790_, v___x_1794_);
if (v___x_1795_ == 0)
{
goto v___jp_1783_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1779_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_snd_1779_);
v___x_1798_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1793_, v___x_1797_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_dec_ref(v___x_1798_);
goto v___jp_1783_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_del_object(v___x_1781_);
lean_dec(v_snd_1779_);
lean_dec(v_fst_1778_);
lean_del_object(v___x_1776_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1809_, lean_object* v_fixedParamPerm_1810_, lean_object* v_xs_1811_, lean_object* v_fnName_1812_, lean_object* v_ys_1813_, lean_object* v_x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1809_, v_fixedParamPerm_1810_, v_xs_1811_, v_fnName_1812_, v_ys_1813_, v_x_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_x_1814_);
lean_dec_ref(v_xs_1811_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1821_, lean_object* v_fixedParamPerm_1822_, lean_object* v_xs_1823_, lean_object* v_value_1824_, lean_object* v_termMeasure_x3f_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___f_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; 
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1831_, 0, v_termMeasure_x3f_1825_);
lean_closure_set(v___f_1831_, 1, v_fixedParamPerm_1822_);
lean_closure_set(v___f_1831_, 2, v_xs_1823_);
lean_closure_set(v___f_1831_, 3, v_fnName_1821_);
v___x_1832_ = 0;
v___x_1833_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1824_, v___f_1831_, v___x_1832_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1834_, lean_object* v_fixedParamPerm_1835_, lean_object* v_xs_1836_, lean_object* v_value_1837_, lean_object* v_termMeasure_x3f_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1834_, v_fixedParamPerm_1835_, v_xs_1836_, v_value_1837_, v_termMeasure_x3f_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1845_, lean_object* v_fnName_1846_, lean_object* v_fixedParamPerm_1847_, lean_object* v_args_1848_, lean_object* v_inst_1849_, lean_object* v_R_1850_, lean_object* v_a_1851_, lean_object* v_b_1852_, lean_object* v_c_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1845_, v_fnName_1846_, v_fixedParamPerm_1847_, v_args_1848_, v_a_1851_, v_b_1852_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1860_, lean_object* v_fnName_1861_, lean_object* v_fixedParamPerm_1862_, lean_object* v_args_1863_, lean_object* v_inst_1864_, lean_object* v_R_1865_, lean_object* v_a_1866_, lean_object* v_b_1867_, lean_object* v_c_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1860_, v_fnName_1861_, v_fixedParamPerm_1862_, v_args_1863_, v_inst_1864_, v_R_1865_, v_a_1866_, v_b_1867_, v_c_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v_args_1863_);
lean_dec(v_upperBound_1860_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
return v_x_1875_;
}
else
{
lean_object* v_key_1877_; lean_object* v_value_1878_; lean_object* v_tail_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1902_; 
v_key_1877_ = lean_ctor_get(v_x_1876_, 0);
v_value_1878_ = lean_ctor_get(v_x_1876_, 1);
v_tail_1879_ = lean_ctor_get(v_x_1876_, 2);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1876_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1881_ = v_x_1876_;
v_isShared_1882_ = v_isSharedCheck_1902_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_tail_1879_);
lean_inc(v_value_1878_);
lean_inc(v_key_1877_);
lean_dec(v_x_1876_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1902_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; uint64_t v___x_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; uint64_t v_fold_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; uint64_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1883_ = lean_array_get_size(v_x_1875_);
v___x_1884_ = lean_uint64_of_nat(v_key_1877_);
v___x_1885_ = 32ULL;
v___x_1886_ = lean_uint64_shift_right(v___x_1884_, v___x_1885_);
v_fold_1887_ = lean_uint64_xor(v___x_1884_, v___x_1886_);
v___x_1888_ = 16ULL;
v___x_1889_ = lean_uint64_shift_right(v_fold_1887_, v___x_1888_);
v___x_1890_ = lean_uint64_xor(v_fold_1887_, v___x_1889_);
v___x_1891_ = lean_uint64_to_usize(v___x_1890_);
v___x_1892_ = lean_usize_of_nat(v___x_1883_);
v___x_1893_ = ((size_t)1ULL);
v___x_1894_ = lean_usize_sub(v___x_1892_, v___x_1893_);
v___x_1895_ = lean_usize_land(v___x_1891_, v___x_1894_);
v___x_1896_ = lean_array_uget_borrowed(v_x_1875_, v___x_1895_);
lean_inc(v___x_1896_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 2, v___x_1896_);
v___x_1898_ = v___x_1881_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_key_1877_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_value_1878_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_array_uset(v_x_1875_, v___x_1895_, v___x_1898_);
v_x_1875_ = v___x_1899_;
v_x_1876_ = v_tail_1879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1903_, lean_object* v_source_1904_, lean_object* v_target_1905_){
_start:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_array_get_size(v_source_1904_);
v___x_1907_ = lean_nat_dec_lt(v_i_1903_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_dec_ref(v_source_1904_);
lean_dec(v_i_1903_);
return v_target_1905_;
}
else
{
lean_object* v_es_1908_; lean_object* v___x_1909_; lean_object* v_source_1910_; lean_object* v_target_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_es_1908_ = lean_array_fget(v_source_1904_, v_i_1903_);
v___x_1909_ = lean_box(0);
v_source_1910_ = lean_array_fset(v_source_1904_, v_i_1903_, v___x_1909_);
v_target_1911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1905_, v_es_1908_);
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_add(v_i_1903_, v___x_1912_);
lean_dec(v_i_1903_);
v_i_1903_ = v___x_1913_;
v_source_1904_ = v_source_1910_;
v_target_1905_ = v_target_1911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v_nbuckets_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1916_ = lean_array_get_size(v_data_1915_);
v___x_1917_ = lean_unsigned_to_nat(2u);
v_nbuckets_1918_ = lean_nat_mul(v___x_1916_, v___x_1917_);
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_mk_array(v_nbuckets_1918_, v___x_1920_);
v___x_1922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1919_, v_data_1915_, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1923_, lean_object* v_x_1924_){
_start:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = 0;
return v___x_1925_;
}
else
{
lean_object* v_key_1926_; lean_object* v_tail_1927_; uint8_t v___x_1928_; 
v_key_1926_ = lean_ctor_get(v_x_1924_, 0);
v_tail_1927_ = lean_ctor_get(v_x_1924_, 2);
v___x_1928_ = lean_nat_dec_eq(v_key_1926_, v_a_1923_);
if (v___x_1928_ == 0)
{
v_x_1924_ = v_tail_1927_;
goto _start;
}
else
{
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1930_, lean_object* v_x_1931_){
_start:
{
uint8_t v_res_1932_; lean_object* v_r_1933_; 
v_res_1932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1930_, v_x_1931_);
lean_dec(v_x_1931_);
lean_dec(v_a_1930_);
v_r_1933_ = lean_box(v_res_1932_);
return v_r_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1934_, lean_object* v_a_1935_, lean_object* v_b_1936_){
_start:
{
lean_object* v_size_1937_; lean_object* v_buckets_1938_; lean_object* v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v_fold_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; uint64_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; lean_object* v_bkt_1952_; uint8_t v___x_1953_; 
v_size_1937_ = lean_ctor_get(v_m_1934_, 0);
v_buckets_1938_ = lean_ctor_get(v_m_1934_, 1);
v___x_1939_ = lean_array_get_size(v_buckets_1938_);
v___x_1940_ = lean_uint64_of_nat(v_a_1935_);
v___x_1941_ = 32ULL;
v___x_1942_ = lean_uint64_shift_right(v___x_1940_, v___x_1941_);
v_fold_1943_ = lean_uint64_xor(v___x_1940_, v___x_1942_);
v___x_1944_ = 16ULL;
v___x_1945_ = lean_uint64_shift_right(v_fold_1943_, v___x_1944_);
v___x_1946_ = lean_uint64_xor(v_fold_1943_, v___x_1945_);
v___x_1947_ = lean_uint64_to_usize(v___x_1946_);
v___x_1948_ = lean_usize_of_nat(v___x_1939_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_sub(v___x_1948_, v___x_1949_);
v___x_1951_ = lean_usize_land(v___x_1947_, v___x_1950_);
v_bkt_1952_ = lean_array_uget_borrowed(v_buckets_1938_, v___x_1951_);
v___x_1953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1935_, v_bkt_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1974_; 
lean_inc_ref(v_buckets_1938_);
lean_inc(v_size_1937_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_m_1934_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1975_ = lean_ctor_get(v_m_1934_, 1);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_m_1934_, 0);
lean_dec(v_unused_1976_);
v___x_1955_ = v_m_1934_;
v_isShared_1956_ = v_isSharedCheck_1974_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v_m_1934_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1974_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v_size_x27_1958_; lean_object* v___x_1959_; lean_object* v_buckets_x27_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1957_ = lean_unsigned_to_nat(1u);
v_size_x27_1958_ = lean_nat_add(v_size_1937_, v___x_1957_);
lean_dec(v_size_1937_);
lean_inc(v_bkt_1952_);
v___x_1959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1959_, 0, v_a_1935_);
lean_ctor_set(v___x_1959_, 1, v_b_1936_);
lean_ctor_set(v___x_1959_, 2, v_bkt_1952_);
v_buckets_x27_1960_ = lean_array_uset(v_buckets_1938_, v___x_1951_, v___x_1959_);
v___x_1961_ = lean_unsigned_to_nat(4u);
v___x_1962_ = lean_nat_mul(v_size_x27_1958_, v___x_1961_);
v___x_1963_ = lean_unsigned_to_nat(3u);
v___x_1964_ = lean_nat_div(v___x_1962_, v___x_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_array_get_size(v_buckets_x27_1960_);
v___x_1966_ = lean_nat_dec_le(v___x_1964_, v___x_1965_);
lean_dec(v___x_1964_);
if (v___x_1966_ == 0)
{
lean_object* v_val_1967_; lean_object* v___x_1969_; 
v_val_1967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1960_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v_val_1967_);
lean_ctor_set(v___x_1955_, 0, v_size_x27_1958_);
v___x_1969_ = v___x_1955_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_size_x27_1958_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_val_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
else
{
lean_object* v___x_1972_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v_buckets_x27_1960_);
lean_ctor_set(v___x_1955_, 0, v_size_x27_1958_);
v___x_1972_ = v___x_1955_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_size_x27_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_buckets_x27_1960_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_dec(v_b_1936_);
lean_dec(v_a_1935_);
return v_m_1934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1977_, size_t v_sz_1978_, size_t v_i_1979_, lean_object* v_b_1980_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_usize_dec_lt(v_i_1979_, v_sz_1978_);
if (v___x_1981_ == 0)
{
return v_b_1980_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; size_t v___x_1985_; size_t v___x_1986_; 
v_a_1982_ = lean_array_uget_borrowed(v_as_1977_, v_i_1979_);
v___x_1983_ = lean_box(0);
lean_inc(v_a_1982_);
v___x_1984_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1980_, v_a_1982_, v___x_1983_);
v___x_1985_ = ((size_t)1ULL);
v___x_1986_ = lean_usize_add(v_i_1979_, v___x_1985_);
v_i_1979_ = v___x_1986_;
v_b_1980_ = v___x_1984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1988_, lean_object* v_sz_1989_, lean_object* v_i_1990_, lean_object* v_b_1991_){
_start:
{
size_t v_sz_boxed_1992_; size_t v_i_boxed_1993_; lean_object* v_res_1994_; 
v_sz_boxed_1992_ = lean_unbox_usize(v_sz_1989_);
lean_dec(v_sz_1989_);
v_i_boxed_1993_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_res_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1988_, v_sz_boxed_1992_, v_i_boxed_1993_, v_b_1991_);
lean_dec_ref(v_as_1988_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_1999_ == 0)
{
return v_b_1998_;
}
else
{
lean_object* v_a_2000_; lean_object* v_indicesPos_2001_; size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; 
v_a_2000_ = lean_array_uget_borrowed(v_as_1995_, v_i_1997_);
v_indicesPos_2001_ = lean_ctor_get(v_a_2000_, 3);
v_sz_2002_ = lean_array_size(v_indicesPos_2001_);
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2001_, v_sz_2002_, v___x_2003_, v_b_1998_);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1997_, v___x_2005_);
v_i_1997_ = v___x_2006_;
v_b_1998_ = v___x_2004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2008_, lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_b_2011_){
_start:
{
size_t v_sz_boxed_2012_; size_t v_i_boxed_2013_; lean_object* v_res_2014_; 
v_sz_boxed_2012_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2013_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2008_, v_sz_boxed_2012_, v_i_boxed_2013_, v_b_2011_);
lean_dec_ref(v_as_2008_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_buckets_2017_; lean_object* v___x_2018_; uint64_t v___x_2019_; uint64_t v___x_2020_; uint64_t v___x_2021_; uint64_t v_fold_2022_; uint64_t v___x_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_buckets_2017_ = lean_ctor_get(v_m_2015_, 1);
v___x_2018_ = lean_array_get_size(v_buckets_2017_);
v___x_2019_ = lean_uint64_of_nat(v_a_2016_);
v___x_2020_ = 32ULL;
v___x_2021_ = lean_uint64_shift_right(v___x_2019_, v___x_2020_);
v_fold_2022_ = lean_uint64_xor(v___x_2019_, v___x_2021_);
v___x_2023_ = 16ULL;
v___x_2024_ = lean_uint64_shift_right(v_fold_2022_, v___x_2023_);
v___x_2025_ = lean_uint64_xor(v_fold_2022_, v___x_2024_);
v___x_2026_ = lean_uint64_to_usize(v___x_2025_);
v___x_2027_ = lean_usize_of_nat(v___x_2018_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_sub(v___x_2027_, v___x_2028_);
v___x_2030_ = lean_usize_land(v___x_2026_, v___x_2029_);
v___x_2031_ = lean_array_uget_borrowed(v_buckets_2017_, v___x_2030_);
v___x_2032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2016_, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2033_, lean_object* v_a_2034_){
_start:
{
uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_res_2035_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2033_, v_a_2034_);
lean_dec(v_a_2034_);
lean_dec_ref(v_m_2033_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2037_, lean_object* v_as_2038_, size_t v_sz_2039_, size_t v_i_2040_, lean_object* v_b_2041_){
_start:
{
lean_object* v_a_2043_; uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_lt(v_i_2040_, v_sz_2039_);
if (v___x_2047_ == 0)
{
return v_b_2041_;
}
else
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2064_; 
v_fst_2048_ = lean_ctor_get(v_b_2041_, 0);
v_snd_2049_ = lean_ctor_get(v_b_2041_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_b_2041_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2051_ = v_b_2041_;
v_isShared_2052_ = v_isSharedCheck_2064_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_inc(v_fst_2048_);
lean_dec(v_b_2041_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2064_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_a_2053_; lean_object* v_recArgPos_2054_; uint8_t v___x_2055_; 
v_a_2053_ = lean_array_uget_borrowed(v_as_2038_, v_i_2040_);
v_recArgPos_2054_ = lean_ctor_get(v_a_2053_, 2);
v___x_2055_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2037_, v_recArgPos_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_inc(v_a_2053_);
v___x_2056_ = lean_array_push(v_snd_2049_, v_a_2053_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2056_);
v___x_2058_ = v___x_2051_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v_a_2043_ = v___x_2058_;
goto v___jp_2042_;
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_inc(v_a_2053_);
v___x_2060_ = lean_array_push(v_fst_2048_, v_a_2053_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2060_);
v___x_2062_ = v___x_2051_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_snd_2049_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_2043_ = v___x_2062_;
goto v___jp_2042_;
}
}
}
}
v___jp_2042_:
{
size_t v___x_2044_; size_t v___x_2045_; 
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2040_, v___x_2044_);
v_i_2040_ = v___x_2045_;
v_b_2041_ = v_a_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2065_, lean_object* v_as_2066_, lean_object* v_sz_2067_, lean_object* v_i_2068_, lean_object* v_b_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2067_);
lean_dec(v_sz_2067_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2065_, v_as_2066_, v_sz_boxed_2070_, v_i_boxed_2071_, v_b_2069_);
lean_dec_ref(v_as_2066_);
lean_dec_ref(v___x_2065_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_unsigned_to_nat(16u);
v___x_2075_ = lean_mk_array(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_indicesPos_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2077_ = lean_unsigned_to_nat(0u);
v_indicesPos_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2078_, 0, v___x_2077_);
lean_ctor_set(v_indicesPos_2078_, 1, v___x_2076_);
return v_indicesPos_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2081_){
_start:
{
lean_object* v_indicesPos_2082_; size_t v_sz_2083_; size_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; 
v_indicesPos_2082_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2083_ = lean_array_size(v_recArgInfos_2081_);
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2081_, v_sz_2083_, v___x_2084_, v_indicesPos_2082_);
v___x_2086_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2085_, v_recArgInfos_2081_, v_sz_2083_, v___x_2084_, v___x_2086_);
lean_dec_ref(v___x_2085_);
v_fst_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v___x_2087_, 1);
lean_inc(v_snd_2089_);
lean_dec_ref(v___x_2087_);
v___x_2090_ = l_Array_append___redArg(v_snd_2089_, v_fst_2088_);
lean_dec(v_fst_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2091_);
lean_dec_ref(v_recArgInfos_2091_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2093_, lean_object* v_m_2094_, lean_object* v_a_2095_, lean_object* v_b_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2094_, v_a_2095_, v_b_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2098_, lean_object* v_m_2099_, lean_object* v_a_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2099_, v_a_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2102_, lean_object* v_m_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v_res_2105_; lean_object* v_r_2106_; 
v_res_2105_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2102_, v_m_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_m_2103_);
v_r_2106_ = lean_box(v_res_2105_);
return v_r_2106_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2107_, lean_object* v_a_2108_, lean_object* v_x_2109_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2108_, v_x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2111_, lean_object* v_a_2112_, lean_object* v_x_2113_){
_start:
{
uint8_t v_res_2114_; lean_object* v_r_2115_; 
v_res_2114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2111_, v_a_2112_, v_x_2113_);
lean_dec(v_x_2113_);
lean_dec(v_a_2112_);
v_r_2115_ = lean_box(v_res_2114_);
return v_r_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2116_, lean_object* v_data_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2119_, lean_object* v_i_2120_, lean_object* v_source_2121_, lean_object* v_target_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2120_, v_source_2121_, v_target_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2125_, v_x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2128_, lean_object* v_a_2129_, lean_object* v_toPure_2130_, uint8_t v_____do__lift_2131_){
_start:
{
if (v_____do__lift_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_array_push(v___y_2128_, v_a_2129_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_apply_2(v_toPure_2130_, lean_box(0), v___x_2133_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_a_2129_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___y_2128_);
v___x_2136_ = lean_apply_2(v_toPure_2130_, lean_box(0), v___x_2135_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2137_, lean_object* v_a_2138_, lean_object* v_toPure_2139_, lean_object* v_____do__lift_2140_){
_start:
{
uint8_t v_____do__lift_192__boxed_2141_; lean_object* v_res_2142_; 
v_____do__lift_192__boxed_2141_ = lean_unbox(v_____do__lift_2140_);
v_res_2142_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2137_, v_a_2138_, v_toPure_2139_, v_____do__lift_192__boxed_2141_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_apply_2(v_eq_2143_, v_x_2145_, v_a_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2147_, lean_object* v___x_2148_, lean_object* v_toBind_2149_, lean_object* v_eq_2150_, lean_object* v_inst_2151_, lean_object* v_a_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___f_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
lean_inc(v_toPure_2147_);
lean_inc(v_a_2152_);
lean_inc_ref(v___y_2154_);
v___f_2155_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2155_, 0, v___y_2154_);
lean_closure_set(v___f_2155_, 1, v_a_2152_);
lean_closure_set(v___f_2155_, 2, v_toPure_2147_);
v___x_2156_ = lean_array_get_size(v___y_2154_);
v___x_2157_ = lean_nat_dec_lt(v___x_2148_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v___y_2154_);
lean_dec(v_a_2152_);
lean_dec_ref(v_inst_2151_);
lean_dec(v_eq_2150_);
v___x_2158_ = lean_box(v___x_2157_);
v___x_2159_ = lean_apply_2(v_toPure_2147_, lean_box(0), v___x_2158_);
v___x_2160_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v___x_2159_, v___f_2155_);
return v___x_2160_;
}
else
{
if (v___x_2157_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v___y_2154_);
lean_dec(v_a_2152_);
lean_dec_ref(v_inst_2151_);
lean_dec(v_eq_2150_);
v___x_2161_ = lean_box(v___x_2157_);
v___x_2162_ = lean_apply_2(v_toPure_2147_, lean_box(0), v___x_2161_);
v___x_2163_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v___x_2162_, v___f_2155_);
return v___x_2163_;
}
else
{
lean_object* v___f_2164_; size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_toPure_2147_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2164_, 0, v_eq_2150_);
lean_closure_set(v___f_2164_, 1, v_a_2152_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = lean_usize_of_nat(v___x_2156_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2151_, v___f_2164_, v___y_2154_, v___x_2165_, v___x_2166_);
v___x_2168_ = lean_apply_4(v_toBind_2149_, lean_box(0), lean_box(0), v___x_2167_, v___f_2155_);
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2169_, lean_object* v___x_2170_, lean_object* v_toBind_2171_, lean_object* v_eq_2172_, lean_object* v_inst_2173_, lean_object* v_a_2174_, lean_object* v_x_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2169_, v___x_2170_, v_toBind_2171_, v_eq_2172_, v_inst_2173_, v_a_2174_, v_x_2175_, v___y_2176_);
lean_dec(v___x_2170_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2178_, lean_object* v_____s_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_apply_2(v_toPure_2178_, lean_box(0), v_____s_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2183_, lean_object* v_eq_2184_, lean_object* v_xs_2185_){
_start:
{
lean_object* v_toApplicative_2186_; lean_object* v_toBind_2187_; lean_object* v_toPure_2188_; lean_object* v___x_2189_; lean_object* v_ret_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; size_t v_sz_2193_; size_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_toApplicative_2186_ = lean_ctor_get(v_inst_2183_, 0);
v_toBind_2187_ = lean_ctor_get(v_inst_2183_, 1);
lean_inc_n(v_toBind_2187_, 2);
v_toPure_2188_ = lean_ctor_get(v_toApplicative_2186_, 1);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_ret_2190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2183_);
lean_inc_n(v_toPure_2188_, 2);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2191_, 0, v_toPure_2188_);
lean_closure_set(v___f_2191_, 1, v___x_2189_);
lean_closure_set(v___f_2191_, 2, v_toBind_2187_);
lean_closure_set(v___f_2191_, 3, v_eq_2184_);
lean_closure_set(v___f_2191_, 4, v_inst_2183_);
v___f_2192_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2192_, 0, v_toPure_2188_);
v_sz_2193_ = lean_array_size(v_xs_2185_);
v___x_2194_ = ((size_t)0ULL);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2183_, v_xs_2185_, v___f_2191_, v_sz_2193_, v___x_2194_, v_ret_2190_);
v___x_2196_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v___x_2195_, v___f_2192_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2197_, lean_object* v_00_u03b1_2198_, lean_object* v_inst_2199_, lean_object* v_eq_2200_, lean_object* v_xs_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2199_, v_eq_2200_, v_xs_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2203_, size_t v_i_2204_, lean_object* v_bs_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_lt(v_i_2204_, v_sz_2203_);
if (v___x_2206_ == 0)
{
return v_bs_2205_;
}
else
{
lean_object* v_v_2207_; lean_object* v_indGroupInst_2208_; lean_object* v___x_2209_; lean_object* v_bs_x27_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_v_2207_ = lean_array_uget_borrowed(v_bs_2205_, v_i_2204_);
v_indGroupInst_2208_ = lean_ctor_get(v_v_2207_, 4);
lean_inc_ref(v_indGroupInst_2208_);
v___x_2209_ = lean_unsigned_to_nat(0u);
v_bs_x27_2210_ = lean_array_uset(v_bs_2205_, v_i_2204_, v___x_2209_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2204_, v___x_2211_);
v___x_2213_ = lean_array_uset(v_bs_x27_2210_, v_i_2204_, v_indGroupInst_2208_);
v_i_2204_ = v___x_2212_;
v_bs_2205_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2215_, lean_object* v_i_2216_, lean_object* v_bs_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2215_);
lean_dec(v_sz_2215_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2218_, v_i_boxed_2219_, v_bs_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2221_, lean_object* v_a_2222_, lean_object* v_as_2223_, size_t v_i_2224_, size_t v_stop_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_usize_dec_eq(v_i_2224_, v_stop_2225_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_array_uget_borrowed(v_as_2223_, v_i_2224_);
lean_inc_ref(v_eq_2221_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v_a_2222_);
lean_inc(v___x_2232_);
v___x_2233_ = lean_apply_7(v_eq_2221_, v___x_2232_, v_a_2222_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, lean_box(0));
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2245_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_unbox(v_a_2234_);
if (v___x_2238_ == 0)
{
size_t v___x_2239_; size_t v___x_2240_; 
lean_del_object(v___x_2236_);
lean_dec(v_a_2234_);
v___x_2239_ = ((size_t)1ULL);
v___x_2240_ = lean_usize_add(v_i_2224_, v___x_2239_);
v_i_2224_ = v___x_2240_;
goto _start;
}
else
{
lean_object* v___x_2243_; 
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
if (v_isShared_2237_ == 0)
{
v___x_2243_ = v___x_2236_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2234_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
return v___x_2233_;
}
}
else
{
uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
v___x_2246_ = 0;
v___x_2247_ = lean_box(v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2249_, lean_object* v_a_2250_, lean_object* v_as_2251_, lean_object* v_i_2252_, lean_object* v_stop_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
size_t v_i_boxed_2259_; size_t v_stop_boxed_2260_; lean_object* v_res_2261_; 
v_i_boxed_2259_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_stop_boxed_2260_ = lean_unbox_usize(v_stop_2253_);
lean_dec(v_stop_2253_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2249_, v_a_2250_, v_as_2251_, v_i_boxed_2259_, v_stop_boxed_2260_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_as_2251_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2262_, lean_object* v_a_2263_, uint8_t v_____do__lift_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
if (v_____do__lift_2264_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_array_push(v_b_2262_, v_a_2263_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec(v_a_2263_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_b_2262_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2275_, lean_object* v_a_2276_, lean_object* v_____do__lift_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v_____do__lift_1292__boxed_2283_; lean_object* v_res_2284_; 
v_____do__lift_1292__boxed_2283_ = lean_unbox(v_____do__lift_2277_);
v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2275_, v_a_2276_, v_____do__lift_1292__boxed_2283_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2285_, lean_object* v_as_2286_, size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_a_2296_; lean_object* v___y_2301_; uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_lt(v_i_2288_, v_sz_2287_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref(v_eq_2285_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_b_2289_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
v_a_2323_ = lean_array_uget_borrowed(v_as_2286_, v_i_2288_);
v___x_2324_ = lean_array_get_size(v_b_2289_);
v___x_2325_ = lean_nat_dec_lt(v___x_2322_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_inc(v_a_2323_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2289_, v_a_2323_, v___x_2325_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
v___y_2301_ = v___x_2326_;
goto v___jp_2300_;
}
else
{
if (v___x_2325_ == 0)
{
lean_object* v___x_2327_; 
lean_inc(v_a_2323_);
v___x_2327_ = lean_array_push(v_b_2289_, v_a_2323_);
v_a_2296_ = v___x_2327_;
goto v___jp_2295_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2324_);
lean_inc(v_a_2323_);
lean_inc_ref(v_eq_2285_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2285_, v_a_2323_, v_b_2289_, v___x_2328_, v___x_2329_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = lean_unbox(v_a_2331_);
lean_dec(v_a_2331_);
lean_inc(v_a_2323_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2289_, v_a_2323_, v___x_2332_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
v___y_2301_ = v___x_2333_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v_b_2289_);
lean_dec_ref(v_eq_2285_);
v_a_2334_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2330_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2330_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
v___jp_2295_:
{
size_t v___x_2297_; size_t v___x_2298_; 
v___x_2297_ = ((size_t)1ULL);
v___x_2298_ = lean_usize_add(v_i_2288_, v___x_2297_);
v_i_2288_ = v___x_2298_;
v_b_2289_ = v_a_2296_;
goto _start;
}
v___jp_2300_:
{
if (lean_obj_tag(v___y_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
v_a_2302_ = lean_ctor_get(v___y_2301_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___y_2301_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2304_ = v___y_2301_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___y_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
if (lean_obj_tag(v_a_2302_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; 
lean_dec_ref(v_eq_2285_);
v_a_2306_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v_a_2302_);
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
lean_object* v_a_2310_; 
lean_del_object(v___x_2304_);
v_a_2310_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v_a_2302_);
v_a_2296_ = v_a_2310_;
goto v___jp_2295_;
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_eq_2285_);
v_a_2312_ = lean_ctor_get(v___y_2301_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___y_2301_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___y_2301_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___y_2301_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2342_, lean_object* v_as_2343_, lean_object* v_sz_2344_, lean_object* v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2344_);
lean_dec(v_sz_2344_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2342_, v_as_2343_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_as_2343_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2355_, lean_object* v_xs_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_ret_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v_ret_2362_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2363_ = lean_array_size(v_xs_2356_);
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2355_, v_xs_2356_, v_sz_2363_, v___x_2364_, v_ret_2362_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2366_, lean_object* v_xs_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2366_, v_xs_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec_ref(v_xs_2367_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; size_t v_sz_2382_; size_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2381_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2382_ = lean_array_size(v_recArgInfos_2375_);
v___x_2383_ = ((size_t)0ULL);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2382_, v___x_2383_, v_recArgInfos_2375_);
v___x_2385_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2381_, v___x_2384_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec_ref(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2393_, lean_object* v_eq_2394_, lean_object* v_xs_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2394_, v_xs_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_eq_2403_, lean_object* v_xs_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2402_, v_eq_2403_, v_xs_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v_xs_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2411_, lean_object* v_eq_2412_, lean_object* v_a_2413_, lean_object* v_as_2414_, size_t v_i_2415_, size_t v_stop_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2412_, v_a_2413_, v_as_2414_, v_i_2415_, v_stop_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_eq_2424_, lean_object* v_a_2425_, lean_object* v_as_2426_, lean_object* v_i_2427_, lean_object* v_stop_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
size_t v_i_boxed_2434_; size_t v_stop_boxed_2435_; lean_object* v_res_2436_; 
v_i_boxed_2434_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_stop_boxed_2435_ = lean_unbox_usize(v_stop_2428_);
lean_dec(v_stop_2428_);
v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2423_, v_eq_2424_, v_a_2425_, v_as_2426_, v_i_boxed_2434_, v_stop_boxed_2435_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_as_2426_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2437_, lean_object* v_eq_2438_, lean_object* v_as_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_b_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2438_, v_as_2439_, v_sz_2440_, v_i_2441_, v_b_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2449_, lean_object* v_eq_2450_, lean_object* v_as_2451_, lean_object* v_sz_2452_, lean_object* v_i_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
size_t v_sz_boxed_2460_; size_t v_i_boxed_2461_; lean_object* v_res_2462_; 
v_sz_boxed_2460_ = lean_unbox_usize(v_sz_2452_);
lean_dec(v_sz_2452_);
v_i_boxed_2461_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2449_, v_eq_2450_, v_as_2451_, v_sz_boxed_2460_, v_i_boxed_2461_, v_b_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec_ref(v_as_2451_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2463_, lean_object* v___y_2464_){
_start:
{
uint8_t v___x_2466_; 
v___x_2466_ = l_Lean_Expr_hasMVar(v_e_2463_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_e_2463_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; lean_object* v_mctx_2469_; lean_object* v___x_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v___x_2473_; lean_object* v_cache_2474_; lean_object* v_zetaDeltaFVarIds_2475_; lean_object* v_postponed_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2486_; 
v___x_2468_ = lean_st_ref_get(v___y_2464_);
v_mctx_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_mctx_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l_Lean_instantiateMVarsCore(v_mctx_2469_, v_e_2463_);
v_fst_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_fst_2471_);
v_snd_2472_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2472_);
lean_dec_ref(v___x_2470_);
v___x_2473_ = lean_st_ref_take(v___y_2464_);
v_cache_2474_ = lean_ctor_get(v___x_2473_, 1);
v_zetaDeltaFVarIds_2475_ = lean_ctor_get(v___x_2473_, 2);
v_postponed_2476_ = lean_ctor_get(v___x_2473_, 3);
v_diag_2477_ = lean_ctor_get(v___x_2473_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2473_, 0);
lean_dec(v_unused_2487_);
v___x_2479_ = v___x_2473_;
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_postponed_2476_);
lean_inc(v_zetaDeltaFVarIds_2475_);
lean_inc(v_cache_2474_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_snd_2472_);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_snd_2472_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_cache_2474_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_zetaDeltaFVarIds_2475_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_postponed_2476_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_diag_2477_);
v___x_2482_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_st_ref_set(v___y_2464_, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_fst_2471_);
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2488_, v___y_2489_);
lean_dec(v___y_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2492_, v___y_2494_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2508_ = lean_unsigned_to_nat(113u);
v___x_2509_ = lean_unsigned_to_nat(214u);
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2512_ = l_mkPanicMessageWithDecl(v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_, v___x_2507_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2513_, size_t v_sz_2514_, size_t v_i_2515_, lean_object* v_bs_2516_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_usize_dec_lt(v_i_2515_, v_sz_2514_);
if (v___x_2517_ == 0)
{
return v_bs_2516_;
}
else
{
lean_object* v_v_2518_; lean_object* v___x_2519_; lean_object* v_bs_x27_2520_; lean_object* v___y_2522_; lean_object* v___x_2527_; 
v_v_2518_ = lean_array_uget(v_bs_2516_, v_i_2515_);
v___x_2519_ = lean_unsigned_to_nat(0u);
v_bs_x27_2520_ = lean_array_uset(v_bs_2516_, v_i_2515_, v___x_2519_);
v___x_2527_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2513_, v_v_2518_);
lean_dec(v_v_2518_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2529_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2528_);
v___y_2522_ = v___x_2529_;
goto v___jp_2521_;
}
else
{
lean_object* v_val_2530_; 
v_val_2530_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_val_2530_);
lean_dec_ref(v___x_2527_);
v___y_2522_ = v_val_2530_;
goto v___jp_2521_;
}
v___jp_2521_:
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)1ULL);
v___x_2524_ = lean_usize_add(v_i_2515_, v___x_2523_);
v___x_2525_ = lean_array_uset(v_bs_x27_2520_, v_i_2515_, v___y_2522_);
v_i_2515_ = v___x_2524_;
v_bs_2516_ = v___x_2525_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2531_, lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_bs_2534_){
_start:
{
size_t v_sz_boxed_2535_; size_t v_i_boxed_2536_; lean_object* v_res_2537_; 
v_sz_boxed_2535_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2536_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2531_, v_sz_boxed_2535_, v_i_boxed_2536_, v_bs_2534_);
lean_dec_ref(v___x_2531_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2538_, size_t v_i_2539_, lean_object* v_bs_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_usize_dec_lt(v_i_2539_, v_sz_2538_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_bs_2540_);
return v___x_2547_;
}
else
{
lean_object* v_v_2548_; lean_object* v___x_2549_; 
v_v_2548_ = lean_array_uget_borrowed(v_bs_2540_, v_i_2539_);
lean_inc(v_v_2548_);
v___x_2549_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2548_, v___y_2542_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v_bs_x27_2552_; size_t v___x_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v_bs_x27_2552_ = lean_array_uset(v_bs_2540_, v_i_2539_, v___x_2551_);
v___x_2553_ = ((size_t)1ULL);
v___x_2554_ = lean_usize_add(v_i_2539_, v___x_2553_);
v___x_2555_ = lean_array_uset(v_bs_x27_2552_, v_i_2539_, v_a_2550_);
v_i_2539_ = v___x_2554_;
v_bs_2540_ = v___x_2555_;
goto _start;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_bs_2540_);
v_a_2557_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2549_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2549_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2565_, lean_object* v_i_2566_, lean_object* v_bs_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
size_t v_sz_boxed_2573_; size_t v_i_boxed_2574_; lean_object* v_res_2575_; 
v_sz_boxed_2573_ = lean_unbox_usize(v_sz_2565_);
lean_dec(v_sz_2565_);
v_i_boxed_2574_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2573_, v_i_boxed_2574_, v_bs_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2575_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2576_, lean_object* v___x_2577_, lean_object* v_as_2578_, size_t v_i_2579_, size_t v_stop_2580_){
_start:
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_usize_dec_eq(v_i_2579_, v_stop_2580_);
if (v___x_2581_ == 0)
{
uint8_t v___x_2582_; uint8_t v___y_2584_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2582_ = 1;
v___x_2588_ = lean_array_uget_borrowed(v_as_2578_, v_i_2579_);
v___x_2589_ = l_Lean_Expr_isFVar(v___x_2588_);
if (v___x_2589_ == 0)
{
v___y_2584_ = v_a_2576_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_nat_dec_eq(v___x_2577_, v___x_2590_);
v___y_2584_ = v___x_2591_;
goto v___jp_2583_;
}
v___jp_2583_:
{
if (v___y_2584_ == 0)
{
size_t v___x_2585_; size_t v___x_2586_; 
v___x_2585_ = ((size_t)1ULL);
v___x_2586_ = lean_usize_add(v_i_2579_, v___x_2585_);
v_i_2579_ = v___x_2586_;
goto _start;
}
else
{
return v___x_2582_;
}
}
}
else
{
uint8_t v___x_2592_; 
v___x_2592_ = 0;
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2593_, lean_object* v___x_2594_, lean_object* v_as_2595_, lean_object* v_i_2596_, lean_object* v_stop_2597_){
_start:
{
uint8_t v_a_9872__boxed_2598_; size_t v_i_boxed_2599_; size_t v_stop_boxed_2600_; uint8_t v_res_2601_; lean_object* v_r_2602_; 
v_a_9872__boxed_2598_ = lean_unbox(v_a_2593_);
v_i_boxed_2599_ = lean_unbox_usize(v_i_2596_);
lean_dec(v_i_2596_);
v_stop_boxed_2600_ = lean_unbox_usize(v_stop_2597_);
lean_dec(v_stop_2597_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9872__boxed_2598_, v___x_2594_, v_as_2595_, v_i_boxed_2599_, v_stop_boxed_2600_);
lean_dec_ref(v_as_2595_);
lean_dec(v___x_2594_);
v_r_2602_ = lean_box(v_res_2601_);
return v_r_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2603_, lean_object* v___x_2604_, lean_object* v_ys_2605_, lean_object* v___x_2606_, lean_object* v_recArgInfo_2607_, lean_object* v___x_2608_, lean_object* v_group_2609_, lean_object* v_as_2610_, size_t v_sz_2611_, size_t v_i_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_a_2620_; uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_b_2613_);
return v___x_2625_;
}
else
{
lean_object* v_snd_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2784_; 
v_snd_2626_ = lean_ctor_get(v_b_2613_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_b_2613_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v_b_2613_, 0);
lean_dec(v_unused_2785_);
v___x_2628_ = v_b_2613_;
v_isShared_2629_ = v_isSharedCheck_2784_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snd_2626_);
lean_dec(v_b_2613_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2784_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_next_2630_; lean_object* v_upperBound_2631_; lean_object* v___x_2632_; 
v_next_2630_ = lean_ctor_get(v_snd_2626_, 0);
lean_inc(v_next_2630_);
v_upperBound_2631_ = lean_ctor_get(v_snd_2626_, 1);
v___x_2632_ = lean_box(0);
if (lean_obj_tag(v_next_2630_) == 0)
{
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
goto v___jp_2633_;
}
else
{
lean_object* v_val_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2783_; 
v_val_2638_ = lean_ctor_get(v_next_2630_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_next_2630_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2640_ = v_next_2630_;
v_isShared_2641_ = v_isSharedCheck_2783_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_val_2638_);
lean_dec(v_next_2630_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2783_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_lt(v_val_2638_, v_upperBound_2631_);
if (v___x_2642_ == 0)
{
lean_del_object(v___x_2640_);
lean_dec(v_val_2638_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
goto v___jp_2633_;
}
else
{
lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2780_; 
lean_inc(v_upperBound_2631_);
lean_del_object(v___x_2628_);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_snd_2626_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; lean_object* v_unused_2782_; 
v_unused_2781_ = lean_ctor_get(v_snd_2626_, 1);
lean_dec(v_unused_2781_);
v_unused_2782_ = lean_ctor_get(v_snd_2626_, 0);
lean_dec(v_unused_2782_);
v___x_2644_ = v_snd_2626_;
v_isShared_2645_ = v_isSharedCheck_2780_;
goto v_resetjp_2643_;
}
else
{
lean_dec(v_snd_2626_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2780_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; 
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc_ref(v___x_2603_);
v___x_2646_ = lean_infer_type(v___x_2603_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___x_2646_);
v___x_2648_ = l_Lean_Meta_whnfD(v_a_2647_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_a_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v_a_2650_ = lean_array_uget_borrowed(v_as_2610_, v_i_2612_);
v___x_2651_ = 0;
lean_inc(v_a_2650_);
v___x_2652_ = l_Lean_Meta_forallMetaTelescope(v_a_2650_, v___x_2651_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_snd_2654_; lean_object* v_fst_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2755_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v_snd_2654_ = lean_ctor_get(v_a_2653_, 1);
v_fst_2655_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2657_ = v_a_2653_;
v_isShared_2658_ = v_isSharedCheck_2755_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2654_);
lean_inc(v_fst_2655_);
lean_dec(v_a_2653_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2755_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2753_; 
v_snd_2659_ = lean_ctor_get(v_snd_2654_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_snd_2654_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v_snd_2654_, 0);
lean_dec(v_unused_2754_);
v___x_2661_ = v_snd_2654_;
v_isShared_2662_ = v_isSharedCheck_2753_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_dec(v_snd_2654_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2753_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2659_, v_a_2649_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_val_2638_, v___x_2665_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2666_);
v___x_2668_ = v___x_2640_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2668_);
v___x_2670_ = v___x_2644_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_upperBound_2631_);
v___x_2670_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_unbox(v_a_2664_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2673_; 
lean_dec(v_a_2664_);
lean_del_object(v___x_2657_);
lean_dec(v_fst_2655_);
lean_dec(v_val_2638_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2670_);
lean_ctor_set(v___x_2661_, 0, v___x_2632_);
v___x_2673_ = v___x_2661_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2670_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
v_a_2620_ = v___x_2673_;
goto v___jp_2619_;
}
}
else
{
size_t v_sz_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v_sz_2675_ = lean_array_size(v_fst_2655_);
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2675_, v___x_2676_, v_fst_2655_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2683_; uint8_t v___x_2684_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_nat_dec_eq(v___x_2604_, v___x_2683_);
v___x_2730_ = lean_array_get_size(v_a_2678_);
v___x_2731_ = lean_nat_dec_lt(v___x_2683_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec(v_a_2664_);
goto v___jp_2685_;
}
else
{
if (v___x_2731_ == 0)
{
lean_dec(v_a_2664_);
goto v___jp_2685_;
}
else
{
size_t v___x_2732_; uint8_t v___x_2733_; uint8_t v___x_2734_; 
v___x_2732_ = lean_usize_of_nat(v___x_2730_);
v___x_2733_ = lean_unbox(v_a_2664_);
lean_dec(v_a_2664_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2733_, v___x_2604_, v_a_2678_, v___x_2676_, v___x_2732_);
if (v___x_2734_ == 0)
{
goto v___jp_2685_;
}
else
{
if (v___x_2684_ == 0)
{
lean_dec(v_a_2678_);
lean_del_object(v___x_2657_);
lean_dec(v_val_2638_);
goto v___jp_2679_;
}
else
{
goto v___jp_2685_;
}
}
}
}
v___jp_2679_:
{
lean_object* v___x_2681_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2670_);
lean_ctor_set(v___x_2661_, 0, v___x_2632_);
v___x_2681_ = v___x_2661_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2670_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v_a_2620_ = v___x_2681_;
goto v___jp_2619_;
}
}
v___jp_2685_:
{
if (v___x_2684_ == 0)
{
uint8_t v___x_2686_; 
lean_del_object(v___x_2661_);
v___x_2686_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2678_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2688_; 
lean_dec(v_a_2678_);
lean_dec(v_val_2638_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2670_);
lean_ctor_set(v___x_2657_, 0, v___x_2632_);
v___x_2688_ = v___x_2657_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2670_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v_a_2620_ = v___x_2688_;
goto v___jp_2619_;
}
}
else
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2605_, v_a_2678_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2721_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2721_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2721_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
if (lean_obj_tag(v_a_2691_) == 1)
{
lean_object* v___x_2696_; 
lean_dec_ref(v_a_2691_);
lean_del_object(v___x_2693_);
lean_dec(v_a_2678_);
lean_dec(v_val_2638_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2670_);
lean_ctor_set(v___x_2657_, 0, v___x_2632_);
v___x_2696_ = v___x_2657_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2670_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
v_a_2620_ = v___x_2696_;
goto v___jp_2619_;
}
}
else
{
lean_object* v_fnName_2698_; lean_object* v_fixedParamPerm_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2691_);
lean_dec_ref(v___x_2603_);
v_fnName_2698_ = lean_ctor_get(v_recArgInfo_2607_, 0);
v_fixedParamPerm_2699_ = lean_ctor_get(v_recArgInfo_2607_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_recArgInfo_2607_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; lean_object* v_unused_2720_; 
v_unused_2717_ = lean_ctor_get(v_recArgInfo_2607_, 5);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2607_, 4);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_recArgInfo_2607_, 3);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_recArgInfo_2607_, 2);
lean_dec(v_unused_2720_);
v___x_2701_ = v_recArgInfo_2607_;
v_isShared_2702_ = v_isSharedCheck_2716_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fixedParamPerm_2699_);
lean_inc(v_fnName_2698_);
lean_dec(v_recArgInfo_2607_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2716_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
size_t v_sz_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v_sz_2703_ = lean_array_size(v_a_2678_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2606_, v_sz_2703_, v___x_2676_, v_a_2678_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 5, v_val_2638_);
lean_ctor_set(v___x_2701_, 4, v_group_2609_);
lean_ctor_set(v___x_2701_, 3, v___x_2704_);
lean_ctor_set(v___x_2701_, 2, v___x_2608_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_fnName_2698_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_fixedParamPerm_2699_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_group_2609_);
lean_ctor_set(v_reuseFailAlloc_2715_, 5, v_val_2638_);
v___x_2706_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2670_);
lean_ctor_set(v___x_2657_, 0, v___x_2708_);
v___x_2710_ = v___x_2657_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2670_);
v___x_2710_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2712_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2710_);
v___x_2712_ = v___x_2693_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2678_);
lean_dec_ref(v___x_2670_);
lean_del_object(v___x_2657_);
lean_dec(v_val_2638_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2722_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2690_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2690_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
else
{
lean_dec(v_a_2678_);
lean_del_object(v___x_2657_);
lean_dec(v_val_2638_);
goto v___jp_2679_;
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v___x_2670_);
lean_dec(v_a_2664_);
lean_del_object(v___x_2661_);
lean_del_object(v___x_2657_);
lean_dec(v_val_2638_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2735_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2677_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2677_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_del_object(v___x_2661_);
lean_del_object(v___x_2657_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2644_);
lean_del_object(v___x_2640_);
lean_dec(v_val_2638_);
lean_dec(v_upperBound_2631_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2745_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2663_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2663_);
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
lean_dec(v_a_2649_);
lean_del_object(v___x_2644_);
lean_del_object(v___x_2640_);
lean_dec(v_val_2638_);
lean_dec(v_upperBound_2631_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2756_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2652_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2652_);
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
lean_del_object(v___x_2644_);
lean_del_object(v___x_2640_);
lean_dec(v_val_2638_);
lean_dec(v_upperBound_2631_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2764_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2648_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2648_);
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
lean_del_object(v___x_2644_);
lean_del_object(v___x_2640_);
lean_dec(v_val_2638_);
lean_dec(v_upperBound_2631_);
lean_dec_ref(v_group_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v_recArgInfo_2607_);
lean_dec_ref(v___x_2603_);
v_a_2772_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2646_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2646_);
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
v___jp_2633_:
{
lean_object* v___x_2635_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2632_);
v___x_2635_ = v___x_2628_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_snd_2626_);
v___x_2635_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
}
}
v___jp_2619_:
{
size_t v___x_2621_; size_t v___x_2622_; 
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2612_, v___x_2621_);
v_i_2612_ = v___x_2622_;
v_b_2613_ = v_a_2620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v_ys_2788_, lean_object* v___x_2789_, lean_object* v_recArgInfo_2790_, lean_object* v___x_2791_, lean_object* v_group_2792_, lean_object* v_as_2793_, lean_object* v_sz_2794_, lean_object* v_i_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
size_t v_sz_boxed_2802_; size_t v_i_boxed_2803_; lean_object* v_res_2804_; 
v_sz_boxed_2802_ = lean_unbox_usize(v_sz_2794_);
lean_dec(v_sz_2794_);
v_i_boxed_2803_ = lean_unbox_usize(v_i_2795_);
lean_dec(v_i_2795_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2786_, v___x_2787_, v_ys_2788_, v___x_2789_, v_recArgInfo_2790_, v___x_2791_, v_group_2792_, v_as_2793_, v_sz_boxed_2802_, v_i_boxed_2803_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_as_2793_);
lean_dec_ref(v___x_2789_);
lean_dec_ref(v_ys_2788_);
lean_dec(v___x_2787_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v_ys_2808_, lean_object* v_recArgInfo_2809_, lean_object* v___x_2810_, lean_object* v_group_2811_, lean_object* v_as_2812_, size_t v_sz_2813_, size_t v_i_2814_, lean_object* v_b_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_a_2822_; uint8_t v___x_2826_; 
v___x_2826_ = lean_usize_dec_lt(v_i_2814_, v_sz_2813_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_b_2815_);
return v___x_2827_;
}
else
{
lean_object* v_snd_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2986_; 
v_snd_2828_ = lean_ctor_get(v_b_2815_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_b_2815_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_b_2815_, 0);
lean_dec(v_unused_2987_);
v___x_2830_ = v_b_2815_;
v_isShared_2831_ = v_isSharedCheck_2986_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_snd_2828_);
lean_dec(v_b_2815_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2986_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_next_2832_; lean_object* v_upperBound_2833_; lean_object* v___x_2834_; 
v_next_2832_ = lean_ctor_get(v_snd_2828_, 0);
lean_inc(v_next_2832_);
v_upperBound_2833_ = lean_ctor_get(v_snd_2828_, 1);
v___x_2834_ = lean_box(0);
if (lean_obj_tag(v_next_2832_) == 0)
{
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
goto v___jp_2835_;
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2985_; 
v_val_2840_ = lean_ctor_get(v_next_2832_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_next_2832_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2842_ = v_next_2832_;
v_isShared_2843_ = v_isSharedCheck_2985_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_val_2840_);
lean_dec(v_next_2832_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2985_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_nat_dec_lt(v_val_2840_, v_upperBound_2833_);
if (v___x_2844_ == 0)
{
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
goto v___jp_2835_;
}
else
{
lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2982_; 
lean_inc(v_upperBound_2833_);
lean_del_object(v___x_2830_);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_snd_2828_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; lean_object* v_unused_2984_; 
v_unused_2983_ = lean_ctor_get(v_snd_2828_, 1);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_snd_2828_, 0);
lean_dec(v_unused_2984_);
v___x_2846_ = v_snd_2828_;
v_isShared_2847_ = v_isSharedCheck_2982_;
goto v_resetjp_2845_;
}
else
{
lean_dec(v_snd_2828_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2982_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; 
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc_ref(v___x_2805_);
v___x_2848_ = lean_infer_type(v___x_2805_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = l_Lean_Meta_whnfD(v_a_2849_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_a_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v_a_2852_ = lean_array_uget_borrowed(v_as_2812_, v_i_2814_);
v___x_2853_ = 0;
lean_inc(v_a_2852_);
v___x_2854_ = l_Lean_Meta_forallMetaTelescope(v_a_2852_, v___x_2853_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_snd_2856_; lean_object* v_fst_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2957_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2854_);
v_snd_2856_ = lean_ctor_get(v_a_2855_, 1);
v_fst_2857_ = lean_ctor_get(v_a_2855_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2859_ = v_a_2855_;
v_isShared_2860_ = v_isSharedCheck_2957_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snd_2856_);
lean_inc(v_fst_2857_);
lean_dec(v_a_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2957_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_snd_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2955_; 
v_snd_2861_ = lean_ctor_get(v_snd_2856_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_snd_2856_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v_snd_2856_, 0);
lean_dec(v_unused_2956_);
v___x_2863_ = v_snd_2856_;
v_isShared_2864_ = v_isSharedCheck_2955_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_snd_2861_);
lean_dec(v_snd_2856_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2955_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2861_, v_a_2851_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_add(v_val_2840_, v___x_2867_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2868_);
v___x_2870_ = v___x_2842_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2870_);
v___x_2872_ = v___x_2846_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_upperBound_2833_);
v___x_2872_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_unbox(v_a_2866_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v_a_2866_);
lean_del_object(v___x_2859_);
lean_dec(v_fst_2857_);
lean_dec(v_val_2840_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2872_);
lean_ctor_set(v___x_2863_, 0, v___x_2834_);
v___x_2875_ = v___x_2863_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2872_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
v_a_2822_ = v___x_2875_;
goto v___jp_2821_;
}
}
else
{
size_t v_sz_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v_sz_2877_ = lean_array_size(v_fst_2857_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2877_, v___x_2878_, v_fst_2857_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = lean_nat_dec_eq(v___x_2806_, v___x_2885_);
v___x_2932_ = lean_array_get_size(v_a_2880_);
v___x_2933_ = lean_nat_dec_lt(v___x_2885_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_dec(v_a_2866_);
goto v___jp_2887_;
}
else
{
if (v___x_2933_ == 0)
{
lean_dec(v_a_2866_);
goto v___jp_2887_;
}
else
{
size_t v___x_2934_; uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_usize_of_nat(v___x_2932_);
v___x_2935_ = lean_unbox(v_a_2866_);
lean_dec(v_a_2866_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2935_, v___x_2806_, v_a_2880_, v___x_2878_, v___x_2934_);
if (v___x_2936_ == 0)
{
goto v___jp_2887_;
}
else
{
if (v___x_2886_ == 0)
{
lean_dec(v_a_2880_);
lean_del_object(v___x_2859_);
lean_dec(v_val_2840_);
goto v___jp_2881_;
}
else
{
goto v___jp_2887_;
}
}
}
}
v___jp_2881_:
{
lean_object* v___x_2883_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2872_);
lean_ctor_set(v___x_2863_, 0, v___x_2834_);
v___x_2883_ = v___x_2863_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2872_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2822_ = v___x_2883_;
goto v___jp_2821_;
}
}
v___jp_2887_:
{
if (v___x_2886_ == 0)
{
uint8_t v___x_2888_; 
lean_del_object(v___x_2863_);
v___x_2888_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2880_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_a_2880_);
lean_dec(v_val_2840_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2872_);
lean_ctor_set(v___x_2859_, 0, v___x_2834_);
v___x_2890_ = v___x_2859_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2872_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
v_a_2822_ = v___x_2890_;
goto v___jp_2821_;
}
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2808_, v_a_2880_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2923_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2923_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2923_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
if (lean_obj_tag(v_a_2893_) == 1)
{
lean_object* v___x_2898_; 
lean_dec_ref(v_a_2893_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2880_);
lean_dec(v_val_2840_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2872_);
lean_ctor_set(v___x_2859_, 0, v___x_2834_);
v___x_2898_ = v___x_2859_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2872_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
v_a_2822_ = v___x_2898_;
goto v___jp_2821_;
}
}
else
{
lean_object* v_fnName_2900_; lean_object* v_fixedParamPerm_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2893_);
lean_dec_ref(v___x_2805_);
v_fnName_2900_ = lean_ctor_get(v_recArgInfo_2809_, 0);
v_fixedParamPerm_2901_ = lean_ctor_get(v_recArgInfo_2809_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_recArgInfo_2809_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; 
v_unused_2919_ = lean_ctor_get(v_recArgInfo_2809_, 5);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_recArgInfo_2809_, 4);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_recArgInfo_2809_, 3);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_recArgInfo_2809_, 2);
lean_dec(v_unused_2922_);
v___x_2903_ = v_recArgInfo_2809_;
v_isShared_2904_ = v_isSharedCheck_2918_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_fixedParamPerm_2901_);
lean_inc(v_fnName_2900_);
lean_dec(v_recArgInfo_2809_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2918_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
size_t v_sz_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v_sz_2905_ = lean_array_size(v_a_2880_);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2807_, v_sz_2905_, v___x_2878_, v_a_2880_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 5, v_val_2840_);
lean_ctor_set(v___x_2903_, 4, v_group_2811_);
lean_ctor_set(v___x_2903_, 3, v___x_2906_);
lean_ctor_set(v___x_2903_, 2, v___x_2810_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_fnName_2900_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_fixedParamPerm_2901_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_group_2811_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_val_2840_);
v___x_2908_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2872_);
lean_ctor_set(v___x_2859_, 0, v___x_2910_);
v___x_2912_ = v___x_2859_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2872_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2912_);
v___x_2914_ = v___x_2895_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_a_2880_);
lean_dec_ref(v___x_2872_);
lean_del_object(v___x_2859_);
lean_dec(v_val_2840_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2924_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2892_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2892_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
else
{
lean_dec(v_a_2880_);
lean_del_object(v___x_2859_);
lean_dec(v_val_2840_);
goto v___jp_2881_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___x_2872_);
lean_dec(v_a_2866_);
lean_del_object(v___x_2863_);
lean_del_object(v___x_2859_);
lean_dec(v_val_2840_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2937_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2879_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2879_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_del_object(v___x_2863_);
lean_del_object(v___x_2859_);
lean_dec(v_fst_2857_);
lean_del_object(v___x_2846_);
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec(v_upperBound_2833_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2947_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2865_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2865_);
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
lean_dec(v_a_2851_);
lean_del_object(v___x_2846_);
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec(v_upperBound_2833_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2958_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2854_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2854_);
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
lean_del_object(v___x_2846_);
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec(v_upperBound_2833_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2966_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2850_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2850_);
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
lean_del_object(v___x_2846_);
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec(v_upperBound_2833_);
lean_dec_ref(v_group_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_recArgInfo_2809_);
lean_dec_ref(v___x_2805_);
v_a_2974_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2848_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2848_);
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
v___jp_2835_:
{
lean_object* v___x_2837_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2834_);
v___x_2837_ = v___x_2830_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_snd_2828_);
v___x_2837_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
}
}
v___jp_2821_:
{
size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2814_, v___x_2823_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2805_, v___x_2806_, v_ys_2808_, v___x_2807_, v_recArgInfo_2809_, v___x_2810_, v_group_2811_, v_as_2812_, v_sz_2813_, v___x_2824_, v_a_2822_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object* v___x_2988_, lean_object* v___x_2989_, lean_object* v___x_2990_, lean_object* v_ys_2991_, lean_object* v_recArgInfo_2992_, lean_object* v___x_2993_, lean_object* v_group_2994_, lean_object* v_as_2995_, lean_object* v_sz_2996_, lean_object* v_i_2997_, lean_object* v_b_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
size_t v_sz_boxed_3004_; size_t v_i_boxed_3005_; lean_object* v_res_3006_; 
v_sz_boxed_3004_ = lean_unbox_usize(v_sz_2996_);
lean_dec(v_sz_2996_);
v_i_boxed_3005_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2988_, v___x_2989_, v___x_2990_, v_ys_2991_, v_recArgInfo_2992_, v___x_2993_, v_group_2994_, v_as_2995_, v_sz_boxed_3004_, v_i_boxed_3005_, v_b_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_as_2995_);
lean_dec_ref(v_ys_2991_);
lean_dec_ref(v___x_2990_);
lean_dec(v___x_2989_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3007_, lean_object* v_xs_3008_, lean_object* v_recArgPos_3009_, lean_object* v_a_3010_, lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_ys_3013_, lean_object* v_x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_toIndGroupInfo_3020_; lean_object* v_all_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3060_; 
v_toIndGroupInfo_3020_ = lean_ctor_get(v_group_3007_, 0);
lean_inc_ref(v_toIndGroupInfo_3020_);
v_all_3021_ = lean_ctor_get(v_toIndGroupInfo_3020_, 0);
v___x_3022_ = l_Lean_instInhabitedExpr;
v___x_3023_ = l_Array_append___redArg(v_xs_3008_, v_ys_3013_);
v___x_3024_ = lean_array_get(v___x_3022_, v___x_3023_, v_recArgPos_3009_);
v___x_3025_ = lean_array_get_size(v_all_3021_);
v___x_3026_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3020_);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_toIndGroupInfo_3020_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; lean_object* v_unused_3062_; 
v_unused_3061_ = lean_ctor_get(v_toIndGroupInfo_3020_, 1);
lean_dec(v_unused_3061_);
v_unused_3062_ = lean_ctor_get(v_toIndGroupInfo_3020_, 0);
lean_dec(v_unused_3062_);
v___x_3028_ = v_toIndGroupInfo_3020_;
v_isShared_3029_ = v_isSharedCheck_3060_;
goto v_resetjp_3027_;
}
else
{
lean_dec(v_toIndGroupInfo_3020_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3060_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3025_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3032_ = v___x_3028_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3026_);
v___x_3032_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; size_t v_sz_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
v_sz_3035_ = lean_array_size(v_a_3010_);
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3024_, v___x_3011_, v___x_3023_, v_ys_3013_, v___x_3012_, v_recArgPos_3009_, v_group_3007_, v_a_3010_, v_sz_3035_, v___x_3036_, v___x_3034_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec_ref(v___x_3023_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3050_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3050_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3050_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; 
v_fst_3042_ = lean_ctor_get(v_a_3038_, 0);
lean_inc(v_fst_3042_);
lean_dec(v_a_3038_);
if (lean_obj_tag(v_fst_3042_) == 0)
{
lean_object* v___x_3044_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3033_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3033_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_object* v_val_3046_; lean_object* v___x_3048_; 
v_val_3046_ = lean_ctor_get(v_fst_3042_, 0);
lean_inc(v_val_3046_);
lean_dec_ref(v_fst_3042_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_val_3046_);
v___x_3048_ = v___x_3040_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_val_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3037_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3037_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3063_, lean_object* v_xs_3064_, lean_object* v_recArgPos_3065_, lean_object* v_a_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v_ys_3069_, lean_object* v_x_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3063_, v_xs_3064_, v_recArgPos_3065_, v_a_3066_, v___x_3067_, v___x_3068_, v_ys_3069_, v_x_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_x_3070_);
lean_dec_ref(v_ys_3069_);
lean_dec(v___x_3067_);
lean_dec_ref(v_a_3066_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3077_, lean_object* v_a_3078_, lean_object* v_xs_3079_, lean_object* v_value_3080_, lean_object* v_as_3081_, size_t v_i_3082_, size_t v_stop_3083_, lean_object* v_b_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_a_3091_; lean_object* v_val_3096_; uint8_t v___x_3098_; 
v___x_3098_ = lean_usize_dec_eq(v_i_3082_, v_stop_3083_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v_recArgPos_3100_; lean_object* v_indGroupInst_3101_; lean_object* v___x_3102_; 
v___x_3099_ = lean_array_uget_borrowed(v_as_3081_, v_i_3082_);
v_recArgPos_3100_ = lean_ctor_get(v___x_3099_, 2);
v_indGroupInst_3101_ = lean_ctor_get(v___x_3099_, 4);
lean_inc_ref(v_indGroupInst_3101_);
lean_inc_ref(v_group_3077_);
v___x_3102_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3077_, v_indGroupInst_3101_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; uint8_t v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___x_3102_);
v___x_3104_ = lean_unbox(v_a_3103_);
lean_dec(v_a_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3105_ = lean_array_get_size(v_a_3078_);
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = lean_nat_dec_eq(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___f_3108_; lean_object* v___x_3109_; 
lean_inc(v___x_3099_);
lean_inc_ref(v_a_3078_);
lean_inc(v_recArgPos_3100_);
lean_inc_ref(v_xs_3079_);
lean_inc_ref(v_group_3077_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3108_, 0, v_group_3077_);
lean_closure_set(v___f_3108_, 1, v_xs_3079_);
lean_closure_set(v___f_3108_, 2, v_recArgPos_3100_);
lean_closure_set(v___f_3108_, 3, v_a_3078_);
lean_closure_set(v___f_3108_, 4, v___x_3105_);
lean_closure_set(v___f_3108_, 5, v___x_3099_);
lean_inc_ref(v_value_3080_);
v___x_3109_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3080_, v___f_3108_, v___x_3107_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
if (lean_obj_tag(v_a_3110_) == 0)
{
v_a_3091_ = v_b_3084_;
goto v___jp_3090_;
}
else
{
lean_object* v_val_3111_; 
v_val_3111_ = lean_ctor_get(v_a_3110_, 0);
lean_inc(v_val_3111_);
lean_dec_ref(v_a_3110_);
v_val_3096_ = v_val_3111_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v_b_3084_);
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v_a_3112_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3109_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3109_);
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
else
{
v_a_3091_ = v_b_3084_;
goto v___jp_3090_;
}
}
else
{
lean_inc(v___x_3099_);
v_val_3096_ = v___x_3099_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_b_3084_);
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v_a_3120_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3102_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3102_);
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
lean_object* v___x_3128_; 
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_b_3084_);
return v___x_3128_;
}
v___jp_3090_:
{
size_t v___x_3092_; size_t v___x_3093_; 
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_add(v_i_3082_, v___x_3092_);
v_i_3082_ = v___x_3093_;
v_b_3084_ = v_a_3091_;
goto _start;
}
v___jp_3095_:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_array_push(v_b_3084_, v_val_3096_);
v_a_3091_ = v___x_3097_;
goto v___jp_3090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3129_, lean_object* v_a_3130_, lean_object* v_xs_3131_, lean_object* v_value_3132_, lean_object* v_as_3133_, lean_object* v_i_3134_, lean_object* v_stop_3135_, lean_object* v_b_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
size_t v_i_boxed_3142_; size_t v_stop_boxed_3143_; lean_object* v_res_3144_; 
v_i_boxed_3142_ = lean_unbox_usize(v_i_3134_);
lean_dec(v_i_3134_);
v_stop_boxed_3143_ = lean_unbox_usize(v_stop_3135_);
lean_dec(v_stop_3135_);
v_res_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3129_, v_a_3130_, v_xs_3131_, v_value_3132_, v_as_3133_, v_i_boxed_3142_, v_stop_boxed_3143_, v_b_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec_ref(v_as_3133_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3145_, lean_object* v_a_3146_, lean_object* v_xs_3147_, lean_object* v_value_3148_, lean_object* v_as_3149_, lean_object* v_start_3150_, lean_object* v_stop_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3158_ = lean_nat_dec_lt(v_start_3150_, v_stop_3151_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref(v_value_3148_);
lean_dec_ref(v_xs_3147_);
lean_dec_ref(v_a_3146_);
lean_dec_ref(v_group_3145_);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = lean_array_get_size(v_as_3149_);
v___x_3161_ = lean_nat_dec_le(v_stop_3151_, v___x_3160_);
if (v___x_3161_ == 0)
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_nat_dec_lt(v_start_3150_, v___x_3160_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec_ref(v_value_3148_);
lean_dec_ref(v_xs_3147_);
lean_dec_ref(v_a_3146_);
lean_dec_ref(v_group_3145_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3157_);
return v___x_3163_;
}
else
{
size_t v___x_3164_; size_t v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_usize_of_nat(v_start_3150_);
v___x_3165_ = lean_usize_of_nat(v___x_3160_);
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3145_, v_a_3146_, v_xs_3147_, v_value_3148_, v_as_3149_, v___x_3164_, v___x_3165_, v___x_3157_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3166_;
}
}
else
{
size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_usize_of_nat(v_start_3150_);
v___x_3168_ = lean_usize_of_nat(v_stop_3151_);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3145_, v_a_3146_, v_xs_3147_, v_value_3148_, v_as_3149_, v___x_3167_, v___x_3168_, v___x_3157_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3170_, lean_object* v_a_3171_, lean_object* v_xs_3172_, lean_object* v_value_3173_, lean_object* v_as_3174_, lean_object* v_start_3175_, lean_object* v_stop_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3170_, v_a_3171_, v_xs_3172_, v_value_3173_, v_as_3174_, v_start_3175_, v_stop_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v_stop_3176_);
lean_dec(v_start_3175_);
lean_dec_ref(v_as_3174_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3183_, lean_object* v_xs_3184_, lean_object* v_value_3185_, lean_object* v_recArgInfos_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; 
lean_inc_ref(v_group_3183_);
v___x_3192_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3183_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = lean_array_get_size(v_recArgInfos_3186_);
v___x_3196_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3183_, v_a_3193_, v_xs_3184_, v_value_3185_, v_recArgInfos_3186_, v___x_3194_, v___x_3195_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3196_;
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v_value_3185_);
lean_dec_ref(v_xs_3184_);
lean_dec_ref(v_group_3183_);
v_a_3197_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3192_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3192_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3205_, lean_object* v_xs_3206_, lean_object* v_value_3207_, lean_object* v_recArgInfos_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Elab_Structural_argsInGroup(v_group_3205_, v_xs_3206_, v_value_3207_, v_recArgInfos_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec_ref(v_recArgInfos_3208_);
return v_res_3214_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_unsigned_to_nat(10u);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3218_, lean_object* v_i_3219_, lean_object* v_acc_3220_){
_start:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = lean_array_get_size(v_xss_3218_);
v___x_3222_ = lean_nat_dec_lt(v_i_3219_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_unsigned_to_nat(1u);
v___x_3224_ = lean_mk_empty_array_with_capacity(v___x_3223_);
v___x_3225_ = lean_array_push(v___x_3224_, v_acc_3220_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3226_ = lean_array_fget_borrowed(v_xss_3218_, v_i_3219_);
v___x_3227_ = lean_unsigned_to_nat(0u);
v___x_3228_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3229_ = lean_array_get_size(v___x_3226_);
v___x_3230_ = lean_nat_dec_lt(v___x_3227_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_dec_ref(v_acc_3220_);
return v___x_3228_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_nat_dec_le(v___x_3229_, v___x_3229_);
if (v___x_3231_ == 0)
{
if (v___x_3230_ == 0)
{
lean_dec_ref(v_acc_3220_);
return v___x_3228_;
}
else
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((size_t)0ULL);
v___x_3233_ = lean_usize_of_nat(v___x_3229_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3219_, v_acc_3220_, v_xss_3218_, v___x_3226_, v___x_3232_, v___x_3233_, v___x_3228_);
return v___x_3234_;
}
}
else
{
size_t v___x_3235_; size_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = ((size_t)0ULL);
v___x_3236_ = lean_usize_of_nat(v___x_3229_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3219_, v_acc_3220_, v_xss_3218_, v___x_3226_, v___x_3235_, v___x_3236_, v___x_3228_);
return v___x_3237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3238_, lean_object* v_acc_3239_, lean_object* v_xss_3240_, lean_object* v_as_3241_, size_t v_i_3242_, size_t v_stop_3243_, lean_object* v_b_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_eq(v_i_3242_, v_stop_3243_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; size_t v___x_3252_; size_t v___x_3253_; 
v___x_3246_ = lean_array_uget_borrowed(v_as_3241_, v_i_3242_);
v___x_3247_ = lean_unsigned_to_nat(1u);
v___x_3248_ = lean_nat_add(v_i_3238_, v___x_3247_);
lean_inc(v___x_3246_);
lean_inc_ref(v_acc_3239_);
v___x_3249_ = lean_array_push(v_acc_3239_, v___x_3246_);
v___x_3250_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3240_, v___x_3248_, v___x_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = l_Array_append___redArg(v_b_3244_, v___x_3250_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = ((size_t)1ULL);
v___x_3253_ = lean_usize_add(v_i_3242_, v___x_3252_);
v_i_3242_ = v___x_3253_;
v_b_3244_ = v___x_3251_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3239_);
return v_b_3244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3255_, lean_object* v_acc_3256_, lean_object* v_xss_3257_, lean_object* v_as_3258_, lean_object* v_i_3259_, lean_object* v_stop_3260_, lean_object* v_b_3261_){
_start:
{
size_t v_i_boxed_3262_; size_t v_stop_boxed_3263_; lean_object* v_res_3264_; 
v_i_boxed_3262_ = lean_unbox_usize(v_i_3259_);
lean_dec(v_i_3259_);
v_stop_boxed_3263_ = lean_unbox_usize(v_stop_3260_);
lean_dec(v_stop_3260_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3255_, v_acc_3256_, v_xss_3257_, v_as_3258_, v_i_boxed_3262_, v_stop_boxed_3263_, v_b_3261_);
lean_dec_ref(v_as_3258_);
lean_dec_ref(v_xss_3257_);
lean_dec(v_i_3255_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3265_, lean_object* v_i_3266_, lean_object* v_acc_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3265_, v_i_3266_, v_acc_3267_);
lean_dec(v_i_3266_);
lean_dec_ref(v_xss_3265_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3269_, lean_object* v_xss_3270_, lean_object* v_i_3271_, lean_object* v_acc_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3270_, v_i_3271_, v_acc_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3274_, lean_object* v_xss_3275_, lean_object* v_i_3276_, lean_object* v_acc_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3274_, v_xss_3275_, v_i_3276_, v_acc_3277_);
lean_dec(v_i_3276_);
lean_dec_ref(v_xss_3275_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3279_, lean_object* v_i_3280_, lean_object* v_acc_3281_, lean_object* v_xss_3282_, lean_object* v_as_3283_, size_t v_i_3284_, size_t v_stop_3285_, lean_object* v_b_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3280_, v_acc_3281_, v_xss_3282_, v_as_3283_, v_i_3284_, v_stop_3285_, v_b_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3288_, lean_object* v_i_3289_, lean_object* v_acc_3290_, lean_object* v_xss_3291_, lean_object* v_as_3292_, lean_object* v_i_3293_, lean_object* v_stop_3294_, lean_object* v_b_3295_){
_start:
{
size_t v_i_boxed_3296_; size_t v_stop_boxed_3297_; lean_object* v_res_3298_; 
v_i_boxed_3296_ = lean_unbox_usize(v_i_3293_);
lean_dec(v_i_3293_);
v_stop_boxed_3297_ = lean_unbox_usize(v_stop_3294_);
lean_dec(v_stop_3294_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3288_, v_i_3289_, v_acc_3290_, v_xss_3291_, v_as_3292_, v_i_boxed_3296_, v_stop_boxed_3297_, v_b_3295_);
lean_dec_ref(v_as_3292_);
lean_dec_ref(v_xss_3291_);
lean_dec(v_i_3289_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3299_, size_t v_i_3300_, size_t v_stop_3301_, lean_object* v_b_3302_){
_start:
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_usize_dec_eq(v_i_3300_, v_stop_3301_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; size_t v___x_3307_; size_t v___x_3308_; 
v___x_3304_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v___x_3305_ = lean_array_get_size(v___x_3304_);
v___x_3306_ = lean_nat_mul(v_b_3302_, v___x_3305_);
lean_dec(v_b_3302_);
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_add(v_i_3300_, v___x_3307_);
v_i_3300_ = v___x_3308_;
v_b_3302_ = v___x_3306_;
goto _start;
}
else
{
return v_b_3302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3310_, lean_object* v_i_3311_, lean_object* v_stop_3312_, lean_object* v_b_3313_){
_start:
{
size_t v_i_boxed_3314_; size_t v_stop_boxed_3315_; lean_object* v_res_3316_; 
v_i_boxed_3314_ = lean_unbox_usize(v_i_3311_);
lean_dec(v_i_3311_);
v_stop_boxed_3315_ = lean_unbox_usize(v_stop_3312_);
lean_dec(v_stop_3312_);
v_res_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3310_, v_i_boxed_3314_, v_stop_boxed_3315_, v_b_3313_);
lean_dec_ref(v_as_3310_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___y_3322_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3318_ = lean_unsigned_to_nat(10u);
v___x_3319_ = lean_unsigned_to_nat(1u);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_array_get_size(v_xss_3317_);
v___x_3329_ = lean_nat_dec_lt(v___x_3320_, v___x_3328_);
if (v___x_3329_ == 0)
{
v___y_3322_ = v___x_3319_;
goto v___jp_3321_;
}
else
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_nat_dec_le(v___x_3328_, v___x_3328_);
if (v___x_3330_ == 0)
{
if (v___x_3329_ == 0)
{
v___y_3322_ = v___x_3319_;
goto v___jp_3321_;
}
else
{
size_t v___x_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = lean_usize_of_nat(v___x_3328_);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3317_, v___x_3331_, v___x_3332_, v___x_3319_);
v___y_3322_ = v___x_3333_;
goto v___jp_3321_;
}
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3328_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3317_, v___x_3334_, v___x_3335_, v___x_3319_);
v___y_3322_ = v___x_3336_;
goto v___jp_3321_;
}
}
v___jp_3321_:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_nat_dec_lt(v___x_3318_, v___y_3322_);
lean_dec(v___y_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3325_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3317_, v___x_3320_, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_box(0);
return v___x_3327_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_as_3359_, size_t v_i_3360_, size_t v_stop_3361_, lean_object* v_b_3362_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6___boxed(lean_object* v_as_3369_, lean_object* v_i_3370_, lean_object* v_stop_3371_, lean_object* v_b_3372_){
_start:
{
size_t v_i_boxed_3373_; size_t v_stop_boxed_3374_; lean_object* v_res_3375_; 
v_i_boxed_3373_ = lean_unbox_usize(v_i_3370_);
lean_dec(v_i_3370_);
v_stop_boxed_3374_ = lean_unbox_usize(v_stop_3371_);
lean_dec(v_stop_3371_);
v_res_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v_as_3369_, v_i_boxed_3373_, v_stop_boxed_3374_, v_b_3372_);
lean_dec_ref(v_as_3369_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(lean_object* v_a_3376_, lean_object* v_as_3377_, size_t v_sz_3378_, size_t v_i_3379_, lean_object* v_b_3380_){
_start:
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_usize_dec_lt(v_i_3379_, v_sz_3378_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref(v_a_3376_);
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_b_3380_);
return v___x_3383_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; size_t v___x_3387_; size_t v___x_3388_; 
v_a_3384_ = lean_array_uget_borrowed(v_as_3377_, v_i_3379_);
lean_inc(v_a_3384_);
lean_inc_ref(v_a_3376_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_a_3376_);
lean_ctor_set(v___x_3385_, 1, v_a_3384_);
v___x_3386_ = lean_array_push(v_b_3380_, v___x_3385_);
v___x_3387_ = ((size_t)1ULL);
v___x_3388_ = lean_usize_add(v_i_3379_, v___x_3387_);
v_i_3379_ = v___x_3388_;
v_b_3380_ = v___x_3386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg___boxed(lean_object* v_a_3390_, lean_object* v_as_3391_, lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_){
_start:
{
size_t v_sz_boxed_3396_; size_t v_i_boxed_3397_; lean_object* v_res_3398_; 
v_sz_boxed_3396_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3397_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3390_, v_as_3391_, v_sz_boxed_3396_, v_i_boxed_3397_, v_b_3394_);
lean_dec_ref(v_as_3391_);
return v_res_3398_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0(lean_object* v___x_3399_, lean_object* v_x_3400_){
_start:
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = lean_array_get_size(v_x_3400_);
v___x_3402_ = lean_nat_dec_eq(v___x_3401_, v___x_3399_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0___boxed(lean_object* v___x_3403_, lean_object* v_x_3404_){
_start:
{
uint8_t v_res_3405_; lean_object* v_r_3406_; 
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0(v___x_3403_, v_x_3404_);
lean_dec_ref(v_x_3404_);
lean_dec(v___x_3403_);
v_r_3406_ = lean_box(v_res_3405_);
return v_r_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3407_, lean_object* v_xs_3408_, lean_object* v_as_3409_, size_t v_sz_3410_, size_t v_i_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_usize_dec_lt(v_i_3411_, v_sz_3410_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec_ref(v_xs_3408_);
lean_dec_ref(v_a_3407_);
v___x_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_b_3412_);
return v___x_3419_;
}
else
{
lean_object* v_snd_3420_; lean_object* v_fst_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3464_; 
v_snd_3420_ = lean_ctor_get(v_b_3412_, 1);
v_fst_3421_ = lean_ctor_get(v_b_3412_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_b_3412_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3423_ = v_b_3412_;
v_isShared_3424_ = v_isSharedCheck_3464_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3421_);
lean_dec(v_b_3412_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3464_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_array_3425_; lean_object* v_start_3426_; lean_object* v_stop_3427_; uint8_t v___x_3428_; 
v_array_3425_ = lean_ctor_get(v_snd_3420_, 0);
v_start_3426_ = lean_ctor_get(v_snd_3420_, 1);
v_stop_3427_ = lean_ctor_get(v_snd_3420_, 2);
v___x_3428_ = lean_nat_dec_lt(v_start_3426_, v_stop_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v_xs_3408_);
lean_dec_ref(v_a_3407_);
if (v_isShared_3424_ == 0)
{
v___x_3430_ = v___x_3423_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_fst_3421_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_snd_3420_);
v___x_3430_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
else
{
lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3460_; 
lean_inc(v_stop_3427_);
lean_inc(v_start_3426_);
lean_inc_ref(v_array_3425_);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_snd_3420_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; lean_object* v_unused_3462_; lean_object* v_unused_3463_; 
v_unused_3461_ = lean_ctor_get(v_snd_3420_, 2);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_snd_3420_, 1);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_snd_3420_, 0);
lean_dec(v_unused_3463_);
v___x_3434_ = v_snd_3420_;
v_isShared_3435_ = v_isSharedCheck_3460_;
goto v_resetjp_3433_;
}
else
{
lean_dec(v_snd_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3460_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_a_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_a_3436_ = lean_array_uget_borrowed(v_as_3409_, v_i_3411_);
v___x_3437_ = lean_array_fget_borrowed(v_array_3425_, v_start_3426_);
lean_inc(v_a_3436_);
lean_inc_ref(v_xs_3408_);
lean_inc_ref(v_a_3407_);
v___x_3438_ = l_Lean_Elab_Structural_argsInGroup(v_a_3407_, v_xs_3408_, v_a_3436_, v___x_3437_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = lean_unsigned_to_nat(1u);
v___x_3441_ = lean_nat_add(v_start_3426_, v___x_3440_);
lean_dec(v_start_3426_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3441_);
v___x_3443_ = v___x_3434_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_array_3425_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_stop_3427_);
v___x_3443_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3444_ = lean_array_push(v_fst_3421_, v_a_3439_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 1, v___x_3443_);
lean_ctor_set(v___x_3423_, 0, v___x_3444_);
v___x_3446_ = v___x_3423_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3443_);
v___x_3446_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
size_t v___x_3447_; size_t v___x_3448_; 
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_add(v_i_3411_, v___x_3447_);
v_i_3411_ = v___x_3448_;
v_b_3412_ = v___x_3446_;
goto _start;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_del_object(v___x_3434_);
lean_dec(v_stop_3427_);
lean_dec(v_start_3426_);
lean_dec_ref(v_array_3425_);
lean_del_object(v___x_3423_);
lean_dec(v_fst_3421_);
lean_dec_ref(v_xs_3408_);
lean_dec_ref(v_a_3407_);
v_a_3452_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3438_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3438_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3465_, lean_object* v_xs_3466_, lean_object* v_as_3467_, lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3465_, v_xs_3466_, v_as_3467_, v_sz_boxed_3476_, v_i_boxed_3477_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v_as_3467_);
return v_res_3478_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__2));
v___x_3485_ = l_Lean_stringToMessageData(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__4));
v___x_3488_ = l_Lean_stringToMessageData(v___x_3487_);
return v___x_3488_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__6));
v___x_3491_ = l_Lean_stringToMessageData(v___x_3490_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__8));
v___x_3494_ = l_Lean_stringToMessageData(v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__10));
v___x_3497_ = l_Lean_stringToMessageData(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__12));
v___x_3500_ = l_Lean_stringToMessageData(v___x_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(lean_object* v___x_3501_, lean_object* v_values_3502_, lean_object* v_xs_3503_, lean_object* v_fnNames_3504_, lean_object* v_as_3505_, size_t v_sz_3506_, size_t v_i_3507_, lean_object* v_b_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_a_3515_; uint8_t v___x_3519_; 
v___x_3519_ = lean_usize_dec_lt(v_i_3507_, v_sz_3506_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_dec_ref(v_xs_3503_);
lean_dec_ref(v___x_3501_);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_b_3508_);
return v___x_3520_;
}
else
{
lean_object* v___x_3521_; lean_object* v_recArgInfoss_3522_; lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; size_t v_sz_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v___x_3521_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v_a_3523_ = lean_array_uget_borrowed(v_as_3505_, v_i_3507_);
v___x_3524_ = lean_array_get_size(v___x_3501_);
lean_inc_ref(v___x_3501_);
v___x_3525_ = l_Array_toSubarray___redArg(v___x_3501_, v___x_3521_, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v_recArgInfoss_3522_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v_sz_3527_ = lean_array_size(v_values_3502_);
v___x_3528_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3503_);
lean_inc(v_a_3523_);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3523_, v_xs_3503_, v_values_3502_, v_sz_3527_, v___x_3528_, v___x_3526_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v_fst_3531_; lean_object* v_snd_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3591_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3529_);
v_fst_3531_ = lean_ctor_get(v_b_3508_, 0);
v_snd_3532_ = lean_ctor_get(v_b_3508_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_b_3508_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3534_ = v_b_3508_;
v_isShared_3535_ = v_isSharedCheck_3591_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_snd_3532_);
lean_inc(v_fst_3531_);
lean_dec(v_b_3508_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3591_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v_fst_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3589_; 
v_fst_3536_ = lean_ctor_get(v_a_3530_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_a_3530_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_a_3530_, 1);
lean_dec(v_unused_3590_);
v___x_3538_ = v_a_3530_;
v_isShared_3539_ = v_isSharedCheck_3589_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_fst_3536_);
lean_dec(v_a_3530_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3589_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___f_3540_; lean_object* v___x_3541_; 
v___f_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1));
v___x_3541_ = l_Array_findIdx_x3f_loop___redArg(v___f_3540_, v_fst_3536_, v___x_3521_);
if (lean_obj_tag(v___x_3541_) == 1)
{
lean_object* v_val_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
lean_dec(v_fst_3536_);
v_val_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_val_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3);
lean_inc(v_a_3523_);
v___x_3545_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3523_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 7);
lean_ctor_set(v___x_3534_, 1, v___x_3545_);
lean_ctor_set(v___x_3534_, 0, v___x_3544_);
v___x_3547_ = v___x_3534_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_array_get_borrowed(v___x_3543_, v_fnNames_3504_, v_val_3542_);
lean_dec(v_val_3542_);
lean_inc(v___x_3550_);
v___x_3551_ = l_Lean_MessageData_ofName(v___x_3550_);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3549_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v_fst_3531_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_snd_3532_);
lean_ctor_set(v___x_3538_, 0, v___x_3555_);
v___x_3557_ = v___x_3538_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_snd_3532_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
v_a_3515_ = v___x_3557_;
goto v___jp_3514_;
}
}
}
else
{
lean_object* v___x_3560_; 
lean_dec(v___x_3541_);
v___x_3560_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3536_);
lean_dec(v_fst_3536_);
if (lean_obj_tag(v___x_3560_) == 1)
{
lean_object* v_val_3561_; size_t v_sz_3562_; lean_object* v___x_3563_; 
lean_del_object(v___x_3534_);
v_val_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_val_3561_);
lean_dec_ref(v___x_3560_);
v_sz_3562_ = lean_array_size(v_val_3561_);
lean_inc(v_a_3523_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3523_, v_val_3561_, v_sz_3562_, v___x_3528_, v_snd_3532_);
lean_dec(v_val_3561_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v___x_3563_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_a_3564_);
lean_ctor_set(v___x_3538_, 0, v_fst_3531_);
v___x_3566_ = v___x_3538_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_fst_3531_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
v_a_3515_ = v___x_3566_;
goto v___jp_3514_;
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_del_object(v___x_3538_);
lean_dec(v_fst_3531_);
lean_dec_ref(v_xs_3503_);
lean_dec_ref(v___x_3501_);
v_a_3568_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3563_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3563_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_dec(v___x_3560_);
v___x_3576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9);
lean_inc(v_a_3523_);
v___x_3577_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3523_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 7);
lean_ctor_set(v___x_3534_, 1, v___x_3577_);
lean_ctor_set(v___x_3534_, 0, v___x_3576_);
v___x_3579_ = v___x_3534_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_fst_3531_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_snd_3532_);
lean_ctor_set(v___x_3538_, 0, v___x_3584_);
v___x_3586_ = v___x_3538_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_snd_3532_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
v_a_3515_ = v___x_3586_;
goto v___jp_3514_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_b_3508_);
lean_dec_ref(v_xs_3503_);
lean_dec_ref(v___x_3501_);
v_a_3592_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3529_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3529_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
v___jp_3514_:
{
size_t v___x_3516_; size_t v___x_3517_; 
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_add(v_i_3507_, v___x_3516_);
v_i_3507_ = v___x_3517_;
v_b_3508_ = v_a_3515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___boxed(lean_object* v___x_3600_, lean_object* v_values_3601_, lean_object* v_xs_3602_, lean_object* v_fnNames_3603_, lean_object* v_as_3604_, lean_object* v_sz_3605_, lean_object* v_i_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
size_t v_sz_boxed_3613_; size_t v_i_boxed_3614_; lean_object* v_res_3615_; 
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3605_);
lean_dec(v_sz_3605_);
v_i_boxed_3614_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(v___x_3600_, v_values_3601_, v_xs_3602_, v_fnNames_3603_, v_as_3604_, v_sz_boxed_3613_, v_i_boxed_3614_, v_b_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v_as_3604_);
lean_dec_ref(v_fnNames_3603_);
lean_dec_ref(v_values_3601_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_xs_3616_, lean_object* v___x_3617_, lean_object* v_values_3618_, lean_object* v_fnNames_3619_, lean_object* v_as_3620_, size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_a_3630_; uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec_ref(v___x_3617_);
lean_dec_ref(v_xs_3616_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_b_3623_);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v_recArgInfoss_3637_; lean_object* v_a_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; size_t v_sz_3642_; size_t v___x_3643_; lean_object* v___x_3644_; 
v___x_3636_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v_a_3638_ = lean_array_uget_borrowed(v_as_3620_, v_i_3622_);
v___x_3639_ = lean_array_get_size(v___x_3617_);
lean_inc_ref(v___x_3617_);
v___x_3640_ = l_Array_toSubarray___redArg(v___x_3617_, v___x_3636_, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v_recArgInfoss_3637_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v_sz_3642_ = lean_array_size(v_values_3618_);
v___x_3643_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3616_);
lean_inc(v_a_3638_);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3638_, v_xs_3616_, v_values_3618_, v_sz_3642_, v___x_3643_, v___x_3641_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3706_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
v_fst_3646_ = lean_ctor_get(v_b_3623_, 0);
v_snd_3647_ = lean_ctor_get(v_b_3623_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_b_3623_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3649_ = v_b_3623_;
v_isShared_3650_ = v_isSharedCheck_3706_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snd_3647_);
lean_inc(v_fst_3646_);
lean_dec(v_b_3623_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3706_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_fst_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3704_; 
v_fst_3651_ = lean_ctor_get(v_a_3645_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_a_3645_);
if (v_isSharedCheck_3704_ == 0)
{
lean_object* v_unused_3705_; 
v_unused_3705_ = lean_ctor_get(v_a_3645_, 1);
lean_dec(v_unused_3705_);
v___x_3653_ = v_a_3645_;
v_isShared_3654_ = v_isSharedCheck_3704_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_fst_3651_);
lean_dec(v_a_3645_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3704_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___f_3655_; lean_object* v___x_3656_; 
v___f_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1));
v___x_3656_ = l_Array_findIdx_x3f_loop___redArg(v___f_3655_, v_fst_3651_, v___x_3636_);
if (lean_obj_tag(v___x_3656_) == 1)
{
lean_object* v_val_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_dec(v_fst_3651_);
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3);
lean_inc(v_a_3638_);
v___x_3660_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3638_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 7);
lean_ctor_set(v___x_3649_, 1, v___x_3660_);
lean_ctor_set(v___x_3649_, 0, v___x_3659_);
v___x_3662_ = v___x_3649_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_array_get_borrowed(v___x_3658_, v_fnNames_3619_, v_val_3657_);
lean_dec(v_val_3657_);
lean_inc(v___x_3665_);
v___x_3666_ = l_Lean_MessageData_ofName(v___x_3665_);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3664_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_fst_3646_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v_snd_3647_);
lean_ctor_set(v___x_3653_, 0, v___x_3670_);
v___x_3672_ = v___x_3653_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_snd_3647_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
v_a_3630_ = v___x_3672_;
goto v___jp_3629_;
}
}
}
else
{
lean_object* v___x_3675_; 
lean_dec(v___x_3656_);
v___x_3675_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3651_);
lean_dec(v_fst_3651_);
if (lean_obj_tag(v___x_3675_) == 1)
{
lean_object* v_val_3676_; size_t v_sz_3677_; lean_object* v___x_3678_; 
lean_del_object(v___x_3649_);
v_val_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_val_3676_);
lean_dec_ref(v___x_3675_);
v_sz_3677_ = lean_array_size(v_val_3676_);
lean_inc(v_a_3638_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3638_, v_val_3676_, v_sz_3677_, v___x_3643_, v_snd_3647_);
lean_dec(v_val_3676_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v_a_3679_);
lean_ctor_set(v___x_3653_, 0, v_fst_3646_);
v___x_3681_ = v___x_3653_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_fst_3646_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_a_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
v_a_3630_ = v___x_3681_;
goto v___jp_3629_;
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3653_);
lean_dec(v_fst_3646_);
lean_dec_ref(v___x_3617_);
lean_dec_ref(v_xs_3616_);
v_a_3683_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3678_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3678_);
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
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_dec(v___x_3675_);
v___x_3691_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9);
lean_inc(v_a_3638_);
v___x_3692_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3638_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 7);
lean_ctor_set(v___x_3649_, 1, v___x_3692_);
lean_ctor_set(v___x_3649_, 0, v___x_3691_);
v___x_3694_ = v___x_3649_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3695_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_fst_3646_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v_snd_3647_);
lean_ctor_set(v___x_3653_, 0, v___x_3699_);
v___x_3701_ = v___x_3653_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_snd_3647_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
v_a_3630_ = v___x_3701_;
goto v___jp_3629_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v_b_3623_);
lean_dec_ref(v___x_3617_);
lean_dec_ref(v_xs_3616_);
v_a_3707_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3644_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3644_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
v___jp_3629_:
{
size_t v___x_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = ((size_t)1ULL);
v___x_3632_ = lean_usize_add(v_i_3622_, v___x_3631_);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(v___x_3617_, v_values_3618_, v_xs_3616_, v_fnNames_3619_, v_as_3620_, v_sz_3621_, v___x_3632_, v_a_3630_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_xs_3715_, lean_object* v___x_3716_, lean_object* v_values_3717_, lean_object* v_fnNames_3718_, lean_object* v_as_3719_, lean_object* v_sz_3720_, lean_object* v_i_3721_, lean_object* v_b_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
size_t v_sz_boxed_3728_; size_t v_i_boxed_3729_; lean_object* v_res_3730_; 
v_sz_boxed_3728_ = lean_unbox_usize(v_sz_3720_);
lean_dec(v_sz_3720_);
v_i_boxed_3729_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_xs_3715_, v___x_3716_, v_values_3717_, v_fnNames_3718_, v_as_3719_, v_sz_boxed_3728_, v_i_boxed_3729_, v_b_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v_as_3719_);
lean_dec_ref(v_fnNames_3718_);
lean_dec_ref(v_values_3717_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3731_, size_t v_i_3732_, lean_object* v_bs_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_usize_dec_lt(v_i_3732_, v_sz_3731_);
if (v___x_3734_ == 0)
{
return v_bs_3733_;
}
else
{
lean_object* v_v_3735_; lean_object* v___x_3736_; lean_object* v_bs_x27_3737_; lean_object* v___x_3738_; size_t v___x_3739_; size_t v___x_3740_; lean_object* v___x_3741_; 
v_v_3735_ = lean_array_uget(v_bs_3733_, v_i_3732_);
v___x_3736_ = lean_unsigned_to_nat(0u);
v_bs_x27_3737_ = lean_array_uset(v_bs_3733_, v_i_3732_, v___x_3736_);
v___x_3738_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3735_);
lean_dec(v_v_3735_);
v___x_3739_ = ((size_t)1ULL);
v___x_3740_ = lean_usize_add(v_i_3732_, v___x_3739_);
v___x_3741_ = lean_array_uset(v_bs_x27_3737_, v_i_3732_, v___x_3738_);
v_i_3732_ = v___x_3740_;
v_bs_3733_ = v___x_3741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3743_, lean_object* v_i_3744_, lean_object* v_bs_3745_){
_start:
{
size_t v_sz_boxed_3746_; size_t v_i_boxed_3747_; lean_object* v_res_3748_; 
v_sz_boxed_3746_ = lean_unbox_usize(v_sz_3743_);
lean_dec(v_sz_3743_);
v_i_boxed_3747_ = lean_unbox_usize(v_i_3744_);
lean_dec(v_i_3744_);
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3746_, v_i_boxed_3747_, v_bs_3745_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3749_, lean_object* v_as_3750_, size_t v_sz_3751_, size_t v_i_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_usize_dec_lt(v_i_3752_, v_sz_3751_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
lean_dec_ref(v_xs_3749_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_b_3753_);
return v___x_3760_;
}
else
{
lean_object* v_snd_3761_; lean_object* v_snd_3762_; lean_object* v_snd_3763_; lean_object* v_snd_3764_; lean_object* v_fst_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3909_; 
v_snd_3761_ = lean_ctor_get(v_b_3753_, 1);
lean_inc(v_snd_3761_);
v_snd_3762_ = lean_ctor_get(v_snd_3761_, 1);
lean_inc(v_snd_3762_);
v_snd_3763_ = lean_ctor_get(v_snd_3762_, 1);
lean_inc(v_snd_3763_);
v_snd_3764_ = lean_ctor_get(v_snd_3763_, 1);
lean_inc(v_snd_3764_);
v_fst_3765_ = lean_ctor_get(v_b_3753_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_b_3753_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v_b_3753_, 1);
lean_dec(v_unused_3910_);
v___x_3767_ = v_b_3753_;
v_isShared_3768_ = v_isSharedCheck_3909_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_fst_3765_);
lean_dec(v_b_3753_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3909_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_fst_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3907_; 
v_fst_3769_ = lean_ctor_get(v_snd_3761_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_snd_3761_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_snd_3761_, 1);
lean_dec(v_unused_3908_);
v___x_3771_ = v_snd_3761_;
v_isShared_3772_ = v_isSharedCheck_3907_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_fst_3769_);
lean_dec(v_snd_3761_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3907_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_fst_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3905_; 
v_fst_3773_ = lean_ctor_get(v_snd_3762_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_snd_3762_);
if (v_isSharedCheck_3905_ == 0)
{
lean_object* v_unused_3906_; 
v_unused_3906_ = lean_ctor_get(v_snd_3762_, 1);
lean_dec(v_unused_3906_);
v___x_3775_ = v_snd_3762_;
v_isShared_3776_ = v_isSharedCheck_3905_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_fst_3773_);
lean_dec(v_snd_3762_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3905_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v_fst_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3903_; 
v_fst_3777_ = lean_ctor_get(v_snd_3763_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_snd_3763_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v_snd_3763_, 1);
lean_dec(v_unused_3904_);
v___x_3779_ = v_snd_3763_;
v_isShared_3780_ = v_isSharedCheck_3903_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_fst_3777_);
lean_dec(v_snd_3763_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3903_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_array_3781_; lean_object* v_start_3782_; lean_object* v_stop_3783_; uint8_t v___x_3784_; 
v_array_3781_ = lean_ctor_get(v_snd_3764_, 0);
v_start_3782_ = lean_ctor_get(v_snd_3764_, 1);
v_stop_3783_ = lean_ctor_get(v_snd_3764_, 2);
v___x_3784_ = lean_nat_dec_lt(v_start_3782_, v_stop_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3786_; 
lean_dec_ref(v_xs_3749_);
if (v_isShared_3780_ == 0)
{
v___x_3786_ = v___x_3779_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_fst_3777_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_snd_3764_);
v___x_3786_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___x_3786_);
v___x_3788_ = v___x_3775_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_fst_3773_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3790_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3788_);
v___x_3790_ = v___x_3771_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_fst_3769_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3792_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3790_);
v___x_3792_ = v___x_3767_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
}
}
}
}
else
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3899_; 
lean_inc(v_stop_3783_);
lean_inc(v_start_3782_);
lean_inc_ref(v_array_3781_);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_snd_3764_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; lean_object* v_unused_3901_; lean_object* v_unused_3902_; 
v_unused_3900_ = lean_ctor_get(v_snd_3764_, 2);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_snd_3764_, 1);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_snd_3764_, 0);
lean_dec(v_unused_3902_);
v___x_3799_ = v_snd_3764_;
v_isShared_3800_ = v_isSharedCheck_3899_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v_snd_3764_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3899_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_array_3801_; lean_object* v_start_3802_; lean_object* v_stop_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v_array_3801_ = lean_ctor_get(v_fst_3777_, 0);
v_start_3802_ = lean_ctor_get(v_fst_3777_, 1);
v_stop_3803_ = lean_ctor_get(v_fst_3777_, 2);
v___x_3804_ = lean_array_fget(v_array_3781_, v_start_3782_);
v___x_3805_ = lean_unsigned_to_nat(1u);
v___x_3806_ = lean_nat_add(v_start_3782_, v___x_3805_);
lean_dec(v_start_3782_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 1, v___x_3806_);
v___x_3808_ = v___x_3799_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_array_3781_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_stop_3783_);
v___x_3808_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
uint8_t v___x_3809_; 
v___x_3809_ = lean_nat_dec_lt(v_start_3802_, v_stop_3803_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3811_; 
lean_dec(v___x_3804_);
lean_dec_ref(v_xs_3749_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v___x_3808_);
v___x_3811_ = v___x_3779_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_fst_3777_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3808_);
v___x_3811_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___x_3811_);
v___x_3813_ = v___x_3775_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_fst_3773_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3815_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3813_);
v___x_3815_ = v___x_3771_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_fst_3769_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3817_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3815_);
v___x_3817_ = v___x_3767_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
return v___x_3818_;
}
}
}
}
}
else
{
lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3894_; 
lean_inc(v_stop_3803_);
lean_inc(v_start_3802_);
lean_inc_ref(v_array_3801_);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_fst_3777_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; 
v_unused_3895_ = lean_ctor_get(v_fst_3777_, 2);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_fst_3777_, 1);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_fst_3777_, 0);
lean_dec(v_unused_3897_);
v___x_3824_ = v_fst_3777_;
v_isShared_3825_ = v_isSharedCheck_3894_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v_fst_3777_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3894_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_array_3826_; lean_object* v_start_3827_; lean_object* v_stop_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
v_array_3826_ = lean_ctor_get(v_fst_3773_, 0);
v_start_3827_ = lean_ctor_get(v_fst_3773_, 1);
v_stop_3828_ = lean_ctor_get(v_fst_3773_, 2);
v___x_3829_ = lean_array_fget(v_array_3801_, v_start_3802_);
v___x_3830_ = lean_nat_add(v_start_3802_, v___x_3805_);
lean_dec(v_start_3802_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 1, v___x_3830_);
v___x_3832_ = v___x_3824_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_array_3801_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_stop_3803_);
v___x_3832_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_nat_dec_lt(v_start_3827_, v_stop_3828_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3835_; 
lean_dec(v___x_3829_);
lean_dec(v___x_3804_);
lean_dec_ref(v_xs_3749_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v___x_3808_);
lean_ctor_set(v___x_3779_, 0, v___x_3832_);
v___x_3835_ = v___x_3779_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3808_);
v___x_3835_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3837_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___x_3835_);
v___x_3837_ = v___x_3775_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3773_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3839_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3837_);
v___x_3839_ = v___x_3771_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_fst_3769_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3841_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3839_);
v___x_3841_ = v___x_3767_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
return v___x_3842_;
}
}
}
}
}
else
{
lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3889_; 
lean_inc(v_stop_3828_);
lean_inc(v_start_3827_);
lean_inc_ref(v_array_3826_);
lean_del_object(v___x_3767_);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_fst_3773_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3890_ = lean_ctor_get(v_fst_3773_, 2);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_fst_3773_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_fst_3773_, 0);
lean_dec(v_unused_3892_);
v___x_3848_ = v_fst_3773_;
v_isShared_3849_ = v_isSharedCheck_3889_;
goto v_resetjp_3847_;
}
else
{
lean_dec(v_fst_3773_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3889_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3850_ = lean_array_uget_borrowed(v_as_3750_, v_i_3752_);
v___x_3851_ = lean_array_fget_borrowed(v_array_3826_, v_start_3827_);
lean_inc(v___x_3851_);
lean_inc_ref(v_xs_3749_);
lean_inc(v_a_3850_);
v___x_3852_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3850_, v___x_3804_, v_xs_3749_, v___x_3851_, v___x_3829_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v_fst_3854_; lean_object* v_snd_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3880_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3852_);
v_fst_3854_ = lean_ctor_get(v_a_3853_, 0);
v_snd_3855_ = lean_ctor_get(v_a_3853_, 1);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_a_3853_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3857_ = v_a_3853_;
v_isShared_3858_ = v_isSharedCheck_3880_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_snd_3855_);
lean_inc(v_fst_3854_);
lean_dec(v_a_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3880_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_nat_add(v_start_3827_, v___x_3805_);
lean_dec(v_start_3827_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 1, v___x_3859_);
v___x_3861_ = v___x_3848_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_array_3826_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_stop_3828_);
v___x_3861_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3862_, 0, v_fst_3765_);
lean_ctor_set(v___x_3862_, 1, v_snd_3855_);
v___x_3863_ = lean_array_push(v_fst_3769_, v_fst_3854_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3808_);
lean_ctor_set(v___x_3857_, 0, v___x_3832_);
v___x_3865_ = v___x_3857_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3808_);
v___x_3865_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v___x_3865_);
lean_ctor_set(v___x_3779_, 0, v___x_3861_);
v___x_3867_ = v___x_3779_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3869_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 1, v___x_3867_);
lean_ctor_set(v___x_3775_, 0, v___x_3863_);
v___x_3869_ = v___x_3775_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3871_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v___x_3869_);
lean_ctor_set(v___x_3771_, 0, v___x_3862_);
v___x_3871_ = v___x_3771_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
size_t v___x_3872_; size_t v___x_3873_; 
v___x_3872_ = ((size_t)1ULL);
v___x_3873_ = lean_usize_add(v_i_3752_, v___x_3872_);
v_i_3752_ = v___x_3873_;
v_b_3753_ = v___x_3871_;
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
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_del_object(v___x_3848_);
lean_dec_ref(v___x_3832_);
lean_dec(v_stop_3828_);
lean_dec(v_start_3827_);
lean_dec_ref(v_array_3826_);
lean_dec_ref(v___x_3808_);
lean_del_object(v___x_3779_);
lean_del_object(v___x_3775_);
lean_del_object(v___x_3771_);
lean_dec(v_fst_3769_);
lean_dec(v_fst_3765_);
lean_dec_ref(v_xs_3749_);
v_a_3881_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3852_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3852_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3911_, lean_object* v_as_3912_, lean_object* v_sz_3913_, lean_object* v_i_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
size_t v_sz_boxed_3921_; size_t v_i_boxed_3922_; lean_object* v_res_3923_; 
v_sz_boxed_3921_ = lean_unbox_usize(v_sz_3913_);
lean_dec(v_sz_3913_);
v_i_boxed_3922_ = lean_unbox_usize(v_i_3914_);
lean_dec(v_i_3914_);
v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3911_, v_as_3912_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v_as_3912_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
if (lean_obj_tag(v_a_3924_) == 0)
{
lean_object* v___x_3926_; 
v___x_3926_ = l_List_reverse___redArg(v_a_3925_);
return v___x_3926_;
}
else
{
lean_object* v_head_3927_; lean_object* v_tail_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3938_; 
v_head_3927_ = lean_ctor_get(v_a_3924_, 0);
v_tail_3928_ = lean_ctor_get(v_a_3924_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3924_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3930_ = v_a_3924_;
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_tail_3928_);
lean_inc(v_head_3927_);
lean_dec(v_a_3924_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3932_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3927_);
v___x_3933_ = l_Lean_MessageData_ofFormat(v___x_3932_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 1, v_a_3925_);
lean_ctor_set(v___x_3930_, 0, v___x_3933_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_a_3925_);
v___x_3935_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
v_a_3924_ = v_tail_3928_;
v_a_3925_ = v___x_3935_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
if (lean_obj_tag(v_a_3939_) == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = l_List_reverse___redArg(v_a_3940_);
return v___x_3941_;
}
else
{
lean_object* v_head_3942_; lean_object* v_tail_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3952_; 
v_head_3942_ = lean_ctor_get(v_a_3939_, 0);
v_tail_3943_ = lean_ctor_get(v_a_3939_, 1);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_a_3939_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3945_ = v_a_3939_;
v_isShared_3946_ = v_isSharedCheck_3952_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_tail_3943_);
lean_inc(v_head_3942_);
lean_dec(v_a_3939_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3952_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3942_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 1, v_a_3940_);
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_a_3940_);
v___x_3949_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
v_a_3939_ = v_tail_3943_;
v_a_3940_ = v___x_3949_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3957_ = l_Lean_MessageData_ofFormat(v___x_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3960_ = l_Lean_stringToMessageData(v___x_3959_);
return v___x_3960_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3965_ = l_Lean_stringToMessageData(v___x_3964_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = lean_box(1);
v___x_3967_ = l_Lean_MessageData_ofFormat(v___x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3968_, lean_object* v_fixedParamPerms_3969_, lean_object* v_xs_3970_, lean_object* v_values_3971_, lean_object* v_termMeasure_x3fs_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v_recArgInfoss_3979_; lean_object* v___x_3980_; lean_object* v_perms_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v_report_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; size_t v_sz_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3978_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v___x_3980_ = lean_array_get_size(v_values_3971_);
v_perms_3981_ = lean_ctor_get(v_fixedParamPerms_3969_, 1);
lean_inc_ref(v_perms_3981_);
lean_dec_ref(v_fixedParamPerms_3969_);
lean_inc_ref(v_values_3971_);
v___x_3982_ = l_Array_toSubarray___redArg(v_values_3971_, v___x_3978_, v___x_3980_);
v___x_3983_ = lean_array_get_size(v_termMeasure_x3fs_3972_);
v_report_3984_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3985_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3972_, v___x_3978_, v___x_3983_);
v___x_3986_ = lean_array_get_size(v_perms_3981_);
v___x_3987_ = l_Array_toSubarray___redArg(v_perms_3981_, v___x_3978_, v___x_3986_);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3985_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3982_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v_recArgInfoss_3979_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_report_3984_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v_sz_3992_ = lean_array_size(v_fnNames_3968_);
v___x_3993_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3970_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3970_, v_fnNames_3968_, v_sz_3992_, v___x_3993_, v___x_3991_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v_snd_3996_; lean_object* v_options_3997_; lean_object* v_fst_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4141_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref(v___x_3994_);
v_snd_3996_ = lean_ctor_get(v_a_3995_, 1);
lean_inc(v_snd_3996_);
v_options_3997_ = lean_ctor_get(v_a_3975_, 2);
v_fst_3998_ = lean_ctor_get(v_a_3995_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_a_3995_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; 
v_unused_4142_ = lean_ctor_get(v_a_3995_, 1);
lean_dec(v_unused_4142_);
v___x_4000_ = v_a_3995_;
v_isShared_4001_ = v_isSharedCheck_4141_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_fst_3998_);
lean_dec(v_a_3995_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4141_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_fst_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4139_; 
v_fst_4002_ = lean_ctor_get(v_snd_3996_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_snd_3996_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v_snd_3996_, 1);
lean_dec(v_unused_4140_);
v___x_4004_ = v_snd_3996_;
v_isShared_4005_ = v_isSharedCheck_4139_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_fst_4002_);
lean_dec(v_snd_3996_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4139_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_inheritedTraceOptions_4006_; uint8_t v_hasTrace_4007_; size_t v_sz_4008_; lean_object* v___x_4009_; lean_object* v___y_4011_; lean_object* v_report_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___x_4059_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; 
v_inheritedTraceOptions_4006_ = lean_ctor_get(v_a_3975_, 13);
v_hasTrace_4007_ = lean_ctor_get_uint8(v_options_3997_, sizeof(void*)*1);
v_sz_4008_ = lean_array_size(v_fst_4002_);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4008_, v___x_3993_, v_fst_4002_);
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4007_ == 0)
{
v___y_4098_ = v_a_3973_;
v___y_4099_ = v_a_3974_;
v___y_4100_ = v_a_3975_;
v___y_4101_ = v_a_3976_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4110_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4006_, v_options_3997_, v___x_4110_);
if (v___x_4111_ == 0)
{
v___y_4098_ = v_a_3973_;
v___y_4099_ = v_a_3974_;
v___y_4100_ = v_a_3975_;
v___y_4101_ = v_a_3976_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4112_; lean_object* v___y_4114_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4132_ = lean_array_get_size(v___x_4009_);
v___x_4133_ = lean_nat_dec_lt(v___x_3978_, v___x_4132_);
if (v___x_4133_ == 0)
{
v___y_4114_ = v___x_4131_;
goto v___jp_4113_;
}
else
{
uint8_t v___x_4134_; 
v___x_4134_ = lean_nat_dec_le(v___x_4132_, v___x_4132_);
if (v___x_4134_ == 0)
{
if (v___x_4133_ == 0)
{
v___y_4114_ = v___x_4131_;
goto v___jp_4113_;
}
else
{
size_t v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_usize_of_nat(v___x_4132_);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4009_, v___x_3993_, v___x_4135_, v___x_4131_);
v___y_4114_ = v___x_4136_;
goto v___jp_4113_;
}
}
else
{
size_t v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_usize_of_nat(v___x_4132_);
v___x_4138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4009_, v___x_3993_, v___x_4137_, v___x_4131_);
v___y_4114_ = v___x_4138_;
goto v___jp_4113_;
}
}
v___jp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4115_ = lean_array_to_list(v___y_4114_);
v___x_4116_ = lean_box(0);
v___x_4117_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4115_, v___x_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4119_ = l_Lean_MessageData_joinSep(v___x_4117_, v___x_4118_);
v___x_4120_ = l_Lean_indentD(v___x_4119_);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4112_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4059_, v___x_4121_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_dec_ref(v___x_4122_);
v___y_4098_ = v_a_3973_;
v___y_4099_ = v_a_3974_;
v___y_4100_ = v_a_3975_;
v___y_4101_ = v_a_3976_;
goto v___jp_4097_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref(v___x_4009_);
lean_del_object(v___x_4004_);
lean_del_object(v___x_4000_);
lean_dec(v_fst_3998_);
lean_dec_ref(v_values_3971_);
lean_dec_ref(v_xs_3970_);
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
v___jp_4010_:
{
lean_object* v___x_4018_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 1, v_recArgInfoss_3979_);
lean_ctor_set(v___x_4004_, 0, v_report_4012_);
v___x_4018_ = v___x_4004_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_report_4012_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_recArgInfoss_3979_);
v___x_4018_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
size_t v_sz_4019_; lean_object* v___x_4020_; 
v_sz_4019_ = lean_array_size(v___y_4011_);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_xs_3970_, v___x_4009_, v_values_3971_, v_fnNames_3968_, v___y_4011_, v_sz_4019_, v___x_3993_, v___x_4018_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_values_3971_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4037_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4037_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4037_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v_fst_4025_; lean_object* v_snd_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4036_; 
v_fst_4025_ = lean_ctor_get(v_a_4021_, 0);
v_snd_4026_ = lean_ctor_get(v_a_4021_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_a_4021_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4028_ = v_a_4021_;
v_isShared_4029_ = v_isSharedCheck_4036_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_snd_4026_);
lean_inc(v_fst_4025_);
lean_dec(v_a_4021_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4036_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 1, v_fst_4025_);
lean_ctor_set(v___x_4028_, 0, v_snd_4026_);
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_snd_4026_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_fst_4025_);
v___x_4031_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4033_; 
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v___x_4031_);
v___x_4033_ = v___x_4023_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v_a_4038_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4020_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4020_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
v___jp_4047_:
{
lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4053_ = lean_array_get_size(v___y_4048_);
v___x_4054_ = lean_nat_dec_eq(v___x_4053_, v___x_3978_);
if (v___x_4054_ == 0)
{
lean_del_object(v___x_4000_);
v___y_4011_ = v___y_4048_;
v_report_4012_ = v_fst_3998_;
v___y_4013_ = v___y_4049_;
v___y_4014_ = v___y_4050_;
v___y_4015_ = v___y_4051_;
v___y_4016_ = v___y_4052_;
goto v___jp_4010_;
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4055_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4001_ == 0)
{
lean_ctor_set_tag(v___x_4000_, 7);
lean_ctor_set(v___x_4000_, 1, v___x_4055_);
v___x_4057_ = v___x_4000_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_fst_3998_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
v___y_4011_ = v___y_4048_;
v_report_4012_ = v___x_4057_;
v___y_4013_ = v___y_4049_;
v___y_4014_ = v___y_4050_;
v___y_4015_ = v___y_4051_;
v___y_4016_ = v___y_4052_;
goto v___jp_4010_;
}
}
}
v___jp_4060_:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4065_, v___y_4063_, v___y_4061_, v___y_4064_, v___y_4062_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_options_4067_; uint8_t v_hasTrace_4068_; 
v_options_4067_ = lean_ctor_get(v___y_4064_, 2);
v_hasTrace_4068_ = lean_ctor_get_uint8(v_options_4067_, sizeof(void*)*1);
if (v_hasTrace_4068_ == 0)
{
lean_object* v_a_4069_; 
v_a_4069_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4069_);
lean_dec_ref(v___x_4066_);
v___y_4048_ = v_a_4069_;
v___y_4049_ = v___y_4063_;
v___y_4050_ = v___y_4061_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4062_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4070_; lean_object* v_inheritedTraceOptions_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v_a_4070_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4070_);
lean_dec_ref(v___x_4066_);
v_inheritedTraceOptions_4071_ = lean_ctor_get(v___y_4064_, 13);
v___x_4072_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4067_, v___x_4072_);
if (v___x_4073_ == 0)
{
v___y_4048_ = v_a_4070_;
v___y_4049_ = v___y_4063_;
v___y_4050_ = v___y_4061_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4062_;
goto v___jp_4047_;
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4074_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4070_);
v___x_4075_ = lean_array_to_list(v_a_4070_);
v___x_4076_ = lean_box(0);
v___x_4077_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v___x_4075_, v___x_4076_);
v___x_4078_ = l_Lean_MessageData_ofList(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4074_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4059_, v___x_4079_, v___y_4063_, v___y_4061_, v___y_4064_, v___y_4062_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_dec_ref(v___x_4080_);
v___y_4048_ = v_a_4070_;
v___y_4049_ = v___y_4063_;
v___y_4050_ = v___y_4061_;
v___y_4051_ = v___y_4064_;
v___y_4052_ = v___y_4062_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4070_);
lean_dec_ref(v___x_4009_);
lean_del_object(v___x_4004_);
lean_del_object(v___x_4000_);
lean_dec(v_fst_3998_);
lean_dec_ref(v_values_3971_);
lean_dec_ref(v_xs_3970_);
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v___x_4009_);
lean_del_object(v___x_4004_);
lean_del_object(v___x_4000_);
lean_dec(v_fst_3998_);
lean_dec_ref(v_values_3971_);
lean_dec_ref(v_xs_3970_);
v_a_4089_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4066_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4066_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
v___jp_4097_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4103_ = lean_array_get_size(v___x_4009_);
v___x_4104_ = lean_nat_dec_lt(v___x_3978_, v___x_4103_);
if (v___x_4104_ == 0)
{
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4098_;
v___y_4064_ = v___y_4100_;
v___y_4065_ = v___x_4102_;
goto v___jp_4060_;
}
else
{
uint8_t v___x_4105_; 
v___x_4105_ = lean_nat_dec_le(v___x_4103_, v___x_4103_);
if (v___x_4105_ == 0)
{
if (v___x_4104_ == 0)
{
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4098_;
v___y_4064_ = v___y_4100_;
v___y_4065_ = v___x_4102_;
goto v___jp_4060_;
}
else
{
size_t v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_usize_of_nat(v___x_4103_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4009_, v___x_3993_, v___x_4106_, v___x_4102_);
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4098_;
v___y_4064_ = v___y_4100_;
v___y_4065_ = v___x_4107_;
goto v___jp_4060_;
}
}
else
{
size_t v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_usize_of_nat(v___x_4103_);
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4009_, v___x_3993_, v___x_4108_, v___x_4102_);
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4098_;
v___y_4064_ = v___y_4100_;
v___y_4065_ = v___x_4109_;
goto v___jp_4060_;
}
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_values_3971_);
lean_dec_ref(v_xs_3970_);
v_a_4143_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_3994_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_3994_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4151_, lean_object* v_fixedParamPerms_4152_, lean_object* v_xs_4153_, lean_object* v_values_4154_, lean_object* v_termMeasure_x3fs_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4151_, v_fixedParamPerms_4152_, v_xs_4153_, v_values_4154_, v_termMeasure_x3fs_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec_ref(v_fnNames_4151_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_a_4162_, lean_object* v_as_4163_, size_t v_sz_4164_, size_t v_i_4165_, lean_object* v_b_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_4162_, v_as_4163_, v_sz_4164_, v_i_4165_, v_b_4166_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_a_4173_, lean_object* v_as_4174_, lean_object* v_sz_4175_, lean_object* v_i_4176_, lean_object* v_b_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
size_t v_sz_boxed_4183_; size_t v_i_boxed_4184_; lean_object* v_res_4185_; 
v_sz_boxed_4183_ = lean_unbox_usize(v_sz_4175_);
lean_dec(v_sz_4175_);
v_i_boxed_4184_ = lean_unbox_usize(v_i_4176_);
lean_dec(v_i_4176_);
v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_a_4173_, v_as_4174_, v_sz_boxed_4183_, v_i_boxed_4184_, v_b_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec_ref(v_as_4174_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4186_, uint8_t v_skipRealize_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; lean_object* v_env_4191_; uint8_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4190_ = lean_st_ref_get(v___y_4188_);
v_env_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc_ref(v_env_4191_);
lean_dec(v___x_4190_);
v___x_4192_ = l_Lean_Environment_contains(v_env_4191_, v_constName_4186_, v_skipRealize_4187_);
v___x_4193_ = lean_box(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4195_, lean_object* v_skipRealize_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
uint8_t v_skipRealize_boxed_4199_; lean_object* v_res_4200_; 
v_skipRealize_boxed_4199_ = lean_unbox(v_skipRealize_4196_);
v_res_4200_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4195_, v_skipRealize_boxed_4199_, v___y_4197_);
lean_dec(v___y_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4201_, uint8_t v_skipRealize_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4201_, v_skipRealize_4202_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4209_, lean_object* v_skipRealize_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v_skipRealize_boxed_4216_; lean_object* v_res_4217_; 
v_skipRealize_boxed_4216_ = lean_unbox(v_skipRealize_4210_);
v_res_4217_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4209_, v_skipRealize_boxed_4216_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Meta_saveState___redArg(v___y_4220_, v___y_4222_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref(v___x_4224_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v___x_4226_ = lean_apply_5(v_x_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, lean_box(0));
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_dec(v_a_4225_);
return v___x_4226_;
}
else
{
lean_object* v_a_4227_; uint8_t v___y_4229_; uint8_t v___x_4247_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
v___x_4247_ = l_Lean_Exception_isInterrupt(v_a_4227_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; 
lean_inc(v_a_4227_);
v___x_4248_ = l_Lean_Exception_isRuntime(v_a_4227_);
v___y_4229_ = v___x_4248_;
goto v___jp_4228_;
}
else
{
v___y_4229_ = v___x_4247_;
goto v___jp_4228_;
}
v___jp_4228_:
{
if (v___y_4229_ == 0)
{
lean_object* v___x_4230_; 
lean_dec_ref(v___x_4226_);
v___x_4230_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4225_, v___y_4220_, v___y_4222_);
lean_dec(v_a_4225_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; 
v_unused_4238_ = lean_ctor_get(v___x_4230_, 0);
lean_dec(v_unused_4238_);
v___x_4232_ = v___x_4230_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_dec(v___x_4230_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
lean_ctor_set_tag(v___x_4232_, 1);
lean_ctor_set(v___x_4232_, 0, v_a_4227_);
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4227_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_a_4227_);
v_a_4239_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4230_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4230_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_dec(v_a_4227_);
lean_dec(v_a_4225_);
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v_x_4218_);
v_a_4249_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4224_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4224_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_x_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4272_, v_x_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
return v_res_4279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4282_ = l_Lean_stringToMessageData(v___x_4281_);
return v___x_4282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4285_ = l_Lean_stringToMessageData(v___x_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4286_, uint8_t v___x_4287_, lean_object* v_group_4288_, lean_object* v_k_4289_, lean_object* v_comb_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4286_, v___x_4287_, v___y_4294_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; uint8_t v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
v___x_4298_ = lean_unbox(v_a_4297_);
lean_dec(v_a_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4300_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4288_);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4301_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_4304_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4303_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4305_; 
lean_dec_ref(v___x_4304_);
v___x_4305_ = lean_apply_6(v_k_4289_, v_comb_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, lean_box(0));
return v___x_4305_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_comb_4290_);
lean_dec_ref(v_k_4289_);
v_a_4306_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4304_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4304_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
else
{
lean_object* v___x_4314_; 
lean_dec_ref(v_group_4288_);
v___x_4314_ = lean_apply_6(v_k_4289_, v_comb_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, lean_box(0));
return v___x_4314_;
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_comb_4290_);
lean_dec_ref(v_k_4289_);
lean_dec_ref(v_group_4288_);
v_a_4315_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4296_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4296_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4323_, lean_object* v___x_4324_, lean_object* v_group_4325_, lean_object* v_k_4326_, lean_object* v_comb_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
uint8_t v___x_4415__boxed_4333_; lean_object* v_res_4334_; 
v___x_4415__boxed_4333_ = lean_unbox(v___x_4324_);
v_res_4334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4323_, v___x_4415__boxed_4333_, v_group_4325_, v_k_4326_, v_comb_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
return v_res_4334_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
return v___x_4337_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4339_ = l_Lean_stringToMessageData(v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4340_, lean_object* v_fnNames_4341_, lean_object* v_xs_4342_, lean_object* v_values_4343_, lean_object* v_as_4344_, size_t v_sz_4345_, size_t v_i_4346_, lean_object* v_b_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
uint8_t v___x_4353_; 
v___x_4353_ = lean_usize_dec_lt(v_i_4346_, v_sz_4345_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_dec_ref(v_values_4343_);
lean_dec_ref(v_xs_4342_);
lean_dec_ref(v_k_4340_);
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_b_4347_);
return v___x_4354_;
}
else
{
lean_object* v_snd_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4425_; 
v_snd_4355_ = lean_ctor_get(v_b_4347_, 1);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_b_4347_);
if (v_isSharedCheck_4425_ == 0)
{
lean_object* v_unused_4426_; 
v_unused_4426_ = lean_ctor_get(v_b_4347_, 0);
lean_dec(v_unused_4426_);
v___x_4357_ = v_b_4347_;
v_isShared_4358_ = v_isSharedCheck_4425_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_snd_4355_);
lean_dec(v_b_4347_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4425_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v_a_4359_; lean_object* v_group_4360_; lean_object* v_comb_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4424_; 
v_a_4359_ = lean_array_uget(v_as_4344_, v_i_4346_);
v_group_4360_ = lean_ctor_get(v_a_4359_, 0);
v_comb_4361_ = lean_ctor_get(v_a_4359_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_a_4359_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4363_ = v_a_4359_;
v_isShared_4364_ = v_isSharedCheck_4424_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_comb_4361_);
lean_inc(v_group_4360_);
lean_dec(v_a_4359_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4424_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v_toIndGroupInfo_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___f_4369_; lean_object* v___x_4370_; 
v_toIndGroupInfo_4365_ = lean_ctor_get(v_group_4360_, 0);
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4365_, v___x_4366_);
v___x_4368_ = lean_box(v___x_4353_);
lean_inc_ref(v_comb_4361_);
lean_inc_ref(v_k_4340_);
v___f_4369_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4369_, 0, v___x_4367_);
lean_closure_set(v___f_4369_, 1, v___x_4368_);
lean_closure_set(v___f_4369_, 2, v_group_4360_);
lean_closure_set(v___f_4369_, 3, v_k_4340_);
lean_closure_set(v___f_4369_, 4, v_comb_4361_);
v___x_4370_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4369_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4382_; 
lean_del_object(v___x_4363_);
lean_dec_ref(v_comb_4361_);
lean_dec_ref(v_values_4343_);
lean_dec_ref(v_xs_4342_);
lean_dec_ref(v_k_4340_);
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4382_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4382_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; lean_object* v___x_4377_; 
v___x_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4375_, 0, v_a_4371_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4375_);
v___x_4377_ = v___x_4357_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4375_);
lean_ctor_set(v_reuseFailAlloc_4381_, 1, v_snd_4355_);
v___x_4377_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4379_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v___x_4377_);
v___x_4379_ = v___x_4373_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4423_; 
v_a_4383_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4385_ = v___x_4370_;
v_isShared_4386_ = v_isSharedCheck_4423_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4370_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4423_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; uint8_t v___y_4389_; uint8_t v___x_4421_; 
v___x_4387_ = lean_box(0);
v___x_4421_ = l_Lean_Exception_isInterrupt(v_a_4383_);
if (v___x_4421_ == 0)
{
uint8_t v___x_4422_; 
lean_inc(v_a_4383_);
v___x_4422_ = l_Lean_Exception_isRuntime(v_a_4383_);
v___y_4389_ = v___x_4422_;
goto v___jp_4388_;
}
else
{
v___y_4389_ = v___x_4421_;
goto v___jp_4388_;
}
v___jp_4388_:
{
if (v___y_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_del_object(v___x_4385_);
lean_inc_ref(v_values_4343_);
lean_inc_ref(v_xs_4342_);
v___x_4390_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4341_, v_xs_4342_, v_values_4343_, v_comb_4361_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref(v___x_4390_);
v___x_4392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4364_ == 0)
{
lean_ctor_set_tag(v___x_4363_, 7);
lean_ctor_set(v___x_4363_, 1, v_a_4391_);
lean_ctor_set(v___x_4363_, 0, v___x_4392_);
v___x_4394_ = v___x_4363_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_a_4391_);
v___x_4394_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4395_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = l_Lean_Exception_toMessageData(v_a_4383_);
v___x_4398_ = l_Lean_indentD(v___x_4397_);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4396_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v_snd_4355_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 1, v___x_4402_);
lean_ctor_set(v___x_4357_, 0, v___x_4387_);
v___x_4404_ = v___x_4357_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
size_t v___x_4405_; size_t v___x_4406_; 
v___x_4405_ = ((size_t)1ULL);
v___x_4406_ = lean_usize_add(v_i_4346_, v___x_4405_);
v_i_4346_ = v___x_4406_;
v_b_4347_ = v___x_4404_;
goto _start;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_a_4383_);
lean_del_object(v___x_4363_);
lean_del_object(v___x_4357_);
lean_dec(v_snd_4355_);
lean_dec_ref(v_values_4343_);
lean_dec_ref(v_xs_4342_);
lean_dec_ref(v_k_4340_);
v_a_4410_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4390_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4390_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_object* v___x_4419_; 
lean_del_object(v___x_4363_);
lean_dec_ref(v_comb_4361_);
lean_del_object(v___x_4357_);
lean_dec(v_snd_4355_);
lean_dec_ref(v_values_4343_);
lean_dec_ref(v_xs_4342_);
lean_dec_ref(v_k_4340_);
if (v_isShared_4386_ == 0)
{
v___x_4419_ = v___x_4385_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4383_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4427_, lean_object* v_fnNames_4428_, lean_object* v_xs_4429_, lean_object* v_values_4430_, lean_object* v_as_4431_, lean_object* v_sz_4432_, lean_object* v_i_4433_, lean_object* v_b_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
size_t v_sz_boxed_4440_; size_t v_i_boxed_4441_; lean_object* v_res_4442_; 
v_sz_boxed_4440_ = lean_unbox_usize(v_sz_4432_);
lean_dec(v_sz_4432_);
v_i_boxed_4441_ = lean_unbox_usize(v_i_4433_);
lean_dec(v_i_4433_);
v_res_4442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4427_, v_fnNames_4428_, v_xs_4429_, v_values_4430_, v_as_4431_, v_sz_boxed_4440_, v_i_boxed_4441_, v_b_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec_ref(v_as_4431_);
lean_dec_ref(v_fnNames_4428_);
return v_res_4442_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4445_ = l_Lean_stringToMessageData(v___x_4444_);
return v___x_4445_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4447_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4448_ = l_Lean_stringToMessageData(v___x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4449_, lean_object* v_xs_4450_, lean_object* v_values_4451_, lean_object* v_candidates_4452_, lean_object* v_k_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_candidates_4459_; lean_object* v_report_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4519_; 
v_candidates_4459_ = lean_ctor_get(v_candidates_4452_, 0);
v_report_4460_ = lean_ctor_get(v_candidates_4452_, 1);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_candidates_4452_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4462_ = v_candidates_4452_;
v_isShared_4463_ = v_isSharedCheck_4519_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_report_4460_);
lean_inc(v_candidates_4459_);
lean_dec(v_candidates_4452_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4519_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4464_ = lean_box(0);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4464_);
v___x_4466_ = v___x_4462_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_report_4460_);
v___x_4466_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
size_t v_sz_4467_; size_t v___x_4468_; lean_object* v___x_4469_; 
v_sz_4467_ = lean_array_size(v_candidates_4459_);
v___x_4468_ = ((size_t)0ULL);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4453_, v_fnNames_4449_, v_xs_4450_, v_values_4451_, v_candidates_4459_, v_sz_4467_, v___x_4468_, v___x_4466_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
lean_dec_ref(v_candidates_4459_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4509_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4472_ = v___x_4469_;
v_isShared_4473_ = v_isSharedCheck_4509_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4509_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_fst_4474_; 
v_fst_4474_ = lean_ctor_get(v_a_4470_, 0);
if (lean_obj_tag(v_fst_4474_) == 0)
{
lean_object* v_options_4475_; lean_object* v_snd_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4503_; 
lean_del_object(v___x_4472_);
v_options_4475_ = lean_ctor_get(v_a_4456_, 2);
v_snd_4476_ = lean_ctor_get(v_a_4470_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_a_4470_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v_a_4470_, 0);
lean_dec(v_unused_4504_);
v___x_4478_ = v_a_4470_;
v_isShared_4479_ = v_isSharedCheck_4503_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_snd_4476_);
lean_dec(v_a_4470_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4503_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v_inheritedTraceOptions_4480_; uint8_t v_hasTrace_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
v_inheritedTraceOptions_4480_ = lean_ctor_get(v_a_4456_, 13);
v_hasTrace_4481_ = lean_ctor_get_uint8(v_options_4475_, sizeof(void*)*1);
v___x_4482_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4479_ == 0)
{
lean_ctor_set_tag(v___x_4478_, 7);
lean_ctor_set(v___x_4478_, 0, v___x_4482_);
v___x_4484_ = v___x_4478_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4482_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_snd_4476_);
v___x_4484_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
if (v_hasTrace_4481_ == 0)
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
return v___x_4485_;
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4486_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4487_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4480_, v_options_4475_, v___x_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
return v___x_4489_;
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4484_);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
lean_ctor_set(v___x_4491_, 1, v___x_4484_);
v___x_4492_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4486_, v___x_4491_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v___x_4493_; 
lean_dec_ref(v___x_4492_);
v___x_4493_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
return v___x_4493_;
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref(v___x_4484_);
v_a_4494_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4492_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4492_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
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
lean_object* v_val_4505_; lean_object* v___x_4507_; 
lean_inc_ref(v_fst_4474_);
lean_dec(v_a_4470_);
v_val_4505_ = lean_ctor_get(v_fst_4474_, 0);
lean_inc(v_val_4505_);
lean_dec_ref(v_fst_4474_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v_val_4505_);
v___x_4507_ = v___x_4472_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_val_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
v_a_4510_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4469_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4469_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4520_, lean_object* v_xs_4521_, lean_object* v_values_4522_, lean_object* v_candidates_4523_, lean_object* v_k_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4520_, v_xs_4521_, v_values_4522_, v_candidates_4523_, v_k_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec_ref(v_fnNames_4520_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4531_, lean_object* v_fnNames_4532_, lean_object* v_xs_4533_, lean_object* v_values_4534_, lean_object* v_candidates_4535_, lean_object* v_k_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4532_, v_xs_4533_, v_values_4534_, v_candidates_4535_, v_k_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4543_, lean_object* v_fnNames_4544_, lean_object* v_xs_4545_, lean_object* v_values_4546_, lean_object* v_candidates_4547_, lean_object* v_k_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4543_, v_fnNames_4544_, v_xs_4545_, v_values_4546_, v_candidates_4547_, v_k_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec_ref(v_fnNames_4544_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4555_, lean_object* v_k_4556_, lean_object* v_fnNames_4557_, lean_object* v_xs_4558_, lean_object* v_values_4559_, lean_object* v_as_4560_, size_t v_sz_4561_, size_t v_i_4562_, lean_object* v_b_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4556_, v_fnNames_4557_, v_xs_4558_, v_values_4559_, v_as_4560_, v_sz_4561_, v_i_4562_, v_b_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4570_, lean_object* v_k_4571_, lean_object* v_fnNames_4572_, lean_object* v_xs_4573_, lean_object* v_values_4574_, lean_object* v_as_4575_, lean_object* v_sz_4576_, lean_object* v_i_4577_, lean_object* v_b_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_sz_boxed_4584_; size_t v_i_boxed_4585_; lean_object* v_res_4586_; 
v_sz_boxed_4584_ = lean_unbox_usize(v_sz_4576_);
lean_dec(v_sz_4576_);
v_i_boxed_4585_ = lean_unbox_usize(v_i_4577_);
lean_dec(v_i_4577_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4570_, v_k_4571_, v_fnNames_4572_, v_xs_4573_, v_values_4574_, v_as_4575_, v_sz_boxed_4584_, v_i_boxed_4585_, v_b_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v_as_4575_);
lean_dec_ref(v_fnNames_4572_);
return v_res_4586_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
