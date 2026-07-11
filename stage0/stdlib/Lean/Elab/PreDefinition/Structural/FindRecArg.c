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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "{indInfo.name} not in {indInfo.all}"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__3;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "its type is an inductive datatype"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__5;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\nand the datatype parameter"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__7;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\ndepends on the function parameter"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__9;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "\nwhich is not fixed."};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__11;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "its type "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__12 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__13;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " is an inductive family"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__14 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__15;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nand index"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__16 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__17;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\ndepends on the non index"};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__18 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfo___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfo___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfo___closed__19;
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfo___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = " is an inductive family and indices are not pairwise distinct"};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = lean_unsigned_to_nat(16u);
v___x_470_ = lean_mk_array(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_474_, lean_object* v_fvarId_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; uint8_t v_fst_480_; lean_object* v_mctx_481_; lean_object* v_mctx_498_; lean_object* v___f_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___y_504_; uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_478_ = lean_st_ref_get(v___y_476_);
v_mctx_498_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref_n(v_mctx_498_, 2);
lean_dec(v___x_478_);
v___f_499_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_500_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_500_, 0, v_fvarId_475_);
v___x_501_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_mctx_498_);
v___x_511_ = l_Lean_Expr_hasFVar(v_e_474_);
v___x_512_ = lean_bool_not(v___x_511_);
if (v___x_512_ == 0)
{
v___y_504_ = v___x_512_;
goto v___jp_503_;
}
else
{
uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = l_Lean_Expr_hasMVar(v_e_474_);
v___x_514_ = lean_bool_not(v___x_513_);
v___y_504_ = v___x_514_;
goto v___jp_503_;
}
v___jp_479_:
{
lean_object* v___x_482_; lean_object* v_cache_483_; lean_object* v_zetaDeltaFVarIds_484_; lean_object* v_postponed_485_; lean_object* v_diag_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_496_; 
v___x_482_ = lean_st_ref_take(v___y_476_);
v_cache_483_ = lean_ctor_get(v___x_482_, 1);
v_zetaDeltaFVarIds_484_ = lean_ctor_get(v___x_482_, 2);
v_postponed_485_ = lean_ctor_get(v___x_482_, 3);
v_diag_486_ = lean_ctor_get(v___x_482_, 4);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_482_, 0);
lean_dec(v_unused_497_);
v___x_488_ = v___x_482_;
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_diag_486_);
lean_inc(v_postponed_485_);
lean_inc(v_zetaDeltaFVarIds_484_);
lean_inc(v_cache_483_);
lean_dec(v___x_482_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v_mctx_481_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_mctx_481_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_cache_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_zetaDeltaFVarIds_484_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_postponed_485_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_diag_486_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_st_ref_set(v___y_476_, v___x_491_);
v___x_493_ = lean_box(v_fst_480_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
v___jp_503_:
{
if (v___y_504_ == 0)
{
lean_object* v___x_505_; lean_object* v_snd_506_; lean_object* v_fst_507_; lean_object* v_mctx_508_; uint8_t v___x_509_; 
lean_dec_ref(v_mctx_498_);
v___x_505_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_500_, v___f_499_, v_e_474_, v___x_502_);
v_snd_506_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_snd_506_);
v_fst_507_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_fst_507_);
lean_dec_ref(v___x_505_);
v_mctx_508_ = lean_ctor_get(v_snd_506_, 1);
lean_inc_ref(v_mctx_508_);
lean_dec(v_snd_506_);
v___x_509_ = lean_unbox(v_fst_507_);
lean_dec(v_fst_507_);
v_fst_480_ = v___x_509_;
v_mctx_481_ = v_mctx_508_;
goto v___jp_479_;
}
else
{
uint8_t v___x_510_; 
lean_dec_ref_known(v___x_502_, 2);
lean_dec_ref(v___f_500_);
lean_dec_ref(v_e_474_);
v___x_510_ = 0;
v_fst_480_ = v___x_510_;
v_mctx_481_ = v_mctx_498_;
goto v___jp_479_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_indices_572_, lean_object* v_as_573_, size_t v_sz_574_, size_t v_i_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_a_571_);
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
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_608_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_608_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_608_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_608_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___y_594_; uint8_t v___x_605_; uint8_t v___x_606_; 
v___x_591_ = lean_box(0);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_605_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_572_, v_a_584_);
v___x_606_ = lean_bool_not(v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_a_587_);
v___y_594_ = v___x_606_;
goto v___jp_593_;
}
else
{
uint8_t v___x_607_; 
v___x_607_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
v___y_594_ = v___x_607_;
goto v___jp_593_;
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
size_t v___x_595_; size_t v___x_596_; 
lean_del_object(v___x_589_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_575_, v___x_595_);
v_i_575_ = v___x_596_;
v_b_576_ = v___x_592_;
goto _start;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec_ref(v_a_570_);
lean_inc(v_a_584_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_571_);
lean_ctor_set(v___x_598_, 1, v_a_584_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_601_);
v___x_603_ = v___x_589_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_a_571_);
lean_dec_ref(v_a_570_);
v_a_609_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_586_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_586_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_indices_619_, lean_object* v_as_620_, lean_object* v_sz_621_, lean_object* v_i_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
size_t v_sz_boxed_629_; size_t v_i_boxed_630_; lean_object* v_res_631_; 
v_sz_boxed_629_ = lean_unbox_usize(v_sz_621_);
lean_dec(v_sz_621_);
v_i_boxed_630_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_617_, v_a_618_, v_indices_619_, v_as_620_, v_sz_boxed_629_, v_i_boxed_630_, v_b_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v_as_620_);
lean_dec_ref(v_indices_619_);
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
lean_object* v_a_645_; lean_object* v___x_646_; 
lean_dec_ref(v_b_637_);
v_a_645_ = lean_array_uget_borrowed(v_as_634_, v_i_636_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v_a_645_);
v___x_646_ = lean_infer_type(v_a_645_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_650_ = lean_array_size(v_ys_632_);
v___x_651_ = ((size_t)0ULL);
lean_inc(v_a_645_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_647_, v_a_645_, v_indices_633_, v_ys_632_, v_sz_650_, v___x_651_, v___x_649_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
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
v_b_637_ = v___x_649_;
goto _start;
}
else
{
lean_object* v___x_665_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_648_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_648_);
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
v_a_673_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_646_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_646_);
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
lean_object* v_a_708_; lean_object* v___x_709_; 
lean_dec_ref(v_b_700_);
v_a_708_ = lean_array_uget_borrowed(v_as_697_, v_i_699_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v_a_708_);
v___x_709_ = lean_infer_type(v_a_708_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_box(0);
v___x_712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_713_ = lean_array_size(v_ys_696_);
v___x_714_ = ((size_t)0ULL);
lean_inc(v_a_708_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_710_, v_a_708_, v_indices_695_, v_ys_696_, v_sz_713_, v___x_714_, v___x_712_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
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
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_696_, v_indices_695_, v_as_697_, v_sz_698_, v___x_725_, v___x_712_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_726_;
}
else
{
lean_object* v___x_728_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_711_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_711_);
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
v_a_736_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_709_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_709_);
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
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_b_803_);
v_a_808_ = lean_array_uget_borrowed(v_as_800_, v_i_802_);
v___x_809_ = l_Lean_Expr_fvarId_x21(v_a_808_);
lean_inc_ref(v_a_799_);
v___x_810_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_799_, v___x_809_, v___y_804_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_828_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_828_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_828_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_828_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_box(0);
v___x_816_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; size_t v___x_818_; size_t v___x_819_; 
lean_del_object(v___x_813_);
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_i_802_, v___x_818_);
v_i_802_ = v___x_819_;
v_b_803_ = v___x_817_;
goto _start;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_a_808_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_799_);
lean_ctor_set(v___x_821_, 1, v_a_808_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_824_);
v___x_826_ = v___x_813_;
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
v_a_829_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_810_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_810_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___f_973_; lean_object* v___x_5980__overap_974_; lean_object* v___x_975_; 
v___f_973_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_5980__overap_974_ = lean_panic_fn_borrowed(v___f_973_, v_msg_967_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
v___x_975_ = lean_apply_5(v___x_5980__overap_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_ref_989_; lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_ref_989_ = lean_ctor_get(v___y_986_, 5);
v___x_990_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_ref_989_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_ref_989_);
lean_ctor_set(v___x_995_, 1, v_a_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_1011_ = lean_unsigned_to_nat(107u);
v___x_1012_ = lean_unsigned_to_nat(97u);
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1015_ = l_mkPanicMessageWithDecl(v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_, v___x_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1016_, size_t v_sz_1017_, size_t v_i_1018_, lean_object* v_bs_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1018_, v_sz_1017_);
if (v___x_1020_ == 0)
{
return v_bs_1019_;
}
else
{
lean_object* v_v_1021_; lean_object* v___x_1022_; lean_object* v_bs_x27_1023_; lean_object* v___y_1025_; lean_object* v___x_1030_; 
v_v_1021_ = lean_array_uget(v_bs_1019_, v_i_1018_);
v___x_1022_ = lean_unsigned_to_nat(0u);
v_bs_x27_1023_ = lean_array_uset(v_bs_1019_, v_i_1018_, v___x_1022_);
v___x_1030_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_1016_, v_v_1021_);
lean_dec(v_v_1021_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3);
v___x_1032_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1031_);
v___y_1025_ = v___x_1032_;
goto v___jp_1024_;
}
else
{
lean_object* v_val_1033_; 
v_val_1033_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v___x_1030_, 1);
v___y_1025_ = v_val_1033_;
goto v___jp_1024_;
}
v___jp_1024_:
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1018_, v___x_1026_);
v___x_1028_ = lean_array_uset(v_bs_x27_1023_, v_i_1018_, v___y_1025_);
v_i_1018_ = v___x_1027_;
v_bs_1019_ = v___x_1028_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_bs_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1034_, v_sz_boxed_1038_, v_i_boxed_1039_, v_bs_1037_);
lean_dec_ref(v_xs_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(lean_object* v_as_1041_, lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_zero_1044_; uint8_t v_isZero_1045_; 
v_zero_1044_ = lean_unsigned_to_nat(0u);
v_isZero_1045_ = lean_nat_dec_eq(v_x_1043_, v_zero_1044_);
if (v_isZero_1045_ == 1)
{
lean_dec(v_x_1043_);
return v_isZero_1045_;
}
else
{
lean_object* v_one_1046_; lean_object* v_n_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; 
v_one_1046_ = lean_unsigned_to_nat(1u);
v_n_1047_ = lean_nat_sub(v_x_1043_, v_one_1046_);
lean_dec(v_x_1043_);
v___x_1048_ = lean_array_fget_borrowed(v_as_1041_, v_n_1047_);
v___x_1049_ = lean_expr_eqv(v_a_1042_, v___x_1048_);
v___x_1050_ = lean_bool_not(v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec(v_n_1047_);
return v___x_1050_;
}
else
{
v_x_1043_ = v_n_1047_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_as_1052_, lean_object* v_a_1053_, lean_object* v_x_1054_){
_start:
{
uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1052_, v_a_1053_, v_x_1054_);
lean_dec_ref(v_a_1053_);
lean_dec_ref(v_as_1052_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(lean_object* v_as_1057_, lean_object* v_i_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_array_get_size(v_as_1057_);
v___x_1060_ = lean_nat_dec_lt(v_i_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; 
lean_dec(v_i_1058_);
v___x_1061_ = 1;
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_array_fget_borrowed(v_as_1057_, v_i_1058_);
lean_inc(v_i_1058_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1057_, v___x_1062_, v_i_1058_);
if (v___x_1063_ == 0)
{
lean_dec(v_i_1058_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_i_1058_, v___x_1064_);
lean_dec(v_i_1058_);
v_i_1058_ = v___x_1065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(lean_object* v_as_1067_, lean_object* v_i_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1067_, v_i_1068_);
lean_dec_ref(v_as_1067_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_as_1071_){
_start:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1071_, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_as_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_as_1074_);
lean_dec_ref(v_as_1074_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_as_1077_, size_t v_i_1078_, size_t v_stop_1079_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_eq(v_i_1078_, v_stop_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_array_uget_borrowed(v_as_1077_, v_i_1078_);
v___x_1082_ = l_Lean_Expr_isFVar(v___x_1081_);
v___x_1083_ = lean_bool_not(v___x_1082_);
if (v___x_1083_ == 0)
{
size_t v___x_1084_; size_t v___x_1085_; 
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1078_, v___x_1084_);
v_i_1078_ = v___x_1085_;
goto _start;
}
else
{
return v___x_1083_;
}
}
else
{
uint8_t v___x_1087_; 
v___x_1087_ = 0;
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_as_1088_, lean_object* v_i_1089_, lean_object* v_stop_1090_){
_start:
{
size_t v_i_boxed_1091_; size_t v_stop_boxed_1092_; uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_i_boxed_1091_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_stop_boxed_1092_ = lean_unbox_usize(v_stop_1090_);
lean_dec(v_stop_1090_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_as_1088_, v_i_boxed_1091_, v_stop_boxed_1092_);
lean_dec_ref(v_as_1088_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(lean_object* v_xs_1095_, lean_object* v_v_1096_, lean_object* v_i_1097_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_array_get_size(v_xs_1095_);
v___x_1099_ = lean_nat_dec_lt(v_i_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec(v_i_1097_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_array_fget_borrowed(v_xs_1095_, v_i_1097_);
v___x_1102_ = lean_name_eq(v___x_1101_, v_v_1096_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_i_1097_, v___x_1103_);
lean_dec(v_i_1097_);
v_i_1097_ = v___x_1104_;
goto _start;
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_i_1097_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(lean_object* v_xs_1107_, lean_object* v_v_1108_, lean_object* v_i_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1107_, v_v_1108_, v_i_1109_);
lean_dec(v_v_1108_);
lean_dec_ref(v_xs_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(lean_object* v_xs_1111_, lean_object* v_v_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1111_, v_v_1112_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(lean_object* v_xs_1115_, lean_object* v_v_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1115_, v_v_1116_);
lean_dec(v_v_1116_);
lean_dec_ref(v_xs_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_xs_1118_, lean_object* v_v_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1118_, v_v_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_box(0);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_val_1122_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1120_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v___x_1120_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_val_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_xs_1130_, lean_object* v_v_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_xs_1130_, v_v_1131_);
lean_dec(v_v_1131_);
lean_dec_ref(v_xs_1130_);
return v_res_1132_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1138_ = lean_unsigned_to_nat(59u);
v___x_1139_ = lean_unsigned_to_nat(96u);
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1142_ = l_mkPanicMessageWithDecl(v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_);
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
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1169_ = l_Lean_stringToMessageData(v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1173_; lean_object* v_dummy_1174_; 
v___x_1173_ = lean_box(0);
v_dummy_1174_ = l_Lean_Expr_sort___override(v___x_1173_);
return v_dummy_1174_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = lean_unsigned_to_nat(68u);
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1184_ = l_mkPanicMessageWithDecl(v___x_1183_, v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1187_ = l_Lean_stringToMessageData(v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1190_ = l_Lean_stringToMessageData(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1197_, lean_object* v_fixedParamPerm_1198_, lean_object* v_xs_1199_, lean_object* v_i_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; uint8_t v___y_1225_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v_lower_1358_; lean_object* v_upper_1359_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_array_get_size(v_fixedParamPerm_1198_);
v___x_1439_ = lean_array_get_size(v_xs_1199_);
v___x_1440_ = lean_nat_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___x_1441_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1442_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1441_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
return v___x_1442_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_nat_dec_lt(v_i_1200_, v___x_1439_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_i_1200_, v___x_1445_);
lean_dec(v_i_1200_);
v___x_1447_ = l_Nat_reprFast(v___x_1446_);
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l_Lean_MessageData_ofFormat(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1444_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Nat_reprFast(v___x_1439_);
v___x_1454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
v___x_1455_ = l_Lean_MessageData_ofFormat(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1452_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1458_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1198_, v_i_1200_);
if (v___x_1460_ == 0)
{
v___y_1411_ = v_a_1201_;
v___y_1412_ = v_a_1202_;
v___y_1413_ = v_a_1203_;
v___y_1414_ = v_a_1204_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1462_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1461_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1212_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1211_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1212_;
}
v___jp_1213_:
{
uint8_t v___x_1226_; 
v___x_1226_ = lean_bool_not(v___y_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1215_);
v___x_1228_ = lean_bool_not(v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1198_, v_xs_1199_);
v___x_1230_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1229_, v___y_1215_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
if (lean_obj_tag(v_a_1231_) == 0)
{
lean_object* v___x_1232_; 
v___x_1232_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1229_, v___y_1221_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
lean_dec_ref(v___x_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1283_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1283_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1283_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v_name_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v___y_1222_);
v_name_1237_ = lean_ctor_get(v___y_1219_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___y_1219_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; lean_object* v_unused_1259_; 
v_unused_1258_ = lean_ctor_get(v___y_1219_, 2);
lean_dec(v_unused_1258_);
v_unused_1259_ = lean_ctor_get(v___y_1219_, 1);
lean_dec(v_unused_1259_);
v___x_1239_ = v___y_1219_;
v_isShared_1240_ = v_isSharedCheck_1257_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_name_1237_);
lean_dec(v___y_1219_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1257_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_array_mk(v___y_1217_);
v___x_1242_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___x_1241_, v_name_1237_);
lean_dec(v_name_1237_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; size_t v_sz_1244_; size_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v_sz_1244_ = lean_array_size(v___y_1215_);
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1199_, v_sz_1244_, v___x_1245_, v___y_1215_);
v___x_1247_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1220_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___y_1221_);
lean_ctor_set(v___x_1239_, 1, v___y_1216_);
lean_ctor_set(v___x_1239_, 0, v___x_1247_);
v___x_1249_ = v___x_1239_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___y_1216_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v___y_1221_);
v___x_1249_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1250_, 0, v_fnName_1197_);
lean_ctor_set(v___x_1250_, 1, v_fixedParamPerm_1198_);
lean_ctor_set(v___x_1250_, 2, v_i_1200_);
lean_ctor_set(v___x_1250_, 3, v___x_1246_);
lean_ctor_set(v___x_1250_, 4, v___x_1249_);
lean_ctor_set(v___x_1250_, 5, v_val_1243_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1250_);
v___x_1252_ = v___x_1235_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v___x_1242_);
lean_del_object(v___x_1239_);
lean_del_object(v___x_1235_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___x_1255_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1256_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1255_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
return v___x_1256_;
}
}
}
else
{
lean_object* v_val_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1235_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_val_1260_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_a_1233_, 1);
v_fst_1261_ = lean_ctor_get(v_val_1260_, 0);
v_snd_1262_ = lean_ctor_get(v_val_1260_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_val_1260_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1264_ = v_val_1260_;
v_isShared_1265_ = v_isSharedCheck_1282_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_inc(v_fst_1261_);
lean_dec(v_val_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1282_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1267_ = l_Lean_indentExpr(v___y_1222_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 7);
lean_ctor_set(v___x_1264_, 1, v___x_1267_);
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1270_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_indentExpr(v_fst_1261_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_indentExpr(v_snd_1262_);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1279_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_a_1284_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1232_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1232_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_val_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_val_1292_ = lean_ctor_get(v_a_1231_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v_a_1231_, 1);
v_fst_1293_ = lean_ctor_get(v_val_1292_, 0);
v_snd_1294_ = lean_ctor_get(v_val_1292_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_val_1292_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1296_ = v_val_1292_;
v_isShared_1297_ = v_isSharedCheck_1317_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_inc(v_fst_1293_);
lean_dec(v_val_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1317_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_name_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_name_1298_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_name_1298_);
lean_dec_ref(v___y_1219_);
v___x_1299_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1300_ = l_Lean_MessageData_ofName(v_name_1298_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 7);
lean_ctor_set(v___x_1296_, 1, v___x_1300_);
lean_ctor_set(v___x_1296_, 0, v___x_1299_);
v___x_1302_ = v___x_1296_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = l_Lean_indentExpr(v___y_1222_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_indentExpr(v_fst_1293_);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_indentExpr(v_snd_1294_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1314_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_a_1318_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1230_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1230_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_name_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_name_1326_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_name_1326_);
lean_dec_ref(v___y_1219_);
v___x_1327_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1328_ = l_Lean_MessageData_ofName(v_name_1326_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_indentExpr(v___y_1222_);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1333_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
return v___x_1334_;
}
}
else
{
lean_object* v_name_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_name_1335_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_name_1335_);
lean_dec_ref(v___y_1219_);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1337_ = l_Lean_MessageData_ofName(v_name_1335_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_indentExpr(v___y_1222_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1342_, v___y_1214_, v___y_1224_, v___y_1223_, v___y_1218_);
return v___x_1343_;
}
}
v___jp_1344_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1360_ = l_Array_toSubarray___redArg(v___y_1347_, v_lower_1358_, v_upper_1359_);
v___x_1361_ = l_Subarray_copy___redArg(v___x_1360_);
v___x_1362_ = lean_array_get_size(v___x_1361_);
v___x_1363_ = lean_nat_dec_lt(v___y_1356_, v___x_1362_);
lean_dec(v___y_1356_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_bool_not(v___y_1345_);
v___y_1214_ = v___y_1346_;
v___y_1215_ = v___x_1361_;
v___y_1216_ = v___y_1351_;
v___y_1217_ = v___y_1348_;
v___y_1218_ = v___y_1352_;
v___y_1219_ = v___y_1353_;
v___y_1220_ = v___y_1354_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___y_1350_;
v___y_1223_ = v___y_1355_;
v___y_1224_ = v___y_1357_;
v___y_1225_ = v___x_1364_;
goto v___jp_1213_;
}
else
{
if (v___x_1363_ == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_bool_not(v___y_1345_);
v___y_1214_ = v___y_1346_;
v___y_1215_ = v___x_1361_;
v___y_1216_ = v___y_1351_;
v___y_1217_ = v___y_1348_;
v___y_1218_ = v___y_1352_;
v___y_1219_ = v___y_1353_;
v___y_1220_ = v___y_1354_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___y_1350_;
v___y_1223_ = v___y_1355_;
v___y_1224_ = v___y_1357_;
v___y_1225_ = v___x_1365_;
goto v___jp_1213_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; uint8_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1362_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v___x_1361_, v___x_1366_, v___x_1367_);
v___x_1369_ = lean_bool_not(v___x_1368_);
v___y_1214_ = v___y_1346_;
v___y_1215_ = v___x_1361_;
v___y_1216_ = v___y_1351_;
v___y_1217_ = v___y_1348_;
v___y_1218_ = v___y_1352_;
v___y_1219_ = v___y_1353_;
v___y_1220_ = v___y_1354_;
v___y_1221_ = v___y_1349_;
v___y_1222_ = v___y_1350_;
v___y_1223_ = v___y_1355_;
v___y_1224_ = v___y_1357_;
v___y_1225_ = v___x_1369_;
goto v___jp_1213_;
}
}
}
v___jp_1370_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = l_Lean_LocalDecl_type(v___y_1371_);
lean_dec_ref(v___y_1371_);
v___x_1377_ = l_Lean_Meta_whnfD(v___x_1376_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Lean_Expr_getAppFn(v_a_1378_);
if (lean_obj_tag(v___x_1379_) == 4)
{
lean_object* v_declName_1380_; lean_object* v_us_1381_; lean_object* v___x_1382_; lean_object* v_env_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
v_declName_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_declName_1380_);
v_us_1381_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_us_1381_);
lean_dec_ref_known(v___x_1379_, 2);
v___x_1382_ = lean_st_ref_get(v___y_1375_);
v_env_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_env_1383_);
lean_dec(v___x_1382_);
v___x_1384_ = 0;
v___x_1385_ = l_Lean_Environment_find_x3f(v_env_1383_, v_declName_1380_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_dec(v_us_1381_);
lean_dec(v_a_1378_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___y_1207_ = v___y_1372_;
v___y_1208_ = v___y_1373_;
v___y_1209_ = v___y_1374_;
v___y_1210_ = v___y_1375_;
goto v___jp_1206_;
}
else
{
lean_object* v_val_1386_; 
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1385_, 1);
if (lean_obj_tag(v_val_1386_) == 5)
{
lean_object* v_val_1387_; lean_object* v_toConstantVal_1388_; lean_object* v_numParams_1389_; lean_object* v_all_1390_; lean_object* v_nargs_1391_; lean_object* v_dummy_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_val_1387_ = lean_ctor_get(v_val_1386_, 0);
lean_inc_ref(v_val_1387_);
lean_dec_ref_known(v_val_1386_, 1);
v_toConstantVal_1388_ = lean_ctor_get(v_val_1387_, 0);
lean_inc_ref(v_toConstantVal_1388_);
v_numParams_1389_ = lean_ctor_get(v_val_1387_, 1);
v_all_1390_ = lean_ctor_get(v_val_1387_, 3);
lean_inc(v_all_1390_);
v_nargs_1391_ = l_Lean_Expr_getAppNumArgs(v_a_1378_);
v_dummy_1392_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1391_);
v___x_1393_ = lean_mk_array(v_nargs_1391_, v_dummy_1392_);
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_sub(v_nargs_1391_, v___x_1394_);
lean_dec(v_nargs_1391_);
lean_inc(v_a_1378_);
v___x_1396_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1378_, v___x_1393_, v___x_1395_);
v___x_1397_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1389_);
lean_inc_ref(v___x_1396_);
v___x_1398_ = l_Array_toSubarray___redArg(v___x_1396_, v___x_1397_, v_numParams_1389_);
v___x_1399_ = l_Subarray_copy___redArg(v___x_1398_);
v___x_1400_ = lean_array_get_size(v___x_1396_);
v___x_1401_ = lean_nat_dec_le(v_numParams_1389_, v___x_1397_);
if (v___x_1401_ == 0)
{
lean_inc(v_numParams_1389_);
v___y_1345_ = v___x_1384_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___x_1396_;
v___y_1348_ = v_all_1390_;
v___y_1349_ = v___x_1399_;
v___y_1350_ = v_a_1378_;
v___y_1351_ = v_us_1381_;
v___y_1352_ = v___y_1375_;
v___y_1353_ = v_toConstantVal_1388_;
v___y_1354_ = v_val_1387_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___x_1397_;
v___y_1357_ = v___y_1373_;
v_lower_1358_ = v_numParams_1389_;
v_upper_1359_ = v___x_1400_;
goto v___jp_1344_;
}
else
{
v___y_1345_ = v___x_1384_;
v___y_1346_ = v___y_1372_;
v___y_1347_ = v___x_1396_;
v___y_1348_ = v_all_1390_;
v___y_1349_ = v___x_1399_;
v___y_1350_ = v_a_1378_;
v___y_1351_ = v_us_1381_;
v___y_1352_ = v___y_1375_;
v___y_1353_ = v_toConstantVal_1388_;
v___y_1354_ = v_val_1387_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___x_1397_;
v___y_1357_ = v___y_1373_;
v_lower_1358_ = v___x_1397_;
v_upper_1359_ = v___x_1400_;
goto v___jp_1344_;
}
}
else
{
lean_dec(v_val_1386_);
lean_dec(v_us_1381_);
lean_dec(v_a_1378_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___y_1207_ = v___y_1372_;
v___y_1208_ = v___y_1373_;
v___y_1209_ = v___y_1374_;
v___y_1210_ = v___y_1375_;
goto v___jp_1206_;
}
}
}
else
{
lean_dec_ref(v___x_1379_);
lean_dec(v_a_1378_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___y_1207_ = v___y_1372_;
v___y_1208_ = v___y_1373_;
v___y_1209_ = v___y_1374_;
v___y_1210_ = v___y_1375_;
goto v___jp_1206_;
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_a_1402_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1377_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1377_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
v___jp_1410_:
{
lean_object* v_x_1415_; lean_object* v___x_1416_; 
v_x_1415_ = lean_array_fget_borrowed(v_xs_1199_, v_i_1200_);
v___x_1416_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1415_, v___y_1411_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; uint8_t v___x_1419_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = 0;
v___x_1419_ = l_Lean_LocalDecl_isLet(v_a_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
v___y_1371_ = v_a_1417_;
v___y_1372_ = v___y_1411_;
v___y_1373_ = v___y_1412_;
v___y_1374_ = v___y_1413_;
v___y_1375_ = v___y_1414_;
goto v___jp_1370_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_a_1417_);
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v___x_1420_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1421_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1420_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_i_1200_);
lean_dec_ref(v_fixedParamPerm_1198_);
lean_dec(v_fnName_1197_);
v_a_1430_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1416_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1416_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1471_, lean_object* v_fixedParamPerm_1472_, lean_object* v_xs_1473_, lean_object* v_i_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1471_, v_fixedParamPerm_1472_, v_xs_1473_, v_i_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_xs_1473_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_msg_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1489_, v_msg_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(lean_object* v_as_1497_, lean_object* v_a_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1497_, v_a_1498_, v_x_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(lean_object* v_as_1502_, lean_object* v_a_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
uint8_t v_res_1506_; lean_object* v_r_1507_; 
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(v_as_1502_, v_a_1503_, v_x_1504_, v_x_1505_);
lean_dec_ref(v_a_1503_);
lean_dec_ref(v_as_1502_);
v_r_1507_ = lean_box(v_res_1506_);
return v_r_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1508_, lean_object* v_e_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = l_Lean_indentD(v_e_1509_);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1508_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1512_, lean_object* v_fnName_1513_, lean_object* v_fixedParamPerm_1514_, lean_object* v_args_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1512_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1513_, v_fixedParamPerm_1514_, v_args_1515_, v_a_1522_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1523_;
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_fixedParamPerm_1514_);
lean_dec(v_fnName_1513_);
v_a_1524_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1521_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1521_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1532_, lean_object* v_fnName_1533_, lean_object* v_fixedParamPerm_1534_, lean_object* v_args_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1532_, v_fnName_1533_, v_fixedParamPerm_1534_, v_args_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_args_1535_);
return v_res_1541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1552_ = l_Lean_MessageData_ofFormat(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1553_, lean_object* v_fnName_1554_, lean_object* v_fixedParamPerm_1555_, lean_object* v_args_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_fst_1565_; lean_object* v_snd_1566_; uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_lt(v_a_1557_, v_upperBound_1553_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_a_1557_);
lean_dec_ref(v_fixedParamPerm_1555_);
lean_dec(v_fnName_1554_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_b_1558_);
return v___x_1572_;
}
else
{
lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1619_; 
v_fst_1573_ = lean_ctor_get(v_b_1558_, 0);
v_snd_1574_ = lean_ctor_get(v_b_1558_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_b_1558_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1576_ = v_b_1558_;
v_isShared_1577_ = v_isSharedCheck_1619_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_snd_1574_);
lean_inc(v_fst_1573_);
lean_dec(v_b_1558_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1619_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; 
lean_inc(v_a_1557_);
lean_inc_ref(v_fixedParamPerm_1555_);
lean_inc(v_fnName_1554_);
v___x_1578_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1554_, v_fixedParamPerm_1555_, v_args_1556_, v_a_1557_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1576_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_array_push(v_fst_1573_, v_a_1579_);
v_fst_1565_ = v___x_1580_;
v_snd_1566_ = v_snd_1574_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1618_; 
v_a_1581_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1583_ = v___x_1578_;
v_isShared_1584_ = v_isSharedCheck_1618_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1578_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1618_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
uint8_t v___y_1586_; uint8_t v___x_1616_; 
v___x_1616_ = l_Lean_Exception_isInterrupt(v_a_1581_);
if (v___x_1616_ == 0)
{
uint8_t v___x_1617_; 
lean_inc(v_a_1581_);
v___x_1617_ = l_Lean_Exception_isRuntime(v_a_1581_);
v___y_1586_ = v___x_1617_;
goto v___jp_1585_;
}
else
{
v___y_1586_ = v___x_1616_;
goto v___jp_1585_;
}
v___jp_1585_:
{
if (v___y_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_del_object(v___x_1583_);
v___x_1587_ = l_Lean_Elab_Structural_prettyParam(v_args_1556_, v_a_1557_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 7);
lean_ctor_set(v___x_1576_, 1, v_a_1588_);
lean_ctor_set(v___x_1576_, 0, v___x_1589_);
v___x_1591_ = v___x_1576_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_a_1588_);
v___x_1591_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
lean_inc(v_fnName_1554_);
v___x_1594_ = l_Lean_MessageData_ofName(v_fnName_1554_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_Exception_toMessageData(v_a_1581_);
v___x_1599_ = l_Lean_indentD(v___x_1598_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1597_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_snd_1574_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v_fst_1565_ = v_fst_1573_;
v_snd_1566_ = v___x_1603_;
goto v___jp_1564_;
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1581_);
lean_del_object(v___x_1576_);
lean_dec(v_snd_1574_);
lean_dec(v_fst_1573_);
lean_dec(v_a_1557_);
lean_dec_ref(v_fixedParamPerm_1555_);
lean_dec(v_fnName_1554_);
v_a_1605_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1587_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1587_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v___x_1614_; 
lean_del_object(v___x_1576_);
lean_dec(v_snd_1574_);
lean_dec(v_fst_1573_);
lean_dec(v_a_1557_);
lean_dec_ref(v_fixedParamPerm_1555_);
lean_dec(v_fnName_1554_);
if (v_isShared_1584_ == 0)
{
v___x_1614_ = v___x_1583_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1581_);
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
}
v___jp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_fst_1565_);
lean_ctor_set(v___x_1567_, 1, v_snd_1566_);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v_a_1557_, v___x_1568_);
lean_dec(v_a_1557_);
v_a_1557_ = v___x_1569_;
v_b_1558_ = v___x_1567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1620_, lean_object* v_fnName_1621_, lean_object* v_fixedParamPerm_1622_, lean_object* v_args_1623_, lean_object* v_a_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1620_, v_fnName_1621_, v_fixedParamPerm_1622_, v_args_1623_, v_a_1624_, v_b_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v_args_1623_);
lean_dec(v_upperBound_1620_);
return v_res_1631_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1632_; double v___x_1633_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_float_of_nat(v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1635_, lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_ref_1642_; lean_object* v___x_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1688_; 
v_ref_1642_ = lean_ctor_get(v___y_1639_, 5);
v___x_1643_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1688_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1688_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v_traceState_1649_; lean_object* v_env_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_ngen_1652_; lean_object* v_auxDeclNGen_1653_; lean_object* v_cache_1654_; lean_object* v_messages_1655_; lean_object* v_infoState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1687_; 
v___x_1648_ = lean_st_ref_take(v___y_1640_);
v_traceState_1649_ = lean_ctor_get(v___x_1648_, 4);
v_env_1650_ = lean_ctor_get(v___x_1648_, 0);
v_nextMacroScope_1651_ = lean_ctor_get(v___x_1648_, 1);
v_ngen_1652_ = lean_ctor_get(v___x_1648_, 2);
v_auxDeclNGen_1653_ = lean_ctor_get(v___x_1648_, 3);
v_cache_1654_ = lean_ctor_get(v___x_1648_, 5);
v_messages_1655_ = lean_ctor_get(v___x_1648_, 6);
v_infoState_1656_ = lean_ctor_get(v___x_1648_, 7);
v_snapshotTasks_1657_ = lean_ctor_get(v___x_1648_, 8);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1659_ = v___x_1648_;
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snapshotTasks_1657_);
lean_inc(v_infoState_1656_);
lean_inc(v_messages_1655_);
lean_inc(v_cache_1654_);
lean_inc(v_traceState_1649_);
lean_inc(v_auxDeclNGen_1653_);
lean_inc(v_ngen_1652_);
lean_inc(v_nextMacroScope_1651_);
lean_inc(v_env_1650_);
lean_dec(v___x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
uint64_t v_tid_1661_; lean_object* v_traces_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1686_; 
v_tid_1661_ = lean_ctor_get_uint64(v_traceState_1649_, sizeof(void*)*1);
v_traces_1662_ = lean_ctor_get(v_traceState_1649_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_traceState_1649_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1664_ = v_traceState_1649_;
v_isShared_1665_ = v_isSharedCheck_1686_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_traces_1662_);
lean_dec(v_traceState_1649_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1686_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; double v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1668_ = 0;
v___x_1669_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1670_, 0, v_cls_1635_);
lean_ctor_set(v___x_1670_, 1, v___x_1666_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3, v___x_1667_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3 + 8, v___x_1667_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 16, v___x_1668_);
v___x_1671_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1672_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v_a_1644_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_inc(v_ref_1642_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_ref_1642_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_PersistentArray_push___redArg(v_traces_1662_, v___x_1673_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1674_);
v___x_1676_ = v___x_1664_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1674_);
lean_ctor_set_uint64(v_reuseFailAlloc_1685_, sizeof(void*)*1, v_tid_1661_);
v___x_1676_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v___x_1676_);
v___x_1678_ = v___x_1659_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_env_1650_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_ngen_1652_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_auxDeclNGen_1653_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v_cache_1654_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v_messages_1655_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v_infoState_1656_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_snapshotTasks_1657_);
v___x_1678_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_st_ref_set(v___y_1640_, v___x_1678_);
v___x_1680_ = lean_box(0);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1680_);
v___x_1682_ = v___x_1646_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1689_, lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1689_, v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___f_1701_; 
v___x_1700_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1701_, 0, v___x_1700_);
return v___f_1701_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1706_; lean_object* v_recArgInfos_1707_; lean_object* v___x_1708_; 
v_report_1706_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1707_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_recArgInfos_1707_);
lean_ctor_set(v___x_1708_, 1, v_report_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1721_ = l_Lean_Name_append(v___x_1720_, v___x_1719_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1725_, lean_object* v_fixedParamPerm_1726_, lean_object* v_xs_1727_, lean_object* v_fnName_1728_, lean_object* v_ys_1729_, lean_object* v_x_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1725_) == 1)
{
lean_object* v_val_1736_; lean_object* v_ref_1737_; lean_object* v_fileName_1738_; lean_object* v_fileMap_1739_; lean_object* v_options_1740_; lean_object* v_currRecDepth_1741_; lean_object* v_maxRecDepth_1742_; lean_object* v_ref_1743_; lean_object* v_currNamespace_1744_; lean_object* v_openDecls_1745_; lean_object* v_initHeartbeats_1746_; lean_object* v_maxHeartbeats_1747_; lean_object* v_quotContext_1748_; lean_object* v_currMacroScope_1749_; uint8_t v_diag_1750_; lean_object* v_cancelTk_x3f_1751_; uint8_t v_suppressElabErrors_1752_; lean_object* v_inheritedTraceOptions_1753_; lean_object* v___f_1754_; lean_object* v_args_1755_; lean_object* v___f_1756_; lean_object* v_ref_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_val_1736_ = lean_ctor_get(v_termMeasure_x3f_1725_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v_termMeasure_x3f_1725_, 1);
v_ref_1737_ = lean_ctor_get(v_val_1736_, 0);
lean_inc(v_ref_1737_);
v_fileName_1738_ = lean_ctor_get(v___y_1733_, 0);
v_fileMap_1739_ = lean_ctor_get(v___y_1733_, 1);
v_options_1740_ = lean_ctor_get(v___y_1733_, 2);
v_currRecDepth_1741_ = lean_ctor_get(v___y_1733_, 3);
v_maxRecDepth_1742_ = lean_ctor_get(v___y_1733_, 4);
v_ref_1743_ = lean_ctor_get(v___y_1733_, 5);
v_currNamespace_1744_ = lean_ctor_get(v___y_1733_, 6);
v_openDecls_1745_ = lean_ctor_get(v___y_1733_, 7);
v_initHeartbeats_1746_ = lean_ctor_get(v___y_1733_, 8);
v_maxHeartbeats_1747_ = lean_ctor_get(v___y_1733_, 9);
v_quotContext_1748_ = lean_ctor_get(v___y_1733_, 10);
v_currMacroScope_1749_ = lean_ctor_get(v___y_1733_, 11);
v_diag_1750_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*14);
v_cancelTk_x3f_1751_ = lean_ctor_get(v___y_1733_, 12);
v_suppressElabErrors_1752_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1753_ = lean_ctor_get(v___y_1733_, 13);
v___f_1754_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1726_);
v_args_1755_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1726_, v_xs_1727_, v_ys_1729_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1756_, 0, v_val_1736_);
lean_closure_set(v___f_1756_, 1, v_fnName_1728_);
lean_closure_set(v___f_1756_, 2, v_fixedParamPerm_1726_);
lean_closure_set(v___f_1756_, 3, v_args_1755_);
v_ref_1757_ = l_Lean_replaceRef(v_ref_1737_, v_ref_1743_);
lean_dec(v_ref_1737_);
lean_inc_ref(v_inheritedTraceOptions_1753_);
lean_inc(v_cancelTk_x3f_1751_);
lean_inc(v_currMacroScope_1749_);
lean_inc(v_quotContext_1748_);
lean_inc(v_maxHeartbeats_1747_);
lean_inc(v_initHeartbeats_1746_);
lean_inc(v_openDecls_1745_);
lean_inc(v_currNamespace_1744_);
lean_inc(v_maxRecDepth_1742_);
lean_inc(v_currRecDepth_1741_);
lean_inc_ref(v_options_1740_);
lean_inc_ref(v_fileMap_1739_);
lean_inc_ref(v_fileName_1738_);
v___x_1758_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1758_, 0, v_fileName_1738_);
lean_ctor_set(v___x_1758_, 1, v_fileMap_1739_);
lean_ctor_set(v___x_1758_, 2, v_options_1740_);
lean_ctor_set(v___x_1758_, 3, v_currRecDepth_1741_);
lean_ctor_set(v___x_1758_, 4, v_maxRecDepth_1742_);
lean_ctor_set(v___x_1758_, 5, v_ref_1757_);
lean_ctor_set(v___x_1758_, 6, v_currNamespace_1744_);
lean_ctor_set(v___x_1758_, 7, v_openDecls_1745_);
lean_ctor_set(v___x_1758_, 8, v_initHeartbeats_1746_);
lean_ctor_set(v___x_1758_, 9, v_maxHeartbeats_1747_);
lean_ctor_set(v___x_1758_, 10, v_quotContext_1748_);
lean_ctor_set(v___x_1758_, 11, v_currMacroScope_1749_);
lean_ctor_set(v___x_1758_, 12, v_cancelTk_x3f_1751_);
lean_ctor_set(v___x_1758_, 13, v_inheritedTraceOptions_1753_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*14, v_diag_1750_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*14 + 1, v_suppressElabErrors_1752_);
v___x_1759_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1756_, v___f_1754_, v___y_1731_, v___y_1732_, v___x_1758_, v___y_1734_);
lean_dec_ref_known(v___x_1758_, 14);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1772_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
v___x_1766_ = lean_array_push(v___x_1765_, v_a_1760_);
v___x_1767_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1768_);
v___x_1770_ = v___x_1762_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1759_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1759_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_args_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v_termMeasure_x3f_1725_);
lean_inc_ref(v_fixedParamPerm_1726_);
v_args_1781_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1726_, v_xs_1727_, v_ys_1729_);
v___x_1782_ = lean_array_get_size(v_args_1781_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1782_, v_fnName_1728_, v_fixedParamPerm_1726_, v_args_1781_, v___x_1783_, v___x_1784_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec_ref(v_args_1781_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1820_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1820_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1820_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1819_; 
v_fst_1790_ = lean_ctor_get(v_a_1786_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1786_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_a_1786_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1793_ = v_a_1786_;
v_isShared_1794_ = v_isSharedCheck_1819_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1786_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1819_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_options_1802_; uint8_t v_hasTrace_1803_; 
v_options_1802_ = lean_ctor_get(v___y_1733_, 2);
v_hasTrace_1803_ = lean_ctor_get_uint8(v_options_1802_, sizeof(void*)*1);
if (v_hasTrace_1803_ == 0)
{
goto v___jp_1795_;
}
else
{
lean_object* v_inheritedTraceOptions_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_inheritedTraceOptions_1804_ = lean_ctor_get(v___y_1733_, 13);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1804_, v_options_1802_, v___x_1806_);
if (v___x_1807_ == 0)
{
goto v___jp_1795_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1791_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_snd_1791_);
v___x_1810_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1805_, v___x_1809_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_dec_ref_known(v___x_1810_, 1);
goto v___jp_1795_;
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_del_object(v___x_1793_);
lean_dec(v_snd_1791_);
lean_dec(v_fst_1790_);
lean_del_object(v___x_1788_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1797_; 
if (v_isShared_1794_ == 0)
{
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_snd_1791_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1797_);
v___x_1799_ = v___x_1788_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
else
{
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1821_, lean_object* v_fixedParamPerm_1822_, lean_object* v_xs_1823_, lean_object* v_fnName_1824_, lean_object* v_ys_1825_, lean_object* v_x_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1821_, v_fixedParamPerm_1822_, v_xs_1823_, v_fnName_1824_, v_ys_1825_, v_x_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_x_1826_);
lean_dec_ref(v_xs_1823_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1833_, lean_object* v_fixedParamPerm_1834_, lean_object* v_xs_1835_, lean_object* v_value_1836_, lean_object* v_termMeasure_x3f_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___f_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1843_, 0, v_termMeasure_x3f_1837_);
lean_closure_set(v___f_1843_, 1, v_fixedParamPerm_1834_);
lean_closure_set(v___f_1843_, 2, v_xs_1835_);
lean_closure_set(v___f_1843_, 3, v_fnName_1833_);
v___x_1844_ = 0;
v___x_1845_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1836_, v___f_1843_, v___x_1844_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1846_, lean_object* v_fixedParamPerm_1847_, lean_object* v_xs_1848_, lean_object* v_value_1849_, lean_object* v_termMeasure_x3f_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1846_, v_fixedParamPerm_1847_, v_xs_1848_, v_value_1849_, v_termMeasure_x3f_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1857_, lean_object* v_fnName_1858_, lean_object* v_fixedParamPerm_1859_, lean_object* v_args_1860_, lean_object* v_inst_1861_, lean_object* v_R_1862_, lean_object* v_a_1863_, lean_object* v_b_1864_, lean_object* v_c_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1857_, v_fnName_1858_, v_fixedParamPerm_1859_, v_args_1860_, v_a_1863_, v_b_1864_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1872_, lean_object* v_fnName_1873_, lean_object* v_fixedParamPerm_1874_, lean_object* v_args_1875_, lean_object* v_inst_1876_, lean_object* v_R_1877_, lean_object* v_a_1878_, lean_object* v_b_1879_, lean_object* v_c_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1872_, v_fnName_1873_, v_fixedParamPerm_1874_, v_args_1875_, v_inst_1876_, v_R_1877_, v_a_1878_, v_b_1879_, v_c_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v_args_1875_);
lean_dec(v_upperBound_1872_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
return v_x_1887_;
}
else
{
lean_object* v_key_1889_; lean_object* v_value_1890_; lean_object* v_tail_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1914_; 
v_key_1889_ = lean_ctor_get(v_x_1888_, 0);
v_value_1890_ = lean_ctor_get(v_x_1888_, 1);
v_tail_1891_ = lean_ctor_get(v_x_1888_, 2);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1893_ = v_x_1888_;
v_isShared_1894_ = v_isSharedCheck_1914_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_tail_1891_);
lean_inc(v_value_1890_);
lean_inc(v_key_1889_);
lean_dec(v_x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1914_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; uint64_t v___x_1898_; uint64_t v_fold_1899_; uint64_t v___x_1900_; uint64_t v___x_1901_; uint64_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1895_ = lean_array_get_size(v_x_1887_);
v___x_1896_ = lean_uint64_of_nat(v_key_1889_);
v___x_1897_ = 32ULL;
v___x_1898_ = lean_uint64_shift_right(v___x_1896_, v___x_1897_);
v_fold_1899_ = lean_uint64_xor(v___x_1896_, v___x_1898_);
v___x_1900_ = 16ULL;
v___x_1901_ = lean_uint64_shift_right(v_fold_1899_, v___x_1900_);
v___x_1902_ = lean_uint64_xor(v_fold_1899_, v___x_1901_);
v___x_1903_ = lean_uint64_to_usize(v___x_1902_);
v___x_1904_ = lean_usize_of_nat(v___x_1895_);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_sub(v___x_1904_, v___x_1905_);
v___x_1907_ = lean_usize_land(v___x_1903_, v___x_1906_);
v___x_1908_ = lean_array_uget_borrowed(v_x_1887_, v___x_1907_);
lean_inc(v___x_1908_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 2, v___x_1908_);
v___x_1910_ = v___x_1893_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_key_1889_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_value_1890_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_array_uset(v_x_1887_, v___x_1907_, v___x_1910_);
v_x_1887_ = v___x_1911_;
v_x_1888_ = v_tail_1891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1915_, lean_object* v_source_1916_, lean_object* v_target_1917_){
_start:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = lean_array_get_size(v_source_1916_);
v___x_1919_ = lean_nat_dec_lt(v_i_1915_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_dec_ref(v_source_1916_);
lean_dec(v_i_1915_);
return v_target_1917_;
}
else
{
lean_object* v_es_1920_; lean_object* v___x_1921_; lean_object* v_source_1922_; lean_object* v_target_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_es_1920_ = lean_array_fget(v_source_1916_, v_i_1915_);
v___x_1921_ = lean_box(0);
v_source_1922_ = lean_array_fset(v_source_1916_, v_i_1915_, v___x_1921_);
v_target_1923_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1917_, v_es_1920_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_add(v_i_1915_, v___x_1924_);
lean_dec(v_i_1915_);
v_i_1915_ = v___x_1925_;
v_source_1916_ = v_source_1922_;
v_target_1917_ = v_target_1923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1927_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v_nbuckets_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1928_ = lean_array_get_size(v_data_1927_);
v___x_1929_ = lean_unsigned_to_nat(2u);
v_nbuckets_1930_ = lean_nat_mul(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_mk_array(v_nbuckets_1930_, v___x_1932_);
v___x_1934_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1931_, v_data_1927_, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1935_, lean_object* v_x_1936_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = 0;
return v___x_1937_;
}
else
{
lean_object* v_key_1938_; lean_object* v_tail_1939_; uint8_t v___x_1940_; 
v_key_1938_ = lean_ctor_get(v_x_1936_, 0);
v_tail_1939_ = lean_ctor_get(v_x_1936_, 2);
v___x_1940_ = lean_nat_dec_eq(v_key_1938_, v_a_1935_);
if (v___x_1940_ == 0)
{
v_x_1936_ = v_tail_1939_;
goto _start;
}
else
{
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1942_, lean_object* v_x_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1942_, v_x_1943_);
lean_dec(v_x_1943_);
lean_dec(v_a_1942_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1946_, lean_object* v_a_1947_, lean_object* v_b_1948_){
_start:
{
lean_object* v_size_1949_; lean_object* v_buckets_1950_; lean_object* v___x_1951_; uint64_t v___x_1952_; uint64_t v___x_1953_; uint64_t v___x_1954_; uint64_t v_fold_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; uint64_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; lean_object* v_bkt_1964_; uint8_t v___x_1965_; 
v_size_1949_ = lean_ctor_get(v_m_1946_, 0);
v_buckets_1950_ = lean_ctor_get(v_m_1946_, 1);
v___x_1951_ = lean_array_get_size(v_buckets_1950_);
v___x_1952_ = lean_uint64_of_nat(v_a_1947_);
v___x_1953_ = 32ULL;
v___x_1954_ = lean_uint64_shift_right(v___x_1952_, v___x_1953_);
v_fold_1955_ = lean_uint64_xor(v___x_1952_, v___x_1954_);
v___x_1956_ = 16ULL;
v___x_1957_ = lean_uint64_shift_right(v_fold_1955_, v___x_1956_);
v___x_1958_ = lean_uint64_xor(v_fold_1955_, v___x_1957_);
v___x_1959_ = lean_uint64_to_usize(v___x_1958_);
v___x_1960_ = lean_usize_of_nat(v___x_1951_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_sub(v___x_1960_, v___x_1961_);
v___x_1963_ = lean_usize_land(v___x_1959_, v___x_1962_);
v_bkt_1964_ = lean_array_uget_borrowed(v_buckets_1950_, v___x_1963_);
v___x_1965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1947_, v_bkt_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1986_; 
lean_inc_ref(v_buckets_1950_);
lean_inc(v_size_1949_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_m_1946_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_m_1946_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_m_1946_, 0);
lean_dec(v_unused_1988_);
v___x_1967_ = v_m_1946_;
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_m_1946_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v_size_x27_1970_; lean_object* v___x_1971_; lean_object* v_buckets_x27_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v_size_x27_1970_ = lean_nat_add(v_size_1949_, v___x_1969_);
lean_dec(v_size_1949_);
lean_inc(v_bkt_1964_);
v___x_1971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1971_, 0, v_a_1947_);
lean_ctor_set(v___x_1971_, 1, v_b_1948_);
lean_ctor_set(v___x_1971_, 2, v_bkt_1964_);
v_buckets_x27_1972_ = lean_array_uset(v_buckets_1950_, v___x_1963_, v___x_1971_);
v___x_1973_ = lean_unsigned_to_nat(4u);
v___x_1974_ = lean_nat_mul(v_size_x27_1970_, v___x_1973_);
v___x_1975_ = lean_unsigned_to_nat(3u);
v___x_1976_ = lean_nat_div(v___x_1974_, v___x_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_array_get_size(v_buckets_x27_1972_);
v___x_1978_ = lean_nat_dec_le(v___x_1976_, v___x_1977_);
lean_dec(v___x_1976_);
if (v___x_1978_ == 0)
{
lean_object* v_val_1979_; lean_object* v___x_1981_; 
v_val_1979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1972_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_val_1979_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1970_);
v___x_1981_ = v___x_1967_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_size_x27_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_val_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v___x_1984_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_buckets_x27_1972_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1970_);
v___x_1984_ = v___x_1967_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_size_x27_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_buckets_x27_1972_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_dec(v_b_1948_);
lean_dec(v_a_1947_);
return v_m_1946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_b_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1993_ == 0)
{
return v_b_1992_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; 
v_a_1994_ = lean_array_uget_borrowed(v_as_1989_, v_i_1991_);
v___x_1995_ = lean_box(0);
lean_inc(v_a_1994_);
v___x_1996_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1992_, v_a_1994_, v___x_1995_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1991_, v___x_1997_);
v_i_1991_ = v___x_1998_;
v_b_1992_ = v___x_1996_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_2000_, lean_object* v_sz_2001_, lean_object* v_i_2002_, lean_object* v_b_2003_){
_start:
{
size_t v_sz_boxed_2004_; size_t v_i_boxed_2005_; lean_object* v_res_2006_; 
v_sz_boxed_2004_ = lean_unbox_usize(v_sz_2001_);
lean_dec(v_sz_2001_);
v_i_boxed_2005_ = lean_unbox_usize(v_i_2002_);
lean_dec(v_i_2002_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_2000_, v_sz_boxed_2004_, v_i_boxed_2005_, v_b_2003_);
lean_dec_ref(v_as_2000_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2011_ == 0)
{
return v_b_2010_;
}
else
{
lean_object* v_a_2012_; lean_object* v_indicesPos_2013_; size_t v_sz_2014_; size_t v___x_2015_; lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v_a_2012_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
v_indicesPos_2013_ = lean_ctor_get(v_a_2012_, 3);
v_sz_2014_ = lean_array_size(v_indicesPos_2013_);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2013_, v_sz_2014_, v___x_2015_, v_b_2010_);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2009_, v___x_2017_);
v_i_2009_ = v___x_2018_;
v_b_2010_ = v___x_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_){
_start:
{
size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2020_, v_sz_boxed_2024_, v_i_boxed_2025_, v_b_2023_);
lean_dec_ref(v_as_2020_);
return v_res_2026_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_buckets_2029_; lean_object* v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; uint64_t v___x_2033_; uint64_t v_fold_2034_; uint64_t v___x_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_buckets_2029_ = lean_ctor_get(v_m_2027_, 1);
v___x_2030_ = lean_array_get_size(v_buckets_2029_);
v___x_2031_ = lean_uint64_of_nat(v_a_2028_);
v___x_2032_ = 32ULL;
v___x_2033_ = lean_uint64_shift_right(v___x_2031_, v___x_2032_);
v_fold_2034_ = lean_uint64_xor(v___x_2031_, v___x_2033_);
v___x_2035_ = 16ULL;
v___x_2036_ = lean_uint64_shift_right(v_fold_2034_, v___x_2035_);
v___x_2037_ = lean_uint64_xor(v_fold_2034_, v___x_2036_);
v___x_2038_ = lean_uint64_to_usize(v___x_2037_);
v___x_2039_ = lean_usize_of_nat(v___x_2030_);
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_sub(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_usize_land(v___x_2038_, v___x_2041_);
v___x_2043_ = lean_array_uget_borrowed(v_buckets_2029_, v___x_2042_);
v___x_2044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2028_, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2045_, lean_object* v_a_2046_){
_start:
{
uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_res_2047_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_m_2045_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2049_, lean_object* v_as_2050_, size_t v_sz_2051_, size_t v_i_2052_, lean_object* v_b_2053_){
_start:
{
lean_object* v_a_2055_; uint8_t v___x_2059_; 
v___x_2059_ = lean_usize_dec_lt(v_i_2052_, v_sz_2051_);
if (v___x_2059_ == 0)
{
return v_b_2053_;
}
else
{
lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2076_; 
v_fst_2060_ = lean_ctor_get(v_b_2053_, 0);
v_snd_2061_ = lean_ctor_get(v_b_2053_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_b_2053_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2063_ = v_b_2053_;
v_isShared_2064_ = v_isSharedCheck_2076_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_snd_2061_);
lean_inc(v_fst_2060_);
lean_dec(v_b_2053_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2076_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_a_2065_; lean_object* v_recArgPos_2066_; uint8_t v___x_2067_; 
v_a_2065_ = lean_array_uget_borrowed(v_as_2050_, v_i_2052_);
v_recArgPos_2066_ = lean_ctor_get(v_a_2065_, 2);
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2049_, v_recArgPos_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_inc(v_a_2065_);
v___x_2068_ = lean_array_push(v_snd_2061_, v_a_2065_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2068_);
v___x_2070_ = v___x_2063_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_fst_2060_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v_a_2055_ = v___x_2070_;
goto v___jp_2054_;
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_inc(v_a_2065_);
v___x_2072_ = lean_array_push(v_fst_2060_, v_a_2065_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2072_);
v___x_2074_ = v___x_2063_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_snd_2061_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v_a_2055_ = v___x_2074_;
goto v___jp_2054_;
}
}
}
}
v___jp_2054_:
{
size_t v___x_2056_; size_t v___x_2057_; 
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2052_, v___x_2056_);
v_i_2052_ = v___x_2057_;
v_b_2053_ = v_a_2055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2077_, lean_object* v_as_2078_, lean_object* v_sz_2079_, lean_object* v_i_2080_, lean_object* v_b_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2079_);
lean_dec(v_sz_2079_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2077_, v_as_2078_, v_sz_boxed_2082_, v_i_boxed_2083_, v_b_2081_);
lean_dec_ref(v_as_2078_);
lean_dec_ref(v___x_2077_);
return v_res_2084_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_unsigned_to_nat(16u);
v___x_2087_ = lean_mk_array(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_indicesPos_2090_; 
v___x_2088_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2089_ = lean_unsigned_to_nat(0u);
v_indicesPos_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2090_, 0, v___x_2089_);
lean_ctor_set(v_indicesPos_2090_, 1, v___x_2088_);
return v_indicesPos_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2093_){
_start:
{
lean_object* v_indicesPos_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___x_2102_; 
v_indicesPos_2094_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2095_ = lean_array_size(v_recArgInfos_2093_);
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2093_, v_sz_2095_, v___x_2096_, v_indicesPos_2094_);
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2097_, v_recArgInfos_2093_, v_sz_2095_, v___x_2096_, v___x_2098_);
lean_dec_ref(v___x_2097_);
v_fst_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_fst_2100_);
v_snd_2101_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_snd_2101_);
lean_dec_ref(v___x_2099_);
v___x_2102_ = l_Array_append___redArg(v_snd_2101_, v_fst_2100_);
lean_dec(v_fst_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2103_);
lean_dec_ref(v_recArgInfos_2103_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2105_, lean_object* v_m_2106_, lean_object* v_a_2107_, lean_object* v_b_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2106_, v_a_2107_, v_b_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2110_, lean_object* v_m_2111_, lean_object* v_a_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2111_, v_a_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2114_, lean_object* v_m_2115_, lean_object* v_a_2116_){
_start:
{
uint8_t v_res_2117_; lean_object* v_r_2118_; 
v_res_2117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2114_, v_m_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_m_2115_);
v_r_2118_ = lean_box(v_res_2117_);
return v_r_2118_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2119_, lean_object* v_a_2120_, lean_object* v_x_2121_){
_start:
{
uint8_t v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2120_, v_x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_a_2124_, lean_object* v_x_2125_){
_start:
{
uint8_t v_res_2126_; lean_object* v_r_2127_; 
v_res_2126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2123_, v_a_2124_, v_x_2125_);
lean_dec(v_x_2125_);
lean_dec(v_a_2124_);
v_r_2127_ = lean_box(v_res_2126_);
return v_r_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2128_, lean_object* v_data_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2131_, lean_object* v_i_2132_, lean_object* v_source_2133_, lean_object* v_target_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2132_, v_source_2133_, v_target_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2137_, v_x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2140_, lean_object* v_a_2141_, lean_object* v_toPure_2142_, uint8_t v_____do__lift_2143_){
_start:
{
if (v_____do__lift_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_array_push(v___y_2140_, v_a_2141_);
v___x_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
v___x_2146_ = lean_apply_2(v_toPure_2142_, lean_box(0), v___x_2145_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_a_2141_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___y_2140_);
v___x_2148_ = lean_apply_2(v_toPure_2142_, lean_box(0), v___x_2147_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2149_, lean_object* v_a_2150_, lean_object* v_toPure_2151_, lean_object* v_____do__lift_2152_){
_start:
{
uint8_t v_____do__lift_192__boxed_2153_; lean_object* v_res_2154_; 
v_____do__lift_192__boxed_2153_ = lean_unbox(v_____do__lift_2152_);
v_res_2154_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2149_, v_a_2150_, v_toPure_2151_, v_____do__lift_192__boxed_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2155_, lean_object* v_a_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_apply_2(v_eq_2155_, v_x_2157_, v_a_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2159_, lean_object* v___x_2160_, lean_object* v_toBind_2161_, lean_object* v_eq_2162_, lean_object* v_inst_2163_, lean_object* v_a_2164_, lean_object* v_x_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___f_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
lean_inc(v_toPure_2159_);
lean_inc(v_a_2164_);
lean_inc_ref(v___y_2166_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2167_, 0, v___y_2166_);
lean_closure_set(v___f_2167_, 1, v_a_2164_);
lean_closure_set(v___f_2167_, 2, v_toPure_2159_);
v___x_2168_ = lean_array_get_size(v___y_2166_);
v___x_2169_ = lean_nat_dec_lt(v___x_2160_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v___y_2166_);
lean_dec(v_a_2164_);
lean_dec_ref(v_inst_2163_);
lean_dec(v_eq_2162_);
v___x_2170_ = lean_box(v___x_2169_);
v___x_2171_ = lean_apply_2(v_toPure_2159_, lean_box(0), v___x_2170_);
v___x_2172_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2171_, v___f_2167_);
return v___x_2172_;
}
else
{
if (v___x_2169_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v___y_2166_);
lean_dec(v_a_2164_);
lean_dec_ref(v_inst_2163_);
lean_dec(v_eq_2162_);
v___x_2173_ = lean_box(v___x_2169_);
v___x_2174_ = lean_apply_2(v_toPure_2159_, lean_box(0), v___x_2173_);
v___x_2175_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2174_, v___f_2167_);
return v___x_2175_;
}
else
{
lean_object* v___f_2176_; size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v_toPure_2159_);
v___f_2176_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2176_, 0, v_eq_2162_);
lean_closure_set(v___f_2176_, 1, v_a_2164_);
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = lean_usize_of_nat(v___x_2168_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2163_, v___f_2176_, v___y_2166_, v___x_2177_, v___x_2178_);
v___x_2180_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2179_, v___f_2167_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2181_, lean_object* v___x_2182_, lean_object* v_toBind_2183_, lean_object* v_eq_2184_, lean_object* v_inst_2185_, lean_object* v_a_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2181_, v___x_2182_, v_toBind_2183_, v_eq_2184_, v_inst_2185_, v_a_2186_, v_x_2187_, v___y_2188_);
lean_dec(v___x_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2190_, lean_object* v_____s_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_apply_2(v_toPure_2190_, lean_box(0), v_____s_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2195_, lean_object* v_eq_2196_, lean_object* v_xs_2197_){
_start:
{
lean_object* v_toApplicative_2198_; lean_object* v_toBind_2199_; lean_object* v_toPure_2200_; lean_object* v___x_2201_; lean_object* v_ret_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; size_t v_sz_2205_; size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_toApplicative_2198_ = lean_ctor_get(v_inst_2195_, 0);
v_toBind_2199_ = lean_ctor_get(v_inst_2195_, 1);
lean_inc_n(v_toBind_2199_, 2);
v_toPure_2200_ = lean_ctor_get(v_toApplicative_2198_, 1);
v___x_2201_ = lean_unsigned_to_nat(0u);
v_ret_2202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2195_);
lean_inc_n(v_toPure_2200_, 2);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2203_, 0, v_toPure_2200_);
lean_closure_set(v___f_2203_, 1, v___x_2201_);
lean_closure_set(v___f_2203_, 2, v_toBind_2199_);
lean_closure_set(v___f_2203_, 3, v_eq_2196_);
lean_closure_set(v___f_2203_, 4, v_inst_2195_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2204_, 0, v_toPure_2200_);
v_sz_2205_ = lean_array_size(v_xs_2197_);
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2195_, v_xs_2197_, v___f_2203_, v_sz_2205_, v___x_2206_, v_ret_2202_);
v___x_2208_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2207_, v___f_2204_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2209_, lean_object* v_00_u03b1_2210_, lean_object* v_inst_2211_, lean_object* v_eq_2212_, lean_object* v_xs_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2211_, v_eq_2212_, v_xs_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2215_, size_t v_i_2216_, lean_object* v_bs_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_usize_dec_lt(v_i_2216_, v_sz_2215_);
if (v___x_2218_ == 0)
{
return v_bs_2217_;
}
else
{
lean_object* v_v_2219_; lean_object* v_indGroupInst_2220_; lean_object* v___x_2221_; lean_object* v_bs_x27_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v_v_2219_ = lean_array_uget_borrowed(v_bs_2217_, v_i_2216_);
v_indGroupInst_2220_ = lean_ctor_get(v_v_2219_, 4);
lean_inc_ref(v_indGroupInst_2220_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v_bs_x27_2222_ = lean_array_uset(v_bs_2217_, v_i_2216_, v___x_2221_);
v___x_2223_ = ((size_t)1ULL);
v___x_2224_ = lean_usize_add(v_i_2216_, v___x_2223_);
v___x_2225_ = lean_array_uset(v_bs_x27_2222_, v_i_2216_, v_indGroupInst_2220_);
v_i_2216_ = v___x_2224_;
v_bs_2217_ = v___x_2225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_bs_2229_){
_start:
{
size_t v_sz_boxed_2230_; size_t v_i_boxed_2231_; lean_object* v_res_2232_; 
v_sz_boxed_2230_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2231_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2230_, v_i_boxed_2231_, v_bs_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2233_, lean_object* v_a_2234_, lean_object* v_as_2235_, size_t v_i_2236_, size_t v_stop_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_usize_dec_eq(v_i_2236_, v_stop_2237_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_array_uget_borrowed(v_as_2235_, v_i_2236_);
lean_inc_ref(v_eq_2233_);
lean_inc(v___y_2241_);
lean_inc_ref(v___y_2240_);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
lean_inc(v_a_2234_);
lean_inc(v___x_2244_);
v___x_2245_ = lean_apply_7(v_eq_2233_, v___x_2244_, v_a_2234_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, lean_box(0));
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2257_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2257_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2257_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_unbox(v_a_2246_);
if (v___x_2250_ == 0)
{
size_t v___x_2251_; size_t v___x_2252_; 
lean_del_object(v___x_2248_);
lean_dec(v_a_2246_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_add(v_i_2236_, v___x_2251_);
v_i_2236_ = v___x_2252_;
goto _start;
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_eq_2233_);
if (v_isShared_2249_ == 0)
{
v___x_2255_ = v___x_2248_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2246_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_dec(v_a_2234_);
lean_dec_ref(v_eq_2233_);
return v___x_2245_;
}
}
else
{
uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_eq_2233_);
v___x_2258_ = 0;
v___x_2259_ = lean_box(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2261_, lean_object* v_a_2262_, lean_object* v_as_2263_, lean_object* v_i_2264_, lean_object* v_stop_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
size_t v_i_boxed_2271_; size_t v_stop_boxed_2272_; lean_object* v_res_2273_; 
v_i_boxed_2271_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_stop_boxed_2272_ = lean_unbox_usize(v_stop_2265_);
lean_dec(v_stop_2265_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2261_, v_a_2262_, v_as_2263_, v_i_boxed_2271_, v_stop_boxed_2272_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_as_2263_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2274_, lean_object* v_a_2275_, uint8_t v_____do__lift_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
if (v_____do__lift_2276_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_array_push(v_b_2274_, v_a_2275_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec(v_a_2275_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_b_2274_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2287_, lean_object* v_a_2288_, lean_object* v_____do__lift_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v_____do__lift_1292__boxed_2295_; lean_object* v_res_2296_; 
v_____do__lift_1292__boxed_2295_ = lean_unbox(v_____do__lift_2289_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2287_, v_a_2288_, v_____do__lift_1292__boxed_2295_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2297_, lean_object* v_as_2298_, size_t v_sz_2299_, size_t v_i_2300_, lean_object* v_b_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_a_2308_; lean_object* v___y_2313_; uint8_t v___x_2332_; 
v___x_2332_ = lean_usize_dec_lt(v_i_2300_, v_sz_2299_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec_ref(v_eq_2297_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_b_2301_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; lean_object* v_a_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2334_ = lean_unsigned_to_nat(0u);
v_a_2335_ = lean_array_uget_borrowed(v_as_2298_, v_i_2300_);
v___x_2336_ = lean_array_get_size(v_b_2301_);
v___x_2337_ = lean_nat_dec_lt(v___x_2334_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_inc(v_a_2335_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2301_, v_a_2335_, v___x_2337_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
v___y_2313_ = v___x_2338_;
goto v___jp_2312_;
}
else
{
if (v___x_2337_ == 0)
{
lean_object* v___x_2339_; 
lean_inc(v_a_2335_);
v___x_2339_ = lean_array_push(v_b_2301_, v_a_2335_);
v_a_2308_ = v___x_2339_;
goto v___jp_2307_;
}
else
{
size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = lean_usize_of_nat(v___x_2336_);
lean_inc(v_a_2335_);
lean_inc_ref(v_eq_2297_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2297_, v_a_2335_, v_b_2301_, v___x_2340_, v___x_2341_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
lean_inc(v_a_2335_);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2301_, v_a_2335_, v___x_2344_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
v___y_2313_ = v___x_2345_;
goto v___jp_2312_;
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_b_2301_);
lean_dec_ref(v_eq_2297_);
v_a_2346_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2342_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2342_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
v___jp_2307_:
{
size_t v___x_2309_; size_t v___x_2310_; 
v___x_2309_ = ((size_t)1ULL);
v___x_2310_ = lean_usize_add(v_i_2300_, v___x_2309_);
v_i_2300_ = v___x_2310_;
v_b_2301_ = v_a_2308_;
goto _start;
}
v___jp_2312_:
{
if (lean_obj_tag(v___y_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v_a_2314_ = lean_ctor_get(v___y_2313_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___y_2313_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2316_ = v___y_2313_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___y_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; 
lean_dec_ref(v_eq_2297_);
v_a_2318_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v_a_2314_, 1);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_a_2318_);
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
else
{
lean_object* v_a_2322_; 
lean_del_object(v___x_2316_);
v_a_2322_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v_a_2314_, 1);
v_a_2308_ = v_a_2322_;
goto v___jp_2307_;
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_eq_2297_);
v_a_2324_ = lean_ctor_get(v___y_2313_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___y_2313_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___y_2313_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___y_2313_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
size_t v_sz_boxed_2364_; size_t v_i_boxed_2365_; lean_object* v_res_2366_; 
v_sz_boxed_2364_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2365_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2354_, v_as_2355_, v_sz_boxed_2364_, v_i_boxed_2365_, v_b_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_as_2355_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2367_, lean_object* v_xs_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_ret_2374_; size_t v_sz_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v_ret_2374_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2375_ = lean_array_size(v_xs_2368_);
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2367_, v_xs_2368_, v_sz_2375_, v___x_2376_, v_ret_2374_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2378_, lean_object* v_xs_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2378_, v_xs_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v_xs_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2393_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2394_ = lean_array_size(v_recArgInfos_2387_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2394_, v___x_2395_, v_recArgInfos_2387_);
v___x_2397_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2393_, v___x_2396_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec_ref(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2405_, lean_object* v_eq_2406_, lean_object* v_xs_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2406_, v_xs_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_eq_2415_, lean_object* v_xs_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2414_, v_eq_2415_, v_xs_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_xs_2416_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2423_, lean_object* v_eq_2424_, lean_object* v_a_2425_, lean_object* v_as_2426_, size_t v_i_2427_, size_t v_stop_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2424_, v_a_2425_, v_as_2426_, v_i_2427_, v_stop_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_eq_2436_, lean_object* v_a_2437_, lean_object* v_as_2438_, lean_object* v_i_2439_, lean_object* v_stop_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
size_t v_i_boxed_2446_; size_t v_stop_boxed_2447_; lean_object* v_res_2448_; 
v_i_boxed_2446_ = lean_unbox_usize(v_i_2439_);
lean_dec(v_i_2439_);
v_stop_boxed_2447_ = lean_unbox_usize(v_stop_2440_);
lean_dec(v_stop_2440_);
v_res_2448_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2435_, v_eq_2436_, v_a_2437_, v_as_2438_, v_i_boxed_2446_, v_stop_boxed_2447_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v_as_2438_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2449_, lean_object* v_eq_2450_, lean_object* v_as_2451_, size_t v_sz_2452_, size_t v_i_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2450_, v_as_2451_, v_sz_2452_, v_i_2453_, v_b_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_eq_2462_, lean_object* v_as_2463_, lean_object* v_sz_2464_, lean_object* v_i_2465_, lean_object* v_b_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
size_t v_sz_boxed_2472_; size_t v_i_boxed_2473_; lean_object* v_res_2474_; 
v_sz_boxed_2472_ = lean_unbox_usize(v_sz_2464_);
lean_dec(v_sz_2464_);
v_i_boxed_2473_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2461_, v_eq_2462_, v_as_2463_, v_sz_boxed_2472_, v_i_boxed_2473_, v_b_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v_as_2463_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2475_, lean_object* v___y_2476_){
_start:
{
uint8_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = l_Lean_Expr_hasMVar(v_e_2475_);
v___x_2479_ = lean_bool_not(v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v_mctx_2481_; lean_object* v___x_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; lean_object* v_cache_2486_; lean_object* v_zetaDeltaFVarIds_2487_; lean_object* v_postponed_2488_; lean_object* v_diag_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2498_; 
v___x_2480_ = lean_st_ref_get(v___y_2476_);
v_mctx_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc_ref(v_mctx_2481_);
lean_dec(v___x_2480_);
v___x_2482_ = l_Lean_instantiateMVarsCore(v_mctx_2481_, v_e_2475_);
v_fst_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v___x_2482_);
v___x_2485_ = lean_st_ref_take(v___y_2476_);
v_cache_2486_ = lean_ctor_get(v___x_2485_, 1);
v_zetaDeltaFVarIds_2487_ = lean_ctor_get(v___x_2485_, 2);
v_postponed_2488_ = lean_ctor_get(v___x_2485_, 3);
v_diag_2489_ = lean_ctor_get(v___x_2485_, 4);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2485_, 0);
lean_dec(v_unused_2499_);
v___x_2491_ = v___x_2485_;
v_isShared_2492_ = v_isSharedCheck_2498_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_diag_2489_);
lean_inc(v_postponed_2488_);
lean_inc(v_zetaDeltaFVarIds_2487_);
lean_inc(v_cache_2486_);
lean_dec(v___x_2485_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2498_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_snd_2484_);
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_snd_2484_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_cache_2486_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_zetaDeltaFVarIds_2487_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_postponed_2488_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_diag_2489_);
v___x_2494_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_st_ref_set(v___y_2476_, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_fst_2483_);
return v___x_2496_;
}
}
}
else
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_e_2475_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2501_, v___y_2502_);
lean_dec(v___y_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2505_, v___y_2507_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2518_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2521_ = lean_unsigned_to_nat(109u);
v___x_2522_ = lean_unsigned_to_nat(216u);
v___x_2523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2525_ = l_mkPanicMessageWithDecl(v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_, v___x_2520_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_bs_2529_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2530_ == 0)
{
return v_bs_2529_;
}
else
{
lean_object* v_v_2531_; lean_object* v___x_2532_; lean_object* v_bs_x27_2533_; lean_object* v___y_2535_; lean_object* v___x_2540_; 
v_v_2531_ = lean_array_uget(v_bs_2529_, v_i_2528_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v_bs_x27_2533_ = lean_array_uset(v_bs_2529_, v_i_2528_, v___x_2532_);
v___x_2540_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2526_, v_v_2531_);
lean_dec(v_v_2531_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2542_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2541_);
v___y_2535_ = v___x_2542_;
goto v___jp_2534_;
}
else
{
lean_object* v_val_2543_; 
v_val_2543_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v___x_2540_, 1);
v___y_2535_ = v_val_2543_;
goto v___jp_2534_;
}
v___jp_2534_:
{
size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2528_, v___x_2536_);
v___x_2538_ = lean_array_uset(v_bs_x27_2533_, v_i_2528_, v___y_2535_);
v_i_2528_ = v___x_2537_;
v_bs_2529_ = v___x_2538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2544_, lean_object* v_sz_2545_, lean_object* v_i_2546_, lean_object* v_bs_2547_){
_start:
{
size_t v_sz_boxed_2548_; size_t v_i_boxed_2549_; lean_object* v_res_2550_; 
v_sz_boxed_2548_ = lean_unbox_usize(v_sz_2545_);
lean_dec(v_sz_2545_);
v_i_boxed_2549_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2544_, v_sz_boxed_2548_, v_i_boxed_2549_, v_bs_2547_);
lean_dec_ref(v___x_2544_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2551_, size_t v_i_2552_, lean_object* v_bs_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_lt(v_i_2552_, v_sz_2551_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_bs_2553_);
return v___x_2560_;
}
else
{
lean_object* v_v_2561_; lean_object* v___x_2562_; 
v_v_2561_ = lean_array_uget_borrowed(v_bs_2553_, v_i_2552_);
lean_inc(v_v_2561_);
v___x_2562_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2561_, v___y_2555_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v_bs_x27_2565_; size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = lean_unsigned_to_nat(0u);
v_bs_x27_2565_ = lean_array_uset(v_bs_2553_, v_i_2552_, v___x_2564_);
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_add(v_i_2552_, v___x_2566_);
v___x_2568_ = lean_array_uset(v_bs_x27_2565_, v_i_2552_, v_a_2563_);
v_i_2552_ = v___x_2567_;
v_bs_2553_ = v___x_2568_;
goto _start;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_bs_2553_);
v_a_2570_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2562_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2562_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2578_, lean_object* v_i_2579_, lean_object* v_bs_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2578_);
lean_dec(v_sz_2578_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2586_, v_i_boxed_2587_, v_bs_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3(lean_object* v___x_2589_, lean_object* v_ys_2590_, lean_object* v___x_2591_, lean_object* v_recArgInfo_2592_, lean_object* v___x_2593_, lean_object* v___x_2594_, lean_object* v_group_2595_, lean_object* v___x_2596_, lean_object* v_as_2597_, size_t v_sz_2598_, size_t v_i_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_a_2607_; uint8_t v___x_2611_; 
v___x_2611_ = lean_usize_dec_lt(v_i_2599_, v_sz_2598_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_b_2600_);
return v___x_2612_;
}
else
{
lean_object* v_snd_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2771_; 
v_snd_2613_ = lean_ctor_get(v_b_2600_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_b_2600_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v_b_2600_, 0);
lean_dec(v_unused_2772_);
v___x_2615_ = v_b_2600_;
v_isShared_2616_ = v_isSharedCheck_2771_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_snd_2613_);
lean_dec(v_b_2600_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2771_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v_next_2617_; lean_object* v_upperBound_2618_; lean_object* v___x_2619_; 
v_next_2617_ = lean_ctor_get(v_snd_2613_, 0);
lean_inc(v_next_2617_);
v_upperBound_2618_ = lean_ctor_get(v_snd_2613_, 1);
v___x_2619_ = lean_box(0);
if (lean_obj_tag(v_next_2617_) == 0)
{
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
goto v___jp_2620_;
}
else
{
lean_object* v_val_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2770_; 
v_val_2625_ = lean_ctor_get(v_next_2617_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_next_2617_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2627_ = v_next_2617_;
v_isShared_2628_ = v_isSharedCheck_2770_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_val_2625_);
lean_dec(v_next_2617_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2770_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_nat_dec_lt(v_val_2625_, v_upperBound_2618_);
if (v___x_2629_ == 0)
{
lean_del_object(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
goto v___jp_2620_;
}
else
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2767_; 
lean_inc(v_upperBound_2618_);
lean_del_object(v___x_2615_);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_snd_2613_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; lean_object* v_unused_2769_; 
v_unused_2768_ = lean_ctor_get(v_snd_2613_, 1);
lean_dec(v_unused_2768_);
v_unused_2769_ = lean_ctor_get(v_snd_2613_, 0);
lean_dec(v_unused_2769_);
v___x_2631_ = v_snd_2613_;
v_isShared_2632_ = v_isSharedCheck_2767_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_snd_2613_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2767_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; 
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc_ref(v___x_2589_);
v___x_2633_ = lean_infer_type(v___x_2589_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = l_Lean_Meta_whnfD(v_a_2634_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v_a_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v_a_2637_ = lean_array_uget_borrowed(v_as_2597_, v_i_2599_);
v___x_2638_ = 0;
lean_inc(v_a_2637_);
v___x_2639_ = l_Lean_Meta_forallMetaTelescope(v_a_2637_, v___x_2638_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_snd_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2741_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_snd_2641_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2641_);
v_fst_2642_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_fst_2642_);
lean_dec(v_a_2640_);
v_snd_2643_ = lean_ctor_get(v_snd_2641_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_snd_2641_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_snd_2641_, 0);
lean_dec(v_unused_2742_);
v___x_2645_ = v_snd_2641_;
v_isShared_2646_ = v_isSharedCheck_2741_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_snd_2643_);
lean_dec(v_snd_2641_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2741_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2643_, v_a_2636_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_val_2625_, v___x_2649_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2650_);
v___x_2652_ = v___x_2627_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2652_);
v___x_2654_ = v___x_2631_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_upperBound_2618_);
v___x_2654_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_unbox(v_a_2648_);
lean_dec(v_a_2648_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2657_; 
lean_dec(v_fst_2642_);
lean_dec(v_val_2625_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2654_);
lean_ctor_set(v___x_2645_, 0, v___x_2619_);
v___x_2657_ = v___x_2645_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2654_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
v_a_2607_ = v___x_2657_;
goto v___jp_2606_;
}
}
else
{
size_t v_sz_2659_; size_t v___x_2660_; lean_object* v___x_2661_; 
v_sz_2659_ = lean_array_size(v_fst_2642_);
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2659_, v___x_2660_, v_fst_2642_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___y_2664_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = lean_nat_dec_eq(v___x_2596_, v___x_2714_);
v___x_2716_ = lean_array_get_size(v_a_2662_);
v___x_2717_ = lean_nat_dec_lt(v___x_2714_, v___x_2716_);
if (v___x_2717_ == 0)
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_bool_not(v___x_2715_);
v___y_2664_ = v___x_2718_;
goto v___jp_2663_;
}
else
{
if (v___x_2717_ == 0)
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_bool_not(v___x_2715_);
v___y_2664_ = v___x_2719_;
goto v___jp_2663_;
}
else
{
size_t v___x_2720_; uint8_t v___x_2721_; uint8_t v___x_2722_; 
v___x_2720_ = lean_usize_of_nat(v___x_2716_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_a_2662_, v___x_2660_, v___x_2720_);
v___x_2722_ = lean_bool_not(v___x_2721_);
v___y_2664_ = v___x_2722_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
uint8_t v___x_2665_; 
v___x_2665_ = lean_bool_not(v___y_2664_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2662_);
v___x_2667_ = lean_bool_not(v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2590_, v_a_2662_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2699_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2699_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2699_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
if (lean_obj_tag(v_a_2669_) == 1)
{
lean_object* v___x_2674_; 
lean_dec_ref_known(v_a_2669_, 1);
lean_del_object(v___x_2671_);
lean_dec(v_a_2662_);
lean_dec(v_val_2625_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2654_);
lean_ctor_set(v___x_2645_, 0, v___x_2619_);
v___x_2674_ = v___x_2645_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2654_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v_a_2607_ = v___x_2674_;
goto v___jp_2606_;
}
}
else
{
lean_object* v_fnName_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2669_);
lean_dec_ref(v___x_2589_);
v_fnName_2676_ = lean_ctor_get(v_recArgInfo_2592_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_recArgInfo_2592_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; lean_object* v_unused_2695_; lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; 
v_unused_2694_ = lean_ctor_get(v_recArgInfo_2592_, 5);
lean_dec(v_unused_2694_);
v_unused_2695_ = lean_ctor_get(v_recArgInfo_2592_, 4);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_recArgInfo_2592_, 3);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_recArgInfo_2592_, 2);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_recArgInfo_2592_, 1);
lean_dec(v_unused_2698_);
v___x_2678_ = v_recArgInfo_2592_;
v_isShared_2679_ = v_isSharedCheck_2693_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_fnName_2676_);
lean_dec(v_recArgInfo_2592_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2693_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
size_t v_sz_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v_sz_2680_ = lean_array_size(v_a_2662_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2591_, v_sz_2680_, v___x_2660_, v_a_2662_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 5, v_val_2625_);
lean_ctor_set(v___x_2678_, 4, v_group_2595_);
lean_ctor_set(v___x_2678_, 3, v___x_2681_);
lean_ctor_set(v___x_2678_, 2, v___x_2594_);
lean_ctor_set(v___x_2678_, 1, v___x_2593_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fnName_2676_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_group_2595_);
lean_ctor_set(v_reuseFailAlloc_2692_, 5, v_val_2625_);
v___x_2683_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2654_);
lean_ctor_set(v___x_2645_, 0, v___x_2685_);
v___x_2687_ = v___x_2645_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2654_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2687_);
v___x_2689_ = v___x_2671_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2662_);
lean_dec_ref(v___x_2654_);
lean_del_object(v___x_2645_);
lean_dec(v_val_2625_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2700_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2668_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2668_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_a_2662_);
lean_dec(v_val_2625_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2654_);
lean_ctor_set(v___x_2645_, 0, v___x_2619_);
v___x_2709_ = v___x_2645_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2654_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
v_a_2607_ = v___x_2709_;
goto v___jp_2606_;
}
}
}
else
{
lean_object* v___x_2712_; 
lean_dec(v_a_2662_);
lean_dec(v_val_2625_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2654_);
lean_ctor_set(v___x_2645_, 0, v___x_2619_);
v___x_2712_ = v___x_2645_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2654_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
v_a_2607_ = v___x_2712_;
goto v___jp_2606_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___x_2654_);
lean_del_object(v___x_2645_);
lean_dec(v_val_2625_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2723_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2661_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2661_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_del_object(v___x_2645_);
lean_dec(v_fst_2642_);
lean_del_object(v___x_2631_);
lean_del_object(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec(v_upperBound_2618_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2733_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2647_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2647_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2636_);
lean_del_object(v___x_2631_);
lean_del_object(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec(v_upperBound_2618_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2743_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2639_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2639_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_del_object(v___x_2631_);
lean_del_object(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec(v_upperBound_2618_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2751_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2635_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2635_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_del_object(v___x_2631_);
lean_del_object(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec(v_upperBound_2618_);
lean_dec_ref(v_group_2595_);
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v_recArgInfo_2592_);
lean_dec_ref(v___x_2589_);
v_a_2759_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2633_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2633_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
}
v___jp_2620_:
{
lean_object* v___x_2622_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2619_);
v___x_2622_ = v___x_2615_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2613_);
v___x_2622_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
return v___x_2623_;
}
}
}
}
v___jp_2606_:
{
size_t v___x_2608_; size_t v___x_2609_; 
v___x_2608_ = ((size_t)1ULL);
v___x_2609_ = lean_usize_add(v_i_2599_, v___x_2608_);
v_i_2599_ = v___x_2609_;
v_b_2600_ = v_a_2607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3___boxed(lean_object** _args){
lean_object* v___x_2773_ = _args[0];
lean_object* v_ys_2774_ = _args[1];
lean_object* v___x_2775_ = _args[2];
lean_object* v_recArgInfo_2776_ = _args[3];
lean_object* v___x_2777_ = _args[4];
lean_object* v___x_2778_ = _args[5];
lean_object* v_group_2779_ = _args[6];
lean_object* v___x_2780_ = _args[7];
lean_object* v_as_2781_ = _args[8];
lean_object* v_sz_2782_ = _args[9];
lean_object* v_i_2783_ = _args[10];
lean_object* v_b_2784_ = _args[11];
lean_object* v___y_2785_ = _args[12];
lean_object* v___y_2786_ = _args[13];
lean_object* v___y_2787_ = _args[14];
lean_object* v___y_2788_ = _args[15];
lean_object* v___y_2789_ = _args[16];
_start:
{
size_t v_sz_boxed_2790_; size_t v_i_boxed_2791_; lean_object* v_res_2792_; 
v_sz_boxed_2790_ = lean_unbox_usize(v_sz_2782_);
lean_dec(v_sz_2782_);
v_i_boxed_2791_ = lean_unbox_usize(v_i_2783_);
lean_dec(v_i_2783_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3(v___x_2773_, v_ys_2774_, v___x_2775_, v_recArgInfo_2776_, v___x_2777_, v___x_2778_, v_group_2779_, v___x_2780_, v_as_2781_, v_sz_boxed_2790_, v_i_boxed_2791_, v_b_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec_ref(v_as_2781_);
lean_dec(v___x_2780_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v_ys_2774_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3(lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v_ys_2795_, lean_object* v_recArgInfo_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v_group_2799_, lean_object* v___x_2800_, lean_object* v_as_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_a_2811_; uint8_t v___x_2815_; 
v___x_2815_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_b_2804_);
return v___x_2816_;
}
else
{
lean_object* v_snd_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2975_; 
v_snd_2817_ = lean_ctor_get(v_b_2804_, 1);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_b_2804_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v_b_2804_, 0);
lean_dec(v_unused_2976_);
v___x_2819_ = v_b_2804_;
v_isShared_2820_ = v_isSharedCheck_2975_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_snd_2817_);
lean_dec(v_b_2804_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2975_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_next_2821_; lean_object* v_upperBound_2822_; lean_object* v___x_2823_; 
v_next_2821_ = lean_ctor_get(v_snd_2817_, 0);
lean_inc(v_next_2821_);
v_upperBound_2822_ = lean_ctor_get(v_snd_2817_, 1);
v___x_2823_ = lean_box(0);
if (lean_obj_tag(v_next_2821_) == 0)
{
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
goto v___jp_2824_;
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2974_; 
v_val_2829_ = lean_ctor_get(v_next_2821_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_next_2821_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2831_ = v_next_2821_;
v_isShared_2832_ = v_isSharedCheck_2974_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_val_2829_);
lean_dec(v_next_2821_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2974_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_nat_dec_lt(v_val_2829_, v_upperBound_2822_);
if (v___x_2833_ == 0)
{
lean_del_object(v___x_2831_);
lean_dec(v_val_2829_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
goto v___jp_2824_;
}
else
{
lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2971_; 
lean_inc(v_upperBound_2822_);
lean_del_object(v___x_2819_);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_snd_2817_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; lean_object* v_unused_2973_; 
v_unused_2972_ = lean_ctor_get(v_snd_2817_, 1);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v_snd_2817_, 0);
lean_dec(v_unused_2973_);
v___x_2835_ = v_snd_2817_;
v_isShared_2836_ = v_isSharedCheck_2971_;
goto v_resetjp_2834_;
}
else
{
lean_dec(v_snd_2817_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2971_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; 
lean_inc(v___y_2808_);
lean_inc_ref(v___y_2807_);
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
lean_inc_ref(v___x_2793_);
v___x_2837_ = lean_infer_type(v___x_2793_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = l_Lean_Meta_whnfD(v_a_2838_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v_a_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v_a_2841_ = lean_array_uget_borrowed(v_as_2801_, v_i_2803_);
v___x_2842_ = 0;
lean_inc(v_a_2841_);
v___x_2843_ = l_Lean_Meta_forallMetaTelescope(v_a_2841_, v___x_2842_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_snd_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2945_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_snd_2845_ = lean_ctor_get(v_a_2844_, 1);
lean_inc(v_snd_2845_);
v_fst_2846_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_fst_2846_);
lean_dec(v_a_2844_);
v_snd_2847_ = lean_ctor_get(v_snd_2845_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_snd_2845_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v_snd_2845_, 0);
lean_dec(v_unused_2946_);
v___x_2849_ = v_snd_2845_;
v_isShared_2850_ = v_isSharedCheck_2945_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snd_2847_);
lean_dec(v_snd_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2945_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2847_, v_a_2840_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v___x_2853_ = lean_unsigned_to_nat(1u);
v___x_2854_ = lean_nat_add(v_val_2829_, v___x_2853_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2854_);
v___x_2856_ = v___x_2831_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2856_);
v___x_2858_ = v___x_2835_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_upperBound_2822_);
v___x_2858_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
uint8_t v___x_2859_; 
v___x_2859_ = lean_unbox(v_a_2852_);
lean_dec(v_a_2852_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2861_; 
lean_dec(v_fst_2846_);
lean_dec(v_val_2829_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2858_);
lean_ctor_set(v___x_2849_, 0, v___x_2823_);
v___x_2861_ = v___x_2849_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2858_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
v_a_2811_ = v___x_2861_;
goto v___jp_2810_;
}
}
else
{
size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
v_sz_2863_ = lean_array_size(v_fst_2846_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2863_, v___x_2864_, v_fst_2846_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; uint8_t v___y_2868_; lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = lean_nat_dec_eq(v___x_2800_, v___x_2918_);
v___x_2920_ = lean_array_get_size(v_a_2866_);
v___x_2921_ = lean_nat_dec_lt(v___x_2918_, v___x_2920_);
if (v___x_2921_ == 0)
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_bool_not(v___x_2919_);
v___y_2868_ = v___x_2922_;
goto v___jp_2867_;
}
else
{
if (v___x_2921_ == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_bool_not(v___x_2919_);
v___y_2868_ = v___x_2923_;
goto v___jp_2867_;
}
else
{
size_t v___x_2924_; uint8_t v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = lean_usize_of_nat(v___x_2920_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_a_2866_, v___x_2864_, v___x_2924_);
v___x_2926_ = lean_bool_not(v___x_2925_);
v___y_2868_ = v___x_2926_;
goto v___jp_2867_;
}
}
v___jp_2867_:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_bool_not(v___y_2868_);
if (v___x_2869_ == 0)
{
uint8_t v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2866_);
v___x_2871_ = lean_bool_not(v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2795_, v_a_2866_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2903_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2903_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2903_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
if (lean_obj_tag(v_a_2873_) == 1)
{
lean_object* v___x_2878_; 
lean_dec_ref_known(v_a_2873_, 1);
lean_del_object(v___x_2875_);
lean_dec(v_a_2866_);
lean_dec(v_val_2829_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2858_);
lean_ctor_set(v___x_2849_, 0, v___x_2823_);
v___x_2878_ = v___x_2849_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2858_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v_a_2811_ = v___x_2878_;
goto v___jp_2810_;
}
}
else
{
lean_object* v_fnName_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2873_);
lean_dec_ref(v___x_2793_);
v_fnName_2880_ = lean_ctor_get(v_recArgInfo_2796_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_recArgInfo_2796_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; lean_object* v_unused_2902_; 
v_unused_2898_ = lean_ctor_get(v_recArgInfo_2796_, 5);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_recArgInfo_2796_, 4);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_recArgInfo_2796_, 3);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_recArgInfo_2796_, 2);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_recArgInfo_2796_, 1);
lean_dec(v_unused_2902_);
v___x_2882_ = v_recArgInfo_2796_;
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_fnName_2880_);
lean_dec(v_recArgInfo_2796_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
size_t v_sz_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v_sz_2884_ = lean_array_size(v_a_2866_);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2794_, v_sz_2884_, v___x_2864_, v_a_2866_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 5, v_val_2829_);
lean_ctor_set(v___x_2882_, 4, v_group_2799_);
lean_ctor_set(v___x_2882_, 3, v___x_2885_);
lean_ctor_set(v___x_2882_, 2, v___x_2798_);
lean_ctor_set(v___x_2882_, 1, v___x_2797_);
v___x_2887_ = v___x_2882_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_fnName_2880_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_group_2799_);
lean_ctor_set(v_reuseFailAlloc_2896_, 5, v_val_2829_);
v___x_2887_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2858_);
lean_ctor_set(v___x_2849_, 0, v___x_2889_);
v___x_2891_ = v___x_2849_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2858_);
v___x_2891_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2893_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2891_);
v___x_2893_ = v___x_2875_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2866_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2829_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2904_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2872_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2872_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v___x_2913_; 
lean_dec(v_a_2866_);
lean_dec(v_val_2829_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2858_);
lean_ctor_set(v___x_2849_, 0, v___x_2823_);
v___x_2913_ = v___x_2849_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2858_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
v_a_2811_ = v___x_2913_;
goto v___jp_2810_;
}
}
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_a_2866_);
lean_dec(v_val_2829_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2858_);
lean_ctor_set(v___x_2849_, 0, v___x_2823_);
v___x_2916_ = v___x_2849_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2858_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v_a_2811_ = v___x_2916_;
goto v___jp_2810_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2829_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2927_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2865_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2865_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_del_object(v___x_2849_);
lean_dec(v_fst_2846_);
lean_del_object(v___x_2835_);
lean_del_object(v___x_2831_);
lean_dec(v_val_2829_);
lean_dec(v_upperBound_2822_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2937_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2851_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2851_);
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
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_a_2840_);
lean_del_object(v___x_2835_);
lean_del_object(v___x_2831_);
lean_dec(v_val_2829_);
lean_dec(v_upperBound_2822_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2947_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2843_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2843_);
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
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_del_object(v___x_2835_);
lean_del_object(v___x_2831_);
lean_dec(v_val_2829_);
lean_dec(v_upperBound_2822_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2955_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2839_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2839_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_del_object(v___x_2835_);
lean_del_object(v___x_2831_);
lean_dec(v_val_2829_);
lean_dec(v_upperBound_2822_);
lean_dec_ref(v_group_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_recArgInfo_2796_);
lean_dec_ref(v___x_2793_);
v_a_2963_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2837_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2837_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2826_ = v___x_2819_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2817_);
v___x_2826_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
}
}
v___jp_2810_:
{
size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = ((size_t)1ULL);
v___x_2813_ = lean_usize_add(v_i_2803_, v___x_2812_);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3_spec__3(v___x_2793_, v_ys_2795_, v___x_2794_, v_recArgInfo_2796_, v___x_2797_, v___x_2798_, v_group_2799_, v___x_2800_, v_as_2801_, v_sz_2802_, v___x_2813_, v_a_2811_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object** _args){
lean_object* v___x_2977_ = _args[0];
lean_object* v___x_2978_ = _args[1];
lean_object* v_ys_2979_ = _args[2];
lean_object* v_recArgInfo_2980_ = _args[3];
lean_object* v___x_2981_ = _args[4];
lean_object* v___x_2982_ = _args[5];
lean_object* v_group_2983_ = _args[6];
lean_object* v___x_2984_ = _args[7];
lean_object* v_as_2985_ = _args[8];
lean_object* v_sz_2986_ = _args[9];
lean_object* v_i_2987_ = _args[10];
lean_object* v_b_2988_ = _args[11];
lean_object* v___y_2989_ = _args[12];
lean_object* v___y_2990_ = _args[13];
lean_object* v___y_2991_ = _args[14];
lean_object* v___y_2992_ = _args[15];
lean_object* v___y_2993_ = _args[16];
_start:
{
size_t v_sz_boxed_2994_; size_t v_i_boxed_2995_; lean_object* v_res_2996_; 
v_sz_boxed_2994_ = lean_unbox_usize(v_sz_2986_);
lean_dec(v_sz_2986_);
v_i_boxed_2995_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_res_2996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2977_, v___x_2978_, v_ys_2979_, v_recArgInfo_2980_, v___x_2981_, v___x_2982_, v_group_2983_, v___x_2984_, v_as_2985_, v_sz_boxed_2994_, v_i_boxed_2995_, v_b_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_as_2985_);
lean_dec(v___x_2984_);
lean_dec_ref(v_ys_2979_);
lean_dec_ref(v___x_2978_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0(lean_object* v_group_2997_, lean_object* v_fixedParamPerm_2998_, lean_object* v_xs_2999_, lean_object* v_recArgPos_3000_, lean_object* v_a_3001_, lean_object* v___x_3002_, lean_object* v___x_3003_, lean_object* v_ys_3004_, lean_object* v_x_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_toIndGroupInfo_3011_; lean_object* v_all_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3051_; 
v_toIndGroupInfo_3011_ = lean_ctor_get(v_group_2997_, 0);
lean_inc_ref(v_toIndGroupInfo_3011_);
v_all_3012_ = lean_ctor_get(v_toIndGroupInfo_3011_, 0);
lean_inc_ref(v_ys_3004_);
lean_inc_ref(v_fixedParamPerm_2998_);
v___x_3013_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_2998_, v_xs_2999_, v_ys_3004_);
v___x_3014_ = l_Lean_instInhabitedExpr;
v___x_3015_ = lean_array_get(v___x_3014_, v___x_3013_, v_recArgPos_3000_);
v___x_3016_ = lean_array_get_size(v_all_3012_);
v___x_3017_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3011_);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_toIndGroupInfo_3011_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; lean_object* v_unused_3053_; 
v_unused_3052_ = lean_ctor_get(v_toIndGroupInfo_3011_, 1);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v_toIndGroupInfo_3011_, 0);
lean_dec(v_unused_3053_);
v___x_3019_ = v_toIndGroupInfo_3011_;
v_isShared_3020_ = v_isSharedCheck_3051_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v_toIndGroupInfo_3011_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3051_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3016_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 1, v___x_3017_);
lean_ctor_set(v___x_3019_, 0, v___x_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3017_);
v___x_3023_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; size_t v_sz_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3023_);
v_sz_3026_ = lean_array_size(v_a_3001_);
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_3015_, v___x_3013_, v_ys_3004_, v___x_3002_, v_fixedParamPerm_2998_, v_recArgPos_3000_, v_group_2997_, v___x_3003_, v_a_3001_, v_sz_3026_, v___x_3027_, v___x_3025_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec_ref(v_ys_3004_);
lean_dec_ref(v___x_3013_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3041_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_fst_3033_; 
v_fst_3033_ = lean_ctor_get(v_a_3029_, 0);
lean_inc(v_fst_3033_);
lean_dec(v_a_3029_);
if (lean_obj_tag(v_fst_3033_) == 0)
{
lean_object* v___x_3035_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3024_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3024_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
else
{
lean_object* v_val_3037_; lean_object* v___x_3039_; 
v_val_3037_ = lean_ctor_get(v_fst_3033_, 0);
lean_inc(v_val_3037_);
lean_dec_ref_known(v_fst_3033_, 1);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_val_3037_);
v___x_3039_ = v___x_3031_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_val_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
v_a_3042_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3028_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3028_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0___boxed(lean_object* v_group_3054_, lean_object* v_fixedParamPerm_3055_, lean_object* v_xs_3056_, lean_object* v_recArgPos_3057_, lean_object* v_a_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v_ys_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0(v_group_3054_, v_fixedParamPerm_3055_, v_xs_3056_, v_recArgPos_3057_, v_a_3058_, v___x_3059_, v___x_3060_, v_ys_3061_, v_x_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec_ref(v_x_3062_);
lean_dec(v___x_3060_);
lean_dec_ref(v_a_3058_);
lean_dec_ref(v_xs_3056_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5(lean_object* v_group_3069_, lean_object* v_a_3070_, lean_object* v_xs_3071_, lean_object* v_value_3072_, lean_object* v_as_3073_, size_t v_i_3074_, size_t v_stop_3075_, lean_object* v_b_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_a_3083_; lean_object* v_val_3088_; uint8_t v___x_3090_; 
v___x_3090_ = lean_usize_dec_eq(v_i_3074_, v_stop_3075_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v_fixedParamPerm_3092_; lean_object* v_recArgPos_3093_; lean_object* v_indGroupInst_3094_; lean_object* v___x_3095_; 
v___x_3091_ = lean_array_uget_borrowed(v_as_3073_, v_i_3074_);
v_fixedParamPerm_3092_ = lean_ctor_get(v___x_3091_, 1);
v_recArgPos_3093_ = lean_ctor_get(v___x_3091_, 2);
v_indGroupInst_3094_ = lean_ctor_get(v___x_3091_, 4);
lean_inc_ref(v_indGroupInst_3094_);
lean_inc_ref(v_group_3069_);
v___x_3095_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3069_, v_indGroupInst_3094_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; uint8_t v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = lean_unbox(v_a_3096_);
lean_dec(v_a_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_array_get_size(v_a_3070_);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_nat_dec_eq(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___f_3101_; lean_object* v___x_3102_; 
lean_inc(v___x_3091_);
lean_inc_ref(v_a_3070_);
lean_inc(v_recArgPos_3093_);
lean_inc_ref(v_xs_3071_);
lean_inc_ref(v_fixedParamPerm_3092_);
lean_inc_ref(v_group_3069_);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3101_, 0, v_group_3069_);
lean_closure_set(v___f_3101_, 1, v_fixedParamPerm_3092_);
lean_closure_set(v___f_3101_, 2, v_xs_3071_);
lean_closure_set(v___f_3101_, 3, v_recArgPos_3093_);
lean_closure_set(v___f_3101_, 4, v_a_3070_);
lean_closure_set(v___f_3101_, 5, v___x_3091_);
lean_closure_set(v___f_3101_, 6, v___x_3098_);
lean_inc_ref(v_value_3072_);
v___x_3102_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3072_, v___f_3101_, v___x_3100_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
if (lean_obj_tag(v_a_3103_) == 0)
{
v_a_3083_ = v_b_3076_;
goto v___jp_3082_;
}
else
{
lean_object* v_val_3104_; 
v_val_3104_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v_a_3103_, 1);
v_val_3088_ = v_val_3104_;
goto v___jp_3087_;
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v_b_3076_);
lean_dec_ref(v_value_3072_);
lean_dec_ref(v_xs_3071_);
lean_dec_ref(v_a_3070_);
lean_dec_ref(v_group_3069_);
v_a_3105_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3102_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3102_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
v_a_3083_ = v_b_3076_;
goto v___jp_3082_;
}
}
else
{
lean_inc(v___x_3091_);
v_val_3088_ = v___x_3091_;
goto v___jp_3087_;
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_b_3076_);
lean_dec_ref(v_value_3072_);
lean_dec_ref(v_xs_3071_);
lean_dec_ref(v_a_3070_);
lean_dec_ref(v_group_3069_);
v_a_3113_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3095_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3095_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v___x_3121_; 
lean_dec_ref(v_value_3072_);
lean_dec_ref(v_xs_3071_);
lean_dec_ref(v_a_3070_);
lean_dec_ref(v_group_3069_);
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3076_);
return v___x_3121_;
}
v___jp_3082_:
{
size_t v___x_3084_; size_t v___x_3085_; 
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_add(v_i_3074_, v___x_3084_);
v_i_3074_ = v___x_3085_;
v_b_3076_ = v_a_3083_;
goto _start;
}
v___jp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_array_push(v_b_3076_, v_val_3088_);
v_a_3083_ = v___x_3089_;
goto v___jp_3082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5___boxed(lean_object* v_group_3122_, lean_object* v_a_3123_, lean_object* v_xs_3124_, lean_object* v_value_3125_, lean_object* v_as_3126_, lean_object* v_i_3127_, lean_object* v_stop_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
size_t v_i_boxed_3135_; size_t v_stop_boxed_3136_; lean_object* v_res_3137_; 
v_i_boxed_3135_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_stop_boxed_3136_ = lean_unbox_usize(v_stop_3128_);
lean_dec(v_stop_3128_);
v_res_3137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5(v_group_3122_, v_a_3123_, v_xs_3124_, v_value_3125_, v_as_3126_, v_i_boxed_3135_, v_stop_boxed_3136_, v_b_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v_as_3126_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v_group_3138_, lean_object* v_a_3139_, lean_object* v_xs_3140_, lean_object* v_value_3141_, lean_object* v_as_3142_, lean_object* v_start_3143_, lean_object* v_stop_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3151_ = lean_nat_dec_lt(v_start_3143_, v_stop_3144_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v_value_3141_);
lean_dec_ref(v_xs_3140_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_group_3138_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
return v___x_3152_;
}
else
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = lean_array_get_size(v_as_3142_);
v___x_3154_ = lean_nat_dec_le(v_stop_3144_, v___x_3153_);
if (v___x_3154_ == 0)
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_nat_dec_lt(v_start_3143_, v___x_3153_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v_value_3141_);
lean_dec_ref(v_xs_3140_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_group_3138_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3150_);
return v___x_3156_;
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = lean_usize_of_nat(v_start_3143_);
v___x_3158_ = lean_usize_of_nat(v___x_3153_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5(v_group_3138_, v_a_3139_, v_xs_3140_, v_value_3141_, v_as_3142_, v___x_3157_, v___x_3158_, v___x_3150_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3159_;
}
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = lean_usize_of_nat(v_start_3143_);
v___x_3161_ = lean_usize_of_nat(v_stop_3144_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__5(v_group_3138_, v_a_3139_, v_xs_3140_, v_value_3141_, v_as_3142_, v___x_3160_, v___x_3161_, v___x_3150_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object* v_group_3163_, lean_object* v_a_3164_, lean_object* v_xs_3165_, lean_object* v_value_3166_, lean_object* v_as_3167_, lean_object* v_start_3168_, lean_object* v_stop_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4(v_group_3163_, v_a_3164_, v_xs_3165_, v_value_3166_, v_as_3167_, v_start_3168_, v_stop_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v_stop_3169_);
lean_dec(v_start_3168_);
lean_dec_ref(v_as_3167_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3176_, lean_object* v_xs_3177_, lean_object* v_value_3178_, lean_object* v_recArgInfos_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v___x_3185_; 
lean_inc_ref(v_group_3176_);
v___x_3185_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3176_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = lean_array_get_size(v_recArgInfos_3179_);
v___x_3189_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__4(v_group_3176_, v_a_3186_, v_xs_3177_, v_value_3178_, v_recArgInfos_3179_, v___x_3187_, v___x_3188_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_value_3178_);
lean_dec_ref(v_xs_3177_);
lean_dec_ref(v_group_3176_);
v_a_3190_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3185_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3185_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3198_, lean_object* v_xs_3199_, lean_object* v_value_3200_, lean_object* v_recArgInfos_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Elab_Structural_argsInGroup(v_group_3198_, v_xs_3199_, v_value_3200_, v_recArgInfos_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec_ref(v_recArgInfos_3201_);
return v_res_3207_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_unsigned_to_nat(10u);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3211_, lean_object* v_i_3212_, lean_object* v_acc_3213_){
_start:
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = lean_array_get_size(v_xss_3211_);
v___x_3215_ = lean_nat_dec_lt(v_i_3212_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_3216_);
v___x_3218_ = lean_array_push(v___x_3217_, v_acc_3213_);
return v___x_3218_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3219_ = lean_array_fget_borrowed(v_xss_3211_, v_i_3212_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3222_ = lean_array_get_size(v___x_3219_);
v___x_3223_ = lean_nat_dec_lt(v___x_3220_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_dec_ref(v_acc_3213_);
return v___x_3221_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_nat_dec_le(v___x_3222_, v___x_3222_);
if (v___x_3224_ == 0)
{
if (v___x_3223_ == 0)
{
lean_dec_ref(v_acc_3213_);
return v___x_3221_;
}
else
{
size_t v___x_3225_; size_t v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = ((size_t)0ULL);
v___x_3226_ = lean_usize_of_nat(v___x_3222_);
v___x_3227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3212_, v_acc_3213_, v_xss_3211_, v___x_3219_, v___x_3225_, v___x_3226_, v___x_3221_);
return v___x_3227_;
}
}
else
{
size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = ((size_t)0ULL);
v___x_3229_ = lean_usize_of_nat(v___x_3222_);
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3212_, v_acc_3213_, v_xss_3211_, v___x_3219_, v___x_3228_, v___x_3229_, v___x_3221_);
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3231_, lean_object* v_acc_3232_, lean_object* v_xss_3233_, lean_object* v_as_3234_, size_t v_i_3235_, size_t v_stop_3236_, lean_object* v_b_3237_){
_start:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_usize_dec_eq(v_i_3235_, v_stop_3236_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; size_t v___x_3245_; size_t v___x_3246_; 
v___x_3239_ = lean_array_uget_borrowed(v_as_3234_, v_i_3235_);
v___x_3240_ = lean_unsigned_to_nat(1u);
v___x_3241_ = lean_nat_add(v_i_3231_, v___x_3240_);
lean_inc(v___x_3239_);
lean_inc_ref(v_acc_3232_);
v___x_3242_ = lean_array_push(v_acc_3232_, v___x_3239_);
v___x_3243_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3233_, v___x_3241_, v___x_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = l_Array_append___redArg(v_b_3237_, v___x_3243_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3235_, v___x_3245_);
v_i_3235_ = v___x_3246_;
v_b_3237_ = v___x_3244_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3232_);
return v_b_3237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3248_, lean_object* v_acc_3249_, lean_object* v_xss_3250_, lean_object* v_as_3251_, lean_object* v_i_3252_, lean_object* v_stop_3253_, lean_object* v_b_3254_){
_start:
{
size_t v_i_boxed_3255_; size_t v_stop_boxed_3256_; lean_object* v_res_3257_; 
v_i_boxed_3255_ = lean_unbox_usize(v_i_3252_);
lean_dec(v_i_3252_);
v_stop_boxed_3256_ = lean_unbox_usize(v_stop_3253_);
lean_dec(v_stop_3253_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3248_, v_acc_3249_, v_xss_3250_, v_as_3251_, v_i_boxed_3255_, v_stop_boxed_3256_, v_b_3254_);
lean_dec_ref(v_as_3251_);
lean_dec_ref(v_xss_3250_);
lean_dec(v_i_3248_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3258_, lean_object* v_i_3259_, lean_object* v_acc_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3258_, v_i_3259_, v_acc_3260_);
lean_dec(v_i_3259_);
lean_dec_ref(v_xss_3258_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3262_, lean_object* v_xss_3263_, lean_object* v_i_3264_, lean_object* v_acc_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3263_, v_i_3264_, v_acc_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3267_, lean_object* v_xss_3268_, lean_object* v_i_3269_, lean_object* v_acc_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3267_, v_xss_3268_, v_i_3269_, v_acc_3270_);
lean_dec(v_i_3269_);
lean_dec_ref(v_xss_3268_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3272_, lean_object* v_i_3273_, lean_object* v_acc_3274_, lean_object* v_xss_3275_, lean_object* v_as_3276_, size_t v_i_3277_, size_t v_stop_3278_, lean_object* v_b_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3273_, v_acc_3274_, v_xss_3275_, v_as_3276_, v_i_3277_, v_stop_3278_, v_b_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_i_3282_, lean_object* v_acc_3283_, lean_object* v_xss_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_, lean_object* v_stop_3287_, lean_object* v_b_3288_){
_start:
{
size_t v_i_boxed_3289_; size_t v_stop_boxed_3290_; lean_object* v_res_3291_; 
v_i_boxed_3289_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_stop_boxed_3290_ = lean_unbox_usize(v_stop_3287_);
lean_dec(v_stop_3287_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3281_, v_i_3282_, v_acc_3283_, v_xss_3284_, v_as_3285_, v_i_boxed_3289_, v_stop_boxed_3290_, v_b_3288_);
lean_dec_ref(v_as_3285_);
lean_dec_ref(v_xss_3284_);
lean_dec(v_i_3282_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3292_, size_t v_i_3293_, size_t v_stop_3294_, lean_object* v_b_3295_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_eq(v_i_3293_, v_stop_3294_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; 
v___x_3297_ = lean_array_uget_borrowed(v_as_3292_, v_i_3293_);
v___x_3298_ = lean_array_get_size(v___x_3297_);
v___x_3299_ = lean_nat_mul(v_b_3295_, v___x_3298_);
lean_dec(v_b_3295_);
v___x_3300_ = ((size_t)1ULL);
v___x_3301_ = lean_usize_add(v_i_3293_, v___x_3300_);
v_i_3293_ = v___x_3301_;
v_b_3295_ = v___x_3299_;
goto _start;
}
else
{
return v_b_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3303_, lean_object* v_i_3304_, lean_object* v_stop_3305_, lean_object* v_b_3306_){
_start:
{
size_t v_i_boxed_3307_; size_t v_stop_boxed_3308_; lean_object* v_res_3309_; 
v_i_boxed_3307_ = lean_unbox_usize(v_i_3304_);
lean_dec(v_i_3304_);
v_stop_boxed_3308_ = lean_unbox_usize(v_stop_3305_);
lean_dec(v_stop_3305_);
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3303_, v_i_boxed_3307_, v_stop_boxed_3308_, v_b_3306_);
lean_dec_ref(v_as_3303_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___y_3315_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3311_ = lean_unsigned_to_nat(10u);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_array_get_size(v_xss_3310_);
v___x_3322_ = lean_nat_dec_lt(v___x_3313_, v___x_3321_);
if (v___x_3322_ == 0)
{
v___y_3315_ = v___x_3312_;
goto v___jp_3314_;
}
else
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_nat_dec_le(v___x_3321_, v___x_3321_);
if (v___x_3323_ == 0)
{
if (v___x_3322_ == 0)
{
v___y_3315_ = v___x_3312_;
goto v___jp_3314_;
}
else
{
size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = lean_usize_of_nat(v___x_3321_);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3310_, v___x_3324_, v___x_3325_, v___x_3312_);
v___y_3315_ = v___x_3326_;
goto v___jp_3314_;
}
}
else
{
size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3321_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3310_, v___x_3327_, v___x_3328_, v___x_3312_);
v___y_3315_ = v___x_3329_;
goto v___jp_3314_;
}
}
v___jp_3314_:
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_nat_dec_lt(v___x_3311_, v___y_3315_);
lean_dec(v___y_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3318_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3310_, v___x_3313_, v___x_3317_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_box(0);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3330_);
lean_dec_ref(v_xss_3330_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3332_, lean_object* v_xss_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3335_, lean_object* v_xss_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3335_, v_xss_3336_);
lean_dec_ref(v_xss_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3338_, lean_object* v_as_3339_, size_t v_i_3340_, size_t v_stop_3341_, lean_object* v_b_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3339_, v_i_3340_, v_stop_3341_, v_b_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3344_, lean_object* v_as_3345_, lean_object* v_i_3346_, lean_object* v_stop_3347_, lean_object* v_b_3348_){
_start:
{
size_t v_i_boxed_3349_; size_t v_stop_boxed_3350_; lean_object* v_res_3351_; 
v_i_boxed_3349_ = lean_unbox_usize(v_i_3346_);
lean_dec(v_i_3346_);
v_stop_boxed_3350_ = lean_unbox_usize(v_stop_3347_);
lean_dec(v_stop_3347_);
v_res_3351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3344_, v_as_3345_, v_i_boxed_3349_, v_stop_boxed_3350_, v_b_3348_);
lean_dec_ref(v_as_3345_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3352_, size_t v_i_3353_, size_t v_stop_3354_, lean_object* v_b_3355_){
_start:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_usize_dec_eq(v_i_3353_, v_stop_3354_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; size_t v___x_3359_; size_t v___x_3360_; 
v___x_3357_ = lean_array_uget_borrowed(v_as_3352_, v_i_3353_);
v___x_3358_ = l_Array_append___redArg(v_b_3355_, v___x_3357_);
v___x_3359_ = ((size_t)1ULL);
v___x_3360_ = lean_usize_add(v_i_3353_, v___x_3359_);
v_i_3353_ = v___x_3360_;
v_b_3355_ = v___x_3358_;
goto _start;
}
else
{
return v_b_3355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3362_, lean_object* v_i_3363_, lean_object* v_stop_3364_, lean_object* v_b_3365_){
_start:
{
size_t v_i_boxed_3366_; size_t v_stop_boxed_3367_; lean_object* v_res_3368_; 
v_i_boxed_3366_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_stop_boxed_3367_ = lean_unbox_usize(v_stop_3364_);
lean_dec(v_stop_3364_);
v_res_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3362_, v_i_boxed_3366_, v_stop_boxed_3367_, v_b_3365_);
lean_dec_ref(v_as_3362_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
if (lean_obj_tag(v_a_3369_) == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = l_List_reverse___redArg(v_a_3370_);
return v___x_3371_;
}
else
{
lean_object* v_head_3372_; lean_object* v_tail_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3383_; 
v_head_3372_ = lean_ctor_get(v_a_3369_, 0);
v_tail_3373_ = lean_ctor_get(v_a_3369_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3369_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3375_ = v_a_3369_;
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_tail_3373_);
lean_inc(v_head_3372_);
lean_dec(v_a_3369_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3377_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3372_);
v___x_3378_ = l_Lean_MessageData_ofFormat(v___x_3377_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v_a_3370_);
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3370_);
v___x_3380_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3369_ = v_tail_3373_;
v_a_3370_ = v___x_3380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_bs_3386_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3387_ == 0)
{
return v_bs_3386_;
}
else
{
lean_object* v_v_3388_; lean_object* v___x_3389_; lean_object* v_bs_x27_3390_; lean_object* v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v_v_3388_ = lean_array_uget(v_bs_3386_, v_i_3385_);
v___x_3389_ = lean_unsigned_to_nat(0u);
v_bs_x27_3390_ = lean_array_uset(v_bs_3386_, v_i_3385_, v___x_3389_);
v___x_3391_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3388_);
lean_dec(v_v_3388_);
v___x_3392_ = ((size_t)1ULL);
v___x_3393_ = lean_usize_add(v_i_3385_, v___x_3392_);
v___x_3394_ = lean_array_uset(v_bs_x27_3390_, v_i_3385_, v___x_3391_);
v_i_3385_ = v___x_3393_;
v_bs_3386_ = v___x_3394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_bs_3398_){
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3399_, v_i_boxed_3400_, v_bs_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3402_, lean_object* v_as_3403_, size_t v_sz_3404_, size_t v_i_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_usize_dec_lt(v_i_3405_, v_sz_3404_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
lean_dec_ref(v_xs_3402_);
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v_b_3406_);
return v___x_3413_;
}
else
{
lean_object* v_snd_3414_; lean_object* v_snd_3415_; lean_object* v_snd_3416_; lean_object* v_snd_3417_; lean_object* v_fst_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3562_; 
v_snd_3414_ = lean_ctor_get(v_b_3406_, 1);
lean_inc(v_snd_3414_);
v_snd_3415_ = lean_ctor_get(v_snd_3414_, 1);
lean_inc(v_snd_3415_);
v_snd_3416_ = lean_ctor_get(v_snd_3415_, 1);
lean_inc(v_snd_3416_);
v_snd_3417_ = lean_ctor_get(v_snd_3416_, 1);
lean_inc(v_snd_3417_);
v_fst_3418_ = lean_ctor_get(v_b_3406_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_b_3406_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v_b_3406_, 1);
lean_dec(v_unused_3563_);
v___x_3420_ = v_b_3406_;
v_isShared_3421_ = v_isSharedCheck_3562_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_fst_3418_);
lean_dec(v_b_3406_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3562_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_fst_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3560_; 
v_fst_3422_ = lean_ctor_get(v_snd_3414_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_snd_3414_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_snd_3414_, 1);
lean_dec(v_unused_3561_);
v___x_3424_ = v_snd_3414_;
v_isShared_3425_ = v_isSharedCheck_3560_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_fst_3422_);
lean_dec(v_snd_3414_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3560_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_fst_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3558_; 
v_fst_3426_ = lean_ctor_get(v_snd_3415_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_snd_3415_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_snd_3415_, 1);
lean_dec(v_unused_3559_);
v___x_3428_ = v_snd_3415_;
v_isShared_3429_ = v_isSharedCheck_3558_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_fst_3426_);
lean_dec(v_snd_3415_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3558_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_fst_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3556_; 
v_fst_3430_ = lean_ctor_get(v_snd_3416_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_snd_3416_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v_snd_3416_, 1);
lean_dec(v_unused_3557_);
v___x_3432_ = v_snd_3416_;
v_isShared_3433_ = v_isSharedCheck_3556_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_fst_3430_);
lean_dec(v_snd_3416_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3556_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_array_3434_; lean_object* v_start_3435_; lean_object* v_stop_3436_; uint8_t v___x_3437_; 
v_array_3434_ = lean_ctor_get(v_snd_3417_, 0);
v_start_3435_ = lean_ctor_get(v_snd_3417_, 1);
v_stop_3436_ = lean_ctor_get(v_snd_3417_, 2);
v___x_3437_ = lean_nat_dec_lt(v_start_3435_, v_stop_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3439_; 
lean_dec_ref(v_xs_3402_);
if (v_isShared_3433_ == 0)
{
v___x_3439_ = v___x_3432_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_snd_3417_);
v___x_3439_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3439_);
v___x_3441_ = v___x_3428_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3441_);
v___x_3443_ = v___x_3424_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_fst_3422_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3443_);
v___x_3445_ = v___x_3420_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_fst_3418_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
}
}
}
else
{
lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3552_; 
lean_inc(v_stop_3436_);
lean_inc(v_start_3435_);
lean_inc_ref(v_array_3434_);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_snd_3417_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3553_ = lean_ctor_get(v_snd_3417_, 2);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_snd_3417_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_snd_3417_, 0);
lean_dec(v_unused_3555_);
v___x_3452_ = v_snd_3417_;
v_isShared_3453_ = v_isSharedCheck_3552_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v_snd_3417_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3552_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_array_3454_; lean_object* v_start_3455_; lean_object* v_stop_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v_array_3454_ = lean_ctor_get(v_fst_3430_, 0);
v_start_3455_ = lean_ctor_get(v_fst_3430_, 1);
v_stop_3456_ = lean_ctor_get(v_fst_3430_, 2);
v___x_3457_ = lean_array_fget(v_array_3434_, v_start_3435_);
v___x_3458_ = lean_unsigned_to_nat(1u);
v___x_3459_ = lean_nat_add(v_start_3435_, v___x_3458_);
lean_dec(v_start_3435_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3459_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_array_3434_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_stop_3436_);
v___x_3461_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_nat_dec_lt(v_start_3455_, v_stop_3456_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3464_; 
lean_dec(v___x_3457_);
lean_dec_ref(v_xs_3402_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3461_);
v___x_3464_ = v___x_3432_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v___x_3461_);
v___x_3464_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3464_);
v___x_3466_ = v___x_3428_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3466_);
v___x_3468_ = v___x_3424_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_fst_3422_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3468_);
v___x_3470_ = v___x_3420_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3418_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
}
}
else
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3547_; 
lean_inc(v_stop_3456_);
lean_inc(v_start_3455_);
lean_inc_ref(v_array_3454_);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_fst_3430_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3548_ = lean_ctor_get(v_fst_3430_, 2);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_fst_3430_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_fst_3430_, 0);
lean_dec(v_unused_3550_);
v___x_3477_ = v_fst_3430_;
v_isShared_3478_ = v_isSharedCheck_3547_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v_fst_3430_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3547_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_array_3479_; lean_object* v_start_3480_; lean_object* v_stop_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v_array_3479_ = lean_ctor_get(v_fst_3426_, 0);
v_start_3480_ = lean_ctor_get(v_fst_3426_, 1);
v_stop_3481_ = lean_ctor_get(v_fst_3426_, 2);
v___x_3482_ = lean_array_fget(v_array_3454_, v_start_3455_);
v___x_3483_ = lean_nat_add(v_start_3455_, v___x_3458_);
lean_dec(v_start_3455_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v___x_3483_);
v___x_3485_ = v___x_3477_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_array_3454_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_stop_3456_);
v___x_3485_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_nat_dec_lt(v_start_3480_, v_stop_3481_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v___x_3482_);
lean_dec(v___x_3457_);
lean_dec_ref(v_xs_3402_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3461_);
lean_ctor_set(v___x_3432_, 0, v___x_3485_);
v___x_3488_ = v___x_3432_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v___x_3461_);
v___x_3488_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3488_);
v___x_3490_ = v___x_3428_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3490_);
v___x_3492_ = v___x_3424_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_fst_3422_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v___x_3492_);
v___x_3494_ = v___x_3420_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_fst_3418_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
}
}
}
}
else
{
lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3542_; 
lean_inc(v_stop_3481_);
lean_inc(v_start_3480_);
lean_inc_ref(v_array_3479_);
lean_del_object(v___x_3420_);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_fst_3426_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; lean_object* v_unused_3544_; lean_object* v_unused_3545_; 
v_unused_3543_ = lean_ctor_get(v_fst_3426_, 2);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_fst_3426_, 1);
lean_dec(v_unused_3544_);
v_unused_3545_ = lean_ctor_get(v_fst_3426_, 0);
lean_dec(v_unused_3545_);
v___x_3501_ = v_fst_3426_;
v_isShared_3502_ = v_isSharedCheck_3542_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v_fst_3426_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3542_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v_a_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_a_3503_ = lean_array_uget_borrowed(v_as_3403_, v_i_3405_);
v___x_3504_ = lean_array_fget_borrowed(v_array_3479_, v_start_3480_);
lean_inc(v___x_3504_);
lean_inc_ref(v_xs_3402_);
lean_inc(v_a_3503_);
v___x_3505_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3503_, v___x_3457_, v_xs_3402_, v___x_3504_, v___x_3482_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v_fst_3507_; lean_object* v_snd_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3533_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v_fst_3507_ = lean_ctor_get(v_a_3506_, 0);
v_snd_3508_ = lean_ctor_get(v_a_3506_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_a_3506_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3510_ = v_a_3506_;
v_isShared_3511_ = v_isSharedCheck_3533_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_snd_3508_);
lean_inc(v_fst_3507_);
lean_dec(v_a_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3533_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3512_ = lean_nat_add(v_start_3480_, v___x_3458_);
lean_dec(v_start_3480_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v___x_3512_);
v___x_3514_ = v___x_3501_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_array_3479_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_stop_3481_);
v___x_3514_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3515_, 0, v_fst_3418_);
lean_ctor_set(v___x_3515_, 1, v_snd_3508_);
v___x_3516_ = lean_array_push(v_fst_3422_, v_fst_3507_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3461_);
lean_ctor_set(v___x_3510_, 0, v___x_3485_);
v___x_3518_ = v___x_3510_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3461_);
v___x_3518_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3518_);
lean_ctor_set(v___x_3432_, 0, v___x_3514_);
v___x_3520_ = v___x_3432_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3520_);
lean_ctor_set(v___x_3428_, 0, v___x_3516_);
v___x_3522_ = v___x_3428_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3522_);
lean_ctor_set(v___x_3424_, 0, v___x_3515_);
v___x_3524_ = v___x_3424_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
size_t v___x_3525_; size_t v___x_3526_; 
v___x_3525_ = ((size_t)1ULL);
v___x_3526_ = lean_usize_add(v_i_3405_, v___x_3525_);
v_i_3405_ = v___x_3526_;
v_b_3406_ = v___x_3524_;
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
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_del_object(v___x_3501_);
lean_dec_ref(v___x_3485_);
lean_dec(v_stop_3481_);
lean_dec(v_start_3480_);
lean_dec_ref(v_array_3479_);
lean_dec_ref(v___x_3461_);
lean_del_object(v___x_3432_);
lean_del_object(v___x_3428_);
lean_del_object(v___x_3424_);
lean_dec(v_fst_3422_);
lean_dec(v_fst_3418_);
lean_dec_ref(v_xs_3402_);
v_a_3534_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3505_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3505_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3564_, lean_object* v_as_3565_, lean_object* v_sz_3566_, lean_object* v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
size_t v_sz_boxed_3574_; size_t v_i_boxed_3575_; lean_object* v_res_3576_; 
v_sz_boxed_3574_ = lean_unbox_usize(v_sz_3566_);
lean_dec(v_sz_3566_);
v_i_boxed_3575_ = lean_unbox_usize(v_i_3567_);
lean_dec(v_i_3567_);
v_res_3576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3564_, v_as_3565_, v_sz_boxed_3574_, v_i_boxed_3575_, v_b_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_as_3565_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
if (lean_obj_tag(v_a_3577_) == 0)
{
lean_object* v___x_3579_; 
v___x_3579_ = l_List_reverse___redArg(v_a_3578_);
return v___x_3579_;
}
else
{
lean_object* v_head_3580_; lean_object* v_tail_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3590_; 
v_head_3580_ = lean_ctor_get(v_a_3577_, 0);
v_tail_3581_ = lean_ctor_get(v_a_3577_, 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3577_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3583_ = v_a_3577_;
v_isShared_3584_ = v_isSharedCheck_3590_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_tail_3581_);
lean_inc(v_head_3580_);
lean_dec(v_a_3577_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3590_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3580_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 1, v_a_3578_);
lean_ctor_set(v___x_3583_, 0, v___x_3585_);
v___x_3587_ = v___x_3583_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_a_3578_);
v___x_3587_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
v_a_3577_ = v_tail_3581_;
v_a_3578_ = v___x_3587_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3591_, lean_object* v_j_3592_){
_start:
{
lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3593_ = lean_array_get_size(v_as_3591_);
v___x_3594_ = lean_nat_dec_lt(v_j_3592_, v___x_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; 
lean_dec(v_j_3592_);
v___x_3595_ = lean_box(0);
return v___x_3595_;
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3596_ = lean_array_fget_borrowed(v_as_3591_, v_j_3592_);
v___x_3597_ = lean_array_get_size(v___x_3596_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v___x_3599_ = lean_nat_dec_eq(v___x_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_unsigned_to_nat(1u);
v___x_3601_ = lean_nat_add(v_j_3592_, v___x_3600_);
lean_dec(v_j_3592_);
v_j_3592_ = v___x_3601_;
goto _start;
}
else
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_j_3592_);
return v___x_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3604_, lean_object* v_j_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3604_, v_j_3605_);
lean_dec_ref(v_as_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3607_, lean_object* v_as_3608_, size_t v_sz_3609_, size_t v_i_3610_, lean_object* v_b_3611_){
_start:
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_usize_dec_lt(v_i_3610_, v_sz_3609_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref(v_a_3607_);
v___x_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3614_, 0, v_b_3611_);
return v___x_3614_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; 
v_a_3615_ = lean_array_uget_borrowed(v_as_3608_, v_i_3610_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3607_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v_a_3607_);
lean_ctor_set(v___x_3616_, 1, v_a_3615_);
v___x_3617_ = lean_array_push(v_b_3611_, v___x_3616_);
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3610_, v___x_3618_);
v_i_3610_ = v___x_3619_;
v_b_3611_ = v___x_3617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3621_, lean_object* v_as_3622_, lean_object* v_sz_3623_, lean_object* v_i_3624_, lean_object* v_b_3625_, lean_object* v___y_3626_){
_start:
{
size_t v_sz_boxed_3627_; size_t v_i_boxed_3628_; lean_object* v_res_3629_; 
v_sz_boxed_3627_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v_i_boxed_3628_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_res_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3621_, v_as_3622_, v_sz_boxed_3627_, v_i_boxed_3628_, v_b_3625_);
lean_dec_ref(v_as_3622_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3630_, lean_object* v_xs_3631_, lean_object* v_as_3632_, size_t v_sz_3633_, size_t v_i_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
uint8_t v___x_3641_; 
v___x_3641_ = lean_usize_dec_lt(v_i_3634_, v_sz_3633_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec_ref(v_xs_3631_);
lean_dec_ref(v_a_3630_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_b_3635_);
return v___x_3642_;
}
else
{
lean_object* v_snd_3643_; lean_object* v_fst_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3687_; 
v_snd_3643_ = lean_ctor_get(v_b_3635_, 1);
v_fst_3644_ = lean_ctor_get(v_b_3635_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_b_3635_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3646_ = v_b_3635_;
v_isShared_3647_ = v_isSharedCheck_3687_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_snd_3643_);
lean_inc(v_fst_3644_);
lean_dec(v_b_3635_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3687_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_array_3648_; lean_object* v_start_3649_; lean_object* v_stop_3650_; uint8_t v___x_3651_; 
v_array_3648_ = lean_ctor_get(v_snd_3643_, 0);
v_start_3649_ = lean_ctor_get(v_snd_3643_, 1);
v_stop_3650_ = lean_ctor_get(v_snd_3643_, 2);
v___x_3651_ = lean_nat_dec_lt(v_start_3649_, v_stop_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3653_; 
lean_dec_ref(v_xs_3631_);
lean_dec_ref(v_a_3630_);
if (v_isShared_3647_ == 0)
{
v___x_3653_ = v___x_3646_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_fst_3644_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_snd_3643_);
v___x_3653_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
else
{
lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3683_; 
lean_inc(v_stop_3650_);
lean_inc(v_start_3649_);
lean_inc_ref(v_array_3648_);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_snd_3643_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; lean_object* v_unused_3685_; lean_object* v_unused_3686_; 
v_unused_3684_ = lean_ctor_get(v_snd_3643_, 2);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_snd_3643_, 1);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_snd_3643_, 0);
lean_dec(v_unused_3686_);
v___x_3657_ = v_snd_3643_;
v_isShared_3658_ = v_isSharedCheck_3683_;
goto v_resetjp_3656_;
}
else
{
lean_dec(v_snd_3643_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3683_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_a_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_a_3659_ = lean_array_uget_borrowed(v_as_3632_, v_i_3634_);
v___x_3660_ = lean_array_fget_borrowed(v_array_3648_, v_start_3649_);
lean_inc(v_a_3659_);
lean_inc_ref(v_xs_3631_);
lean_inc_ref(v_a_3630_);
v___x_3661_ = l_Lean_Elab_Structural_argsInGroup(v_a_3630_, v_xs_3631_, v_a_3659_, v___x_3660_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = lean_nat_add(v_start_3649_, v___x_3663_);
lean_dec(v_start_3649_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v___x_3664_);
v___x_3666_ = v___x_3657_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_array_3648_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_stop_3650_);
v___x_3666_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_array_push(v_fst_3644_, v_a_3662_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___x_3666_);
lean_ctor_set(v___x_3646_, 0, v___x_3667_);
v___x_3669_ = v___x_3646_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3666_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
size_t v___x_3670_; size_t v___x_3671_; 
v___x_3670_ = ((size_t)1ULL);
v___x_3671_ = lean_usize_add(v_i_3634_, v___x_3670_);
v_i_3634_ = v___x_3671_;
v_b_3635_ = v___x_3669_;
goto _start;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_del_object(v___x_3657_);
lean_dec(v_stop_3650_);
lean_dec(v_start_3649_);
lean_dec_ref(v_array_3648_);
lean_del_object(v___x_3646_);
lean_dec(v_fst_3644_);
lean_dec_ref(v_xs_3631_);
lean_dec_ref(v_a_3630_);
v_a_3675_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3661_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3661_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3688_, lean_object* v_xs_3689_, lean_object* v_as_3690_, lean_object* v_sz_3691_, lean_object* v_i_3692_, lean_object* v_b_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
size_t v_sz_boxed_3699_; size_t v_i_boxed_3700_; lean_object* v_res_3701_; 
v_sz_boxed_3699_ = lean_unbox_usize(v_sz_3691_);
lean_dec(v_sz_3691_);
v_i_boxed_3700_ = lean_unbox_usize(v_i_3692_);
lean_dec(v_i_3692_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3688_, v_xs_3689_, v_as_3690_, v_sz_boxed_3699_, v_i_boxed_3700_, v_b_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_as_3690_);
return v_res_3701_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3706_ = l_Lean_stringToMessageData(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3715_ = l_Lean_stringToMessageData(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3722_, lean_object* v_values_3723_, lean_object* v_xs_3724_, lean_object* v_fnNames_3725_, lean_object* v_as_3726_, size_t v_sz_3727_, size_t v_i_3728_, lean_object* v_b_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_a_3736_; uint8_t v___x_3740_; 
v___x_3740_ = lean_usize_dec_lt(v_i_3728_, v_sz_3727_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v_xs_3724_);
lean_dec_ref(v___x_3722_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_b_3729_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v_recArgInfoss_3743_; lean_object* v_a_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; size_t v_sz_3748_; size_t v___x_3749_; lean_object* v___x_3750_; 
v___x_3742_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3744_ = lean_array_uget_borrowed(v_as_3726_, v_i_3728_);
v___x_3745_ = lean_array_get_size(v___x_3722_);
lean_inc_ref(v___x_3722_);
v___x_3746_ = l_Array_toSubarray___redArg(v___x_3722_, v___x_3742_, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v_recArgInfoss_3743_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v_sz_3748_ = lean_array_size(v_values_3723_);
v___x_3749_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3724_);
lean_inc(v_a_3744_);
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3744_, v_xs_3724_, v_values_3723_, v_sz_3748_, v___x_3749_, v___x_3747_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v_fst_3752_; lean_object* v_snd_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3811_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v_fst_3752_ = lean_ctor_get(v_b_3729_, 0);
v_snd_3753_ = lean_ctor_get(v_b_3729_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_b_3729_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3755_ = v_b_3729_;
v_isShared_3756_ = v_isSharedCheck_3811_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_snd_3753_);
lean_inc(v_fst_3752_);
lean_dec(v_b_3729_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3811_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_fst_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3809_; 
v_fst_3757_ = lean_ctor_get(v_a_3751_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v_a_3751_, 1);
lean_dec(v_unused_3810_);
v___x_3759_ = v_a_3751_;
v_isShared_3760_ = v_isSharedCheck_3809_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_fst_3757_);
lean_dec(v_a_3751_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3809_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3757_, v___x_3742_);
if (lean_obj_tag(v___x_3761_) == 1)
{
lean_object* v_val_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec(v_fst_3757_);
v_val_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3744_);
v___x_3765_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3744_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set_tag(v___x_3755_, 7);
lean_ctor_set(v___x_3755_, 1, v___x_3765_);
lean_ctor_set(v___x_3755_, 0, v___x_3764_);
v___x_3767_ = v___x_3755_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_array_get_borrowed(v___x_3763_, v_fnNames_3725_, v_val_3762_);
lean_dec(v_val_3762_);
lean_inc(v___x_3770_);
v___x_3771_ = l_Lean_MessageData_ofName(v___x_3770_);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3769_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_fst_3752_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_snd_3753_);
lean_ctor_set(v___x_3759_, 0, v___x_3775_);
v___x_3777_ = v___x_3759_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_snd_3753_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
v_a_3736_ = v___x_3777_;
goto v___jp_3735_;
}
}
}
else
{
lean_object* v___x_3780_; 
lean_dec(v___x_3761_);
v___x_3780_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3757_);
lean_dec(v_fst_3757_);
if (lean_obj_tag(v___x_3780_) == 1)
{
lean_object* v_val_3781_; size_t v_sz_3782_; lean_object* v___x_3783_; 
lean_del_object(v___x_3755_);
v_val_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_val_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v_sz_3782_ = lean_array_size(v_val_3781_);
lean_inc(v_a_3744_);
v___x_3783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3744_, v_val_3781_, v_sz_3782_, v___x_3749_, v_snd_3753_);
lean_dec(v_val_3781_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_a_3784_);
lean_ctor_set(v___x_3759_, 0, v_fst_3752_);
v___x_3786_ = v___x_3759_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_fst_3752_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_a_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
v_a_3736_ = v___x_3786_;
goto v___jp_3735_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3759_);
lean_dec(v_fst_3752_);
lean_dec_ref(v_xs_3724_);
lean_dec_ref(v___x_3722_);
v_a_3788_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3783_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3783_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
lean_dec(v___x_3780_);
v___x_3796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3744_);
v___x_3797_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3744_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set_tag(v___x_3755_, 7);
lean_ctor_set(v___x_3755_, 1, v___x_3797_);
lean_ctor_set(v___x_3755_, 0, v___x_3796_);
v___x_3799_ = v___x_3755_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v_fst_3752_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v_snd_3753_);
lean_ctor_set(v___x_3759_, 0, v___x_3804_);
v___x_3806_ = v___x_3759_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_snd_3753_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v_a_3736_ = v___x_3806_;
goto v___jp_3735_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_b_3729_);
lean_dec_ref(v_xs_3724_);
lean_dec_ref(v___x_3722_);
v_a_3812_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3750_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3750_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
v___jp_3735_:
{
size_t v___x_3737_; size_t v___x_3738_; 
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3728_, v___x_3737_);
v_i_3728_ = v___x_3738_;
v_b_3729_ = v_a_3736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3820_, lean_object* v_values_3821_, lean_object* v_xs_3822_, lean_object* v_fnNames_3823_, lean_object* v_as_3824_, lean_object* v_sz_3825_, lean_object* v_i_3826_, lean_object* v_b_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3825_);
lean_dec(v_sz_3825_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3826_);
lean_dec(v_i_3826_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3820_, v_values_3821_, v_xs_3822_, v_fnNames_3823_, v_as_3824_, v_sz_boxed_3833_, v_i_boxed_3834_, v_b_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec_ref(v_as_3824_);
lean_dec_ref(v_fnNames_3823_);
lean_dec_ref(v_values_3821_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3836_, lean_object* v___x_3837_, lean_object* v_values_3838_, lean_object* v_fnNames_3839_, lean_object* v_as_3840_, size_t v_sz_3841_, size_t v_i_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_a_3850_; uint8_t v___x_3854_; 
v___x_3854_ = lean_usize_dec_lt(v_i_3842_, v_sz_3841_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___x_3837_);
lean_dec_ref(v_xs_3836_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_b_3843_);
return v___x_3855_;
}
else
{
lean_object* v___x_3856_; lean_object* v_recArgInfoss_3857_; lean_object* v_a_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; size_t v_sz_3862_; size_t v___x_3863_; lean_object* v___x_3864_; 
v___x_3856_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3858_ = lean_array_uget_borrowed(v_as_3840_, v_i_3842_);
v___x_3859_ = lean_array_get_size(v___x_3837_);
lean_inc_ref(v___x_3837_);
v___x_3860_ = l_Array_toSubarray___redArg(v___x_3837_, v___x_3856_, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_recArgInfoss_3857_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v_sz_3862_ = lean_array_size(v_values_3838_);
v___x_3863_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3836_);
lean_inc(v_a_3858_);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3858_, v_xs_3836_, v_values_3838_, v_sz_3862_, v___x_3863_, v___x_3861_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v_fst_3866_; lean_object* v_snd_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3925_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v_fst_3866_ = lean_ctor_get(v_b_3843_, 0);
v_snd_3867_ = lean_ctor_get(v_b_3843_, 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_b_3843_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3869_ = v_b_3843_;
v_isShared_3870_ = v_isSharedCheck_3925_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_snd_3867_);
lean_inc(v_fst_3866_);
lean_dec(v_b_3843_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3925_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_fst_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3923_; 
v_fst_3871_ = lean_ctor_get(v_a_3865_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_a_3865_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; 
v_unused_3924_ = lean_ctor_get(v_a_3865_, 1);
lean_dec(v_unused_3924_);
v___x_3873_ = v_a_3865_;
v_isShared_3874_ = v_isSharedCheck_3923_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_fst_3871_);
lean_dec(v_a_3865_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3923_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3871_, v___x_3856_);
if (lean_obj_tag(v___x_3875_) == 1)
{
lean_object* v_val_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
lean_dec(v_fst_3871_);
v_val_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_val_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v___x_3877_ = lean_box(0);
v___x_3878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3858_);
v___x_3879_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3858_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set_tag(v___x_3869_, 7);
lean_ctor_set(v___x_3869_, 1, v___x_3879_);
lean_ctor_set(v___x_3869_, 0, v___x_3878_);
v___x_3881_ = v___x_3869_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3881_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = lean_array_get_borrowed(v___x_3877_, v_fnNames_3839_, v_val_3876_);
lean_dec(v_val_3876_);
lean_inc(v___x_3884_);
v___x_3885_ = l_Lean_MessageData_ofName(v___x_3884_);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3883_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_fst_3866_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v_snd_3867_);
lean_ctor_set(v___x_3873_, 0, v___x_3889_);
v___x_3891_ = v___x_3873_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_snd_3867_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
v_a_3850_ = v___x_3891_;
goto v___jp_3849_;
}
}
}
else
{
lean_object* v___x_3894_; 
lean_dec(v___x_3875_);
v___x_3894_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3871_);
lean_dec(v_fst_3871_);
if (lean_obj_tag(v___x_3894_) == 1)
{
lean_object* v_val_3895_; size_t v_sz_3896_; lean_object* v___x_3897_; 
lean_del_object(v___x_3869_);
v_val_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v_sz_3896_ = lean_array_size(v_val_3895_);
lean_inc(v_a_3858_);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3858_, v_val_3895_, v_sz_3896_, v___x_3863_, v_snd_3867_);
lean_dec(v_val_3895_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v_a_3898_);
lean_ctor_set(v___x_3873_, 0, v_fst_3866_);
v___x_3900_ = v___x_3873_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_fst_3866_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_a_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
v_a_3850_ = v___x_3900_;
goto v___jp_3849_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3873_);
lean_dec(v_fst_3866_);
lean_dec_ref(v___x_3837_);
lean_dec_ref(v_xs_3836_);
v_a_3902_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3897_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3897_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v___x_3894_);
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3858_);
v___x_3911_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3858_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set_tag(v___x_3869_, 7);
lean_ctor_set(v___x_3869_, 1, v___x_3911_);
lean_ctor_set(v___x_3869_, 0, v___x_3910_);
v___x_3913_ = v___x_3869_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_fst_3866_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v_snd_3867_);
lean_ctor_set(v___x_3873_, 0, v___x_3918_);
v___x_3920_ = v___x_3873_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_snd_3867_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
v_a_3850_ = v___x_3920_;
goto v___jp_3849_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v_b_3843_);
lean_dec_ref(v___x_3837_);
lean_dec_ref(v_xs_3836_);
v_a_3926_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3864_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3864_);
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
v___jp_3849_:
{
size_t v___x_3851_; size_t v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = ((size_t)1ULL);
v___x_3852_ = lean_usize_add(v_i_3842_, v___x_3851_);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3837_, v_values_3838_, v_xs_3836_, v_fnNames_3839_, v_as_3840_, v_sz_3841_, v___x_3852_, v_a_3850_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3934_, lean_object* v___x_3935_, lean_object* v_values_3936_, lean_object* v_fnNames_3937_, lean_object* v_as_3938_, lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
size_t v_sz_boxed_3947_; size_t v_i_boxed_3948_; lean_object* v_res_3949_; 
v_sz_boxed_3947_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3948_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3934_, v___x_3935_, v_values_3936_, v_fnNames_3937_, v_as_3938_, v_sz_boxed_3947_, v_i_boxed_3948_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec_ref(v_as_3938_);
lean_dec_ref(v_fnNames_3937_);
lean_dec_ref(v_values_3936_);
return v_res_3949_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3954_ = l_Lean_MessageData_ofFormat(v___x_3953_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3957_ = l_Lean_stringToMessageData(v___x_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3962_ = l_Lean_stringToMessageData(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_box(1);
v___x_3964_ = l_Lean_MessageData_ofFormat(v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3965_, lean_object* v_fixedParamPerms_3966_, lean_object* v_xs_3967_, lean_object* v_values_3968_, lean_object* v_termMeasure_x3fs_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v___x_3975_; lean_object* v_recArgInfoss_3976_; lean_object* v___x_3977_; lean_object* v_perms_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v_report_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; size_t v_sz_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3975_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3977_ = lean_array_get_size(v_values_3968_);
v_perms_3978_ = lean_ctor_get(v_fixedParamPerms_3966_, 1);
lean_inc_ref(v_perms_3978_);
lean_dec_ref(v_fixedParamPerms_3966_);
lean_inc_ref(v_values_3968_);
v___x_3979_ = l_Array_toSubarray___redArg(v_values_3968_, v___x_3975_, v___x_3977_);
v___x_3980_ = lean_array_get_size(v_termMeasure_x3fs_3969_);
v_report_3981_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3982_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3969_, v___x_3975_, v___x_3980_);
v___x_3983_ = lean_array_get_size(v_perms_3978_);
v___x_3984_ = l_Array_toSubarray___redArg(v_perms_3978_, v___x_3975_, v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3982_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3979_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_recArgInfoss_3976_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v_report_3981_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v_sz_3989_ = lean_array_size(v_fnNames_3965_);
v___x_3990_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3967_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3967_, v_fnNames_3965_, v_sz_3989_, v___x_3990_, v___x_3988_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v_snd_3993_; lean_object* v_options_3994_; lean_object* v_fst_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4138_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v_snd_3993_ = lean_ctor_get(v_a_3992_, 1);
lean_inc(v_snd_3993_);
v_options_3994_ = lean_ctor_get(v_a_3972_, 2);
v_fst_3995_ = lean_ctor_get(v_a_3992_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_a_3992_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_a_3992_, 1);
lean_dec(v_unused_4139_);
v___x_3997_ = v_a_3992_;
v_isShared_3998_ = v_isSharedCheck_4138_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_fst_3995_);
lean_dec(v_a_3992_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4138_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_fst_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4136_; 
v_fst_3999_ = lean_ctor_get(v_snd_3993_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_snd_3993_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v_snd_3993_, 1);
lean_dec(v_unused_4137_);
v___x_4001_ = v_snd_3993_;
v_isShared_4002_ = v_isSharedCheck_4136_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_fst_3999_);
lean_dec(v_snd_3993_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4136_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v_inheritedTraceOptions_4003_; uint8_t v_hasTrace_4004_; size_t v_sz_4005_; lean_object* v___x_4006_; lean_object* v___y_4008_; lean_object* v_report_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___x_4056_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; 
v_inheritedTraceOptions_4003_ = lean_ctor_get(v_a_3972_, 13);
v_hasTrace_4004_ = lean_ctor_get_uint8(v_options_3994_, sizeof(void*)*1);
v_sz_4005_ = lean_array_size(v_fst_3999_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4005_, v___x_3990_, v_fst_3999_);
v___x_4056_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4004_ == 0)
{
v___y_4095_ = v_a_3970_;
v___y_4096_ = v_a_3971_;
v___y_4097_ = v_a_3972_;
v___y_4098_ = v_a_3973_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_4107_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4003_, v_options_3994_, v___x_4107_);
if (v___x_4108_ == 0)
{
v___y_4095_ = v_a_3970_;
v___y_4096_ = v_a_3971_;
v___y_4097_ = v_a_3972_;
v___y_4098_ = v_a_3973_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4109_; lean_object* v___y_4111_; lean_object* v___x_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4109_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4128_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4129_ = lean_array_get_size(v___x_4006_);
v___x_4130_ = lean_nat_dec_lt(v___x_3975_, v___x_4129_);
if (v___x_4130_ == 0)
{
v___y_4111_ = v___x_4128_;
goto v___jp_4110_;
}
else
{
uint8_t v___x_4131_; 
v___x_4131_ = lean_nat_dec_le(v___x_4129_, v___x_4129_);
if (v___x_4131_ == 0)
{
if (v___x_4130_ == 0)
{
v___y_4111_ = v___x_4128_;
goto v___jp_4110_;
}
else
{
size_t v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_usize_of_nat(v___x_4129_);
v___x_4133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4006_, v___x_3990_, v___x_4132_, v___x_4128_);
v___y_4111_ = v___x_4133_;
goto v___jp_4110_;
}
}
else
{
size_t v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_usize_of_nat(v___x_4129_);
v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4006_, v___x_3990_, v___x_4134_, v___x_4128_);
v___y_4111_ = v___x_4135_;
goto v___jp_4110_;
}
}
v___jp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4112_ = lean_array_to_list(v___y_4111_);
v___x_4113_ = lean_box(0);
v___x_4114_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4112_, v___x_4113_);
v___x_4115_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4116_ = l_Lean_MessageData_joinSep(v___x_4114_, v___x_4115_);
v___x_4117_ = l_Lean_indentD(v___x_4116_);
v___x_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4109_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4056_, v___x_4118_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_dec_ref_known(v___x_4119_, 1);
v___y_4095_ = v_a_3970_;
v___y_4096_ = v_a_3971_;
v___y_4097_ = v_a_3972_;
v___y_4098_ = v_a_3973_;
goto v___jp_4094_;
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v___x_4006_);
lean_del_object(v___x_4001_);
lean_del_object(v___x_3997_);
lean_dec(v_fst_3995_);
lean_dec_ref(v_values_3968_);
lean_dec_ref(v_xs_3967_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
v___jp_4007_:
{
lean_object* v___x_4015_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v_recArgInfoss_3976_);
lean_ctor_set(v___x_4001_, 0, v_report_4009_);
v___x_4015_ = v___x_4001_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_report_4009_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_recArgInfoss_3976_);
v___x_4015_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
size_t v_sz_4016_; lean_object* v___x_4017_; 
v_sz_4016_ = lean_array_size(v___y_4008_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3967_, v___x_4006_, v_values_3968_, v_fnNames_3965_, v___y_4008_, v_sz_4016_, v___x_3990_, v___x_4015_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v_values_3968_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4034_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4034_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v_fst_4022_; lean_object* v_snd_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4033_; 
v_fst_4022_ = lean_ctor_get(v_a_4018_, 0);
v_snd_4023_ = lean_ctor_get(v_a_4018_, 1);
v_isSharedCheck_4033_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4025_ = v_a_4018_;
v_isShared_4026_ = v_isSharedCheck_4033_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_snd_4023_);
lean_inc(v_fst_4022_);
lean_dec(v_a_4018_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4033_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 1, v_fst_4022_);
lean_ctor_set(v___x_4025_, 0, v_snd_4023_);
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_snd_4023_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_fst_4022_);
v___x_4028_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4028_);
v___x_4030_ = v___x_4020_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4017_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4017_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
}
v___jp_4044_:
{
lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4050_ = lean_array_get_size(v___y_4045_);
v___x_4051_ = lean_nat_dec_eq(v___x_4050_, v___x_3975_);
if (v___x_4051_ == 0)
{
lean_del_object(v___x_3997_);
v___y_4008_ = v___y_4045_;
v_report_4009_ = v_fst_3995_;
v___y_4010_ = v___y_4046_;
v___y_4011_ = v___y_4047_;
v___y_4012_ = v___y_4048_;
v___y_4013_ = v___y_4049_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4052_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 7);
lean_ctor_set(v___x_3997_, 1, v___x_4052_);
v___x_4054_ = v___x_3997_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_fst_3995_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
v___y_4008_ = v___y_4045_;
v_report_4009_ = v___x_4054_;
v___y_4010_ = v___y_4046_;
v___y_4011_ = v___y_4047_;
v___y_4012_ = v___y_4048_;
v___y_4013_ = v___y_4049_;
goto v___jp_4007_;
}
}
}
v___jp_4057_:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4062_, v___y_4060_, v___y_4059_, v___y_4061_, v___y_4058_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_options_4064_; uint8_t v_hasTrace_4065_; 
v_options_4064_ = lean_ctor_get(v___y_4061_, 2);
v_hasTrace_4065_ = lean_ctor_get_uint8(v_options_4064_, sizeof(void*)*1);
if (v_hasTrace_4065_ == 0)
{
lean_object* v_a_4066_; 
v_a_4066_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4063_, 1);
v___y_4045_ = v_a_4066_;
v___y_4046_ = v___y_4060_;
v___y_4047_ = v___y_4059_;
v___y_4048_ = v___y_4061_;
v___y_4049_ = v___y_4058_;
goto v___jp_4044_;
}
else
{
lean_object* v_a_4067_; lean_object* v_inheritedTraceOptions_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v_a_4067_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4063_, 1);
v_inheritedTraceOptions_4068_ = lean_ctor_get(v___y_4061_, 13);
v___x_4069_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4064_, v___x_4069_);
if (v___x_4070_ == 0)
{
v___y_4045_ = v_a_4067_;
v___y_4046_ = v___y_4060_;
v___y_4047_ = v___y_4059_;
v___y_4048_ = v___y_4061_;
v___y_4049_ = v___y_4058_;
goto v___jp_4044_;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4071_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4067_);
v___x_4072_ = lean_array_to_list(v_a_4067_);
v___x_4073_ = lean_box(0);
v___x_4074_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4072_, v___x_4073_);
v___x_4075_ = l_Lean_MessageData_ofList(v___x_4074_);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4071_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4056_, v___x_4076_, v___y_4060_, v___y_4059_, v___y_4061_, v___y_4058_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_dec_ref_known(v___x_4077_, 1);
v___y_4045_ = v_a_4067_;
v___y_4046_ = v___y_4060_;
v___y_4047_ = v___y_4059_;
v___y_4048_ = v___y_4061_;
v___y_4049_ = v___y_4058_;
goto v___jp_4044_;
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v_a_4067_);
lean_dec_ref(v___x_4006_);
lean_del_object(v___x_4001_);
lean_del_object(v___x_3997_);
lean_dec(v_fst_3995_);
lean_dec_ref(v_values_3968_);
lean_dec_ref(v_xs_3967_);
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v___x_4006_);
lean_del_object(v___x_4001_);
lean_del_object(v___x_3997_);
lean_dec(v_fst_3995_);
lean_dec_ref(v_values_3968_);
lean_dec_ref(v_xs_3967_);
v_a_4086_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4063_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4063_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
v___jp_4094_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4099_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4100_ = lean_array_get_size(v___x_4006_);
v___x_4101_ = lean_nat_dec_lt(v___x_3975_, v___x_4100_);
if (v___x_4101_ == 0)
{
v___y_4058_ = v___y_4098_;
v___y_4059_ = v___y_4096_;
v___y_4060_ = v___y_4095_;
v___y_4061_ = v___y_4097_;
v___y_4062_ = v___x_4099_;
goto v___jp_4057_;
}
else
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_nat_dec_le(v___x_4100_, v___x_4100_);
if (v___x_4102_ == 0)
{
if (v___x_4101_ == 0)
{
v___y_4058_ = v___y_4098_;
v___y_4059_ = v___y_4096_;
v___y_4060_ = v___y_4095_;
v___y_4061_ = v___y_4097_;
v___y_4062_ = v___x_4099_;
goto v___jp_4057_;
}
else
{
size_t v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_usize_of_nat(v___x_4100_);
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4006_, v___x_3990_, v___x_4103_, v___x_4099_);
v___y_4058_ = v___y_4098_;
v___y_4059_ = v___y_4096_;
v___y_4060_ = v___y_4095_;
v___y_4061_ = v___y_4097_;
v___y_4062_ = v___x_4104_;
goto v___jp_4057_;
}
}
else
{
size_t v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_usize_of_nat(v___x_4100_);
v___x_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4006_, v___x_3990_, v___x_4105_, v___x_4099_);
v___y_4058_ = v___y_4098_;
v___y_4059_ = v___y_4096_;
v___y_4060_ = v___y_4095_;
v___y_4061_ = v___y_4097_;
v___y_4062_ = v___x_4106_;
goto v___jp_4057_;
}
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_values_3968_);
lean_dec_ref(v_xs_3967_);
v_a_4140_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_3991_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_3991_);
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
lean_object* v_a_4224_; uint8_t v___y_4226_; uint8_t v___x_4244_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
v___x_4244_ = l_Lean_Exception_isInterrupt(v_a_4224_);
if (v___x_4244_ == 0)
{
uint8_t v___x_4245_; 
lean_inc(v_a_4224_);
v___x_4245_ = l_Lean_Exception_isRuntime(v_a_4224_);
v___y_4226_ = v___x_4245_;
goto v___jp_4225_;
}
else
{
v___y_4226_ = v___x_4244_;
goto v___jp_4225_;
}
v___jp_4225_:
{
if (v___y_4226_ == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4223_, 1);
v___x_4227_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4222_, v___y_4217_, v___y_4219_);
lean_dec(v_a_4222_);
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
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_x_4215_);
v_a_4246_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4221_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4221_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4261_, lean_object* v_x_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4279_ = l_Lean_stringToMessageData(v___x_4278_);
return v___x_4279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4282_ = l_Lean_stringToMessageData(v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4283_, uint8_t v___x_4284_, lean_object* v_group_4285_, lean_object* v_k_4286_, lean_object* v_comb_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4283_, v___x_4284_, v___y_4291_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; uint8_t v___x_4295_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
v___x_4295_ = lean_unbox(v_a_4294_);
lean_dec(v_a_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4297_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4285_);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4300_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; 
lean_dec_ref_known(v___x_4301_, 1);
v___x_4302_ = lean_apply_6(v_k_4286_, v_comb_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, lean_box(0));
return v___x_4302_;
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_comb_4287_);
lean_dec_ref(v_k_4286_);
v_a_4303_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4301_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4301_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
else
{
lean_object* v___x_4311_; 
lean_dec_ref(v_group_4285_);
v___x_4311_ = lean_apply_6(v_k_4286_, v_comb_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, lean_box(0));
return v___x_4311_;
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_comb_4287_);
lean_dec_ref(v_k_4286_);
lean_dec_ref(v_group_4285_);
v_a_4312_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4293_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4293_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4320_, lean_object* v___x_4321_, lean_object* v_group_4322_, lean_object* v_k_4323_, lean_object* v_comb_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
uint8_t v___x_4418__boxed_4330_; lean_object* v_res_4331_; 
v___x_4418__boxed_4330_ = lean_unbox(v___x_4321_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4320_, v___x_4418__boxed_4330_, v_group_4322_, v_k_4323_, v_comb_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v_res_4331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4337_, lean_object* v_fnNames_4338_, lean_object* v_xs_4339_, lean_object* v_values_4340_, lean_object* v_as_4341_, size_t v_sz_4342_, size_t v_i_4343_, lean_object* v_b_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v___x_4350_; 
v___x_4350_ = lean_usize_dec_lt(v_i_4343_, v_sz_4342_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
lean_dec_ref(v_values_4340_);
lean_dec_ref(v_xs_4339_);
lean_dec_ref(v_k_4337_);
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_b_4344_);
return v___x_4351_;
}
else
{
lean_object* v_snd_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4422_; 
v_snd_4352_ = lean_ctor_get(v_b_4344_, 1);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_b_4344_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; 
v_unused_4423_ = lean_ctor_get(v_b_4344_, 0);
lean_dec(v_unused_4423_);
v___x_4354_ = v_b_4344_;
v_isShared_4355_ = v_isSharedCheck_4422_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_snd_4352_);
lean_dec(v_b_4344_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4422_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v_a_4356_; lean_object* v_group_4357_; lean_object* v_comb_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4421_; 
v_a_4356_ = lean_array_uget(v_as_4341_, v_i_4343_);
v_group_4357_ = lean_ctor_get(v_a_4356_, 0);
v_comb_4358_ = lean_ctor_get(v_a_4356_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_a_4356_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4360_ = v_a_4356_;
v_isShared_4361_ = v_isSharedCheck_4421_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_comb_4358_);
lean_inc(v_group_4357_);
lean_dec(v_a_4356_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4421_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_toIndGroupInfo_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; 
v_toIndGroupInfo_4362_ = lean_ctor_get(v_group_4357_, 0);
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4362_, v___x_4363_);
v___x_4365_ = lean_box(v___x_4350_);
lean_inc_ref(v_comb_4358_);
lean_inc_ref(v_k_4337_);
v___f_4366_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4366_, 0, v___x_4364_);
lean_closure_set(v___f_4366_, 1, v___x_4365_);
lean_closure_set(v___f_4366_, 2, v_group_4357_);
lean_closure_set(v___f_4366_, 3, v_k_4337_);
lean_closure_set(v___f_4366_, 4, v_comb_4358_);
v___x_4367_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4366_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4360_);
lean_dec_ref(v_comb_4358_);
lean_dec_ref(v_values_4340_);
lean_dec_ref(v_xs_4339_);
lean_dec_ref(v_k_4337_);
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
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4372_);
v___x_4374_ = v___x_4354_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_snd_4352_);
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
lean_object* v___x_4384_; uint8_t v___y_4386_; uint8_t v___x_4418_; 
v___x_4384_ = lean_box(0);
v___x_4418_ = l_Lean_Exception_isInterrupt(v_a_4380_);
if (v___x_4418_ == 0)
{
uint8_t v___x_4419_; 
lean_inc(v_a_4380_);
v___x_4419_ = l_Lean_Exception_isRuntime(v_a_4380_);
v___y_4386_ = v___x_4419_;
goto v___jp_4385_;
}
else
{
v___y_4386_ = v___x_4418_;
goto v___jp_4385_;
}
v___jp_4385_:
{
if (v___y_4386_ == 0)
{
lean_object* v___x_4387_; 
lean_del_object(v___x_4382_);
lean_inc_ref(v_values_4340_);
lean_inc_ref(v_xs_4339_);
v___x_4387_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4338_, v_xs_4339_, v_values_4340_, v_comb_4358_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4389_; lean_object* v___x_4391_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4389_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4361_ == 0)
{
lean_ctor_set_tag(v___x_4360_, 7);
lean_ctor_set(v___x_4360_, 1, v_a_4388_);
lean_ctor_set(v___x_4360_, 0, v___x_4389_);
v___x_4391_ = v___x_4360_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4389_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_a_4388_);
v___x_4391_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4392_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = l_Lean_Exception_toMessageData(v_a_4380_);
v___x_4395_ = l_Lean_indentD(v___x_4394_);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4393_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v_snd_4352_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 1, v___x_4399_);
lean_ctor_set(v___x_4354_, 0, v___x_4384_);
v___x_4401_ = v___x_4354_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
size_t v___x_4402_; size_t v___x_4403_; 
v___x_4402_ = ((size_t)1ULL);
v___x_4403_ = lean_usize_add(v_i_4343_, v___x_4402_);
v_i_4343_ = v___x_4403_;
v_b_4344_ = v___x_4401_;
goto _start;
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4380_);
lean_del_object(v___x_4360_);
lean_del_object(v___x_4354_);
lean_dec(v_snd_4352_);
lean_dec_ref(v_values_4340_);
lean_dec_ref(v_xs_4339_);
lean_dec_ref(v_k_4337_);
v_a_4407_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4387_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4387_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v___x_4416_; 
lean_del_object(v___x_4360_);
lean_dec_ref(v_comb_4358_);
lean_del_object(v___x_4354_);
lean_dec(v_snd_4352_);
lean_dec_ref(v_values_4340_);
lean_dec_ref(v_xs_4339_);
lean_dec_ref(v_k_4337_);
if (v_isShared_4383_ == 0)
{
v___x_4416_ = v___x_4382_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4380_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
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
lean_object* v_candidates_4456_; lean_object* v_report_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4516_; 
v_candidates_4456_ = lean_ctor_get(v_candidates_4449_, 0);
v_report_4457_ = lean_ctor_get(v_candidates_4449_, 1);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_candidates_4449_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4459_ = v_candidates_4449_;
v_isShared_4460_ = v_isSharedCheck_4516_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_report_4457_);
lean_inc(v_candidates_4456_);
lean_dec(v_candidates_4449_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4516_;
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
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4461_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_report_4457_);
v___x_4463_ = v_reuseFailAlloc_4515_;
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
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4506_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4506_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4506_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v_fst_4471_; 
v_fst_4471_ = lean_ctor_get(v_a_4467_, 0);
if (lean_obj_tag(v_fst_4471_) == 0)
{
lean_object* v_options_4472_; lean_object* v_snd_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4500_; 
lean_del_object(v___x_4469_);
v_options_4472_ = lean_ctor_get(v_a_4453_, 2);
v_snd_4473_ = lean_ctor_get(v_a_4467_, 1);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_a_4467_, 0);
lean_dec(v_unused_4501_);
v___x_4475_ = v_a_4467_;
v_isShared_4476_ = v_isSharedCheck_4500_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_snd_4473_);
lean_dec(v_a_4467_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4500_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_inheritedTraceOptions_4477_; uint8_t v_hasTrace_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
v_inheritedTraceOptions_4477_ = lean_ctor_get(v_a_4453_, 13);
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
v___x_4482_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
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
v___x_4486_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
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
v___x_4489_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4483_, v___x_4488_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4490_; 
lean_dec_ref_known(v___x_4489_, 1);
v___x_4490_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4481_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
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
lean_inc_ref(v_fst_4471_);
lean_dec(v_a_4467_);
v_val_4502_ = lean_ctor_get(v_fst_4471_, 0);
lean_inc(v_val_4502_);
lean_dec_ref_known(v_fst_4471_, 1);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v_val_4502_);
v___x_4504_ = v___x_4469_;
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
v_a_4507_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4466_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4466_);
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
