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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* v___f_969_; lean_object* v___x_6889__overap_970_; lean_object* v___x_971_; 
v___f_969_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6889__overap_970_ = lean_panic_fn_borrowed(v___f_969_, v_msg_963_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
v___x_971_ = lean_apply_5(v___x_6889__overap_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, lean_box(0));
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
v___x_1220_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1211_);
if (v___x_1220_ == 0)
{
lean_object* v_name_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec(v___y_1218_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1221_ = lean_ctor_get(v___y_1216_, 0);
lean_inc(v_name_1221_);
lean_dec_ref(v___y_1216_);
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1223_ = l_Lean_MessageData_ofName(v_name_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_indentExpr(v___y_1219_);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1228_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1193_, v_xs_1194_);
v___x_1231_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1230_, v___y_1211_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1230_, v___y_1210_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
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
lean_dec_ref(v___y_1219_);
v_name_1238_ = lean_ctor_get(v___y_1216_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___y_1216_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v___y_1216_, 2);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v___y_1216_, 1);
lean_dec(v_unused_1260_);
v___x_1240_ = v___y_1216_;
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_name_1238_);
lean_dec(v___y_1216_);
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
v_sz_1245_ = lean_array_size(v___y_1211_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1194_, v_sz_1245_, v___x_1246_, v___y_1211_);
v___x_1248_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1209_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 2, v___y_1210_);
lean_ctor_set(v___x_1240_, 1, v___y_1212_);
lean_ctor_set(v___x_1240_, 0, v___x_1248_);
v___x_1250_ = v___x_1240_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___y_1212_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___y_1210_);
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
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1256_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1257_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1256_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
return v___x_1257_;
}
}
}
else
{
lean_object* v_val_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1236_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
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
v___x_1268_ = l_Lean_indentExpr(v___y_1219_);
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
v___x_1281_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1280_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
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
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
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
v_name_1299_ = lean_ctor_get(v___y_1216_, 0);
lean_inc(v_name_1299_);
lean_dec_ref(v___y_1216_);
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
v___x_1306_ = l_Lean_indentExpr(v___y_1219_);
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
v___x_1316_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1315_, v___y_1215_, v___y_1214_, v___y_1213_, v___y_1217_);
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___x_1230_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
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
v___x_1342_ = l_Array_toSubarray___redArg(v___y_1329_, v_lower_1340_, v_upper_1341_);
v___x_1343_ = l_Subarray_copy___redArg(v___x_1342_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_nat_dec_lt(v___y_1330_, v___x_1344_);
lean_dec(v___y_1330_);
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1332_;
v___y_1211_ = v___x_1343_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1331_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1332_;
v___y_1211_ = v___x_1343_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1331_;
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
v___y_1210_ = v___y_1332_;
v___y_1211_ = v___x_1343_;
v___y_1212_ = v___y_1333_;
v___y_1213_ = v___y_1334_;
v___y_1214_ = v___y_1335_;
v___y_1215_ = v___y_1336_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1331_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
lean_object* v_name_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1343_);
lean_dec(v___y_1338_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec_ref(v___y_1328_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1349_ = lean_ctor_get(v___y_1337_, 0);
lean_inc(v_name_1349_);
lean_dec_ref(v___y_1337_);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1351_ = l_Lean_MessageData_ofName(v_name_1349_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_indentExpr(v___y_1339_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1356_, v___y_1336_, v___y_1335_, v___y_1334_, v___y_1331_);
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
v___y_1328_ = v_val_1375_;
v___y_1329_ = v___x_1384_;
v___y_1330_ = v___x_1385_;
v___y_1331_ = v___y_1363_;
v___y_1332_ = v___x_1387_;
v___y_1333_ = v_us_1369_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1360_;
v___y_1337_ = v_toConstantVal_1376_;
v___y_1338_ = v_all_1378_;
v___y_1339_ = v_a_1366_;
v_lower_1340_ = v_numParams_1377_;
v_upper_1341_ = v___x_1388_;
goto v___jp_1327_;
}
else
{
v___y_1328_ = v_val_1375_;
v___y_1329_ = v___x_1384_;
v___y_1330_ = v___x_1385_;
v___y_1331_ = v___y_1363_;
v___y_1332_ = v___x_1387_;
v___y_1333_ = v_us_1369_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1361_;
v___y_1336_ = v___y_1360_;
v___y_1337_ = v_toConstantVal_1376_;
v___y_1338_ = v_all_1378_;
v___y_1339_ = v_a_1366_;
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
lean_object* v_ref_1630_; lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1677_; 
v_ref_1630_ = lean_ctor_get(v___y_1627_, 5);
v___x_1631_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1677_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1677_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v_traceState_1637_; lean_object* v_env_1638_; lean_object* v_nextMacroScope_1639_; lean_object* v_ngen_1640_; lean_object* v_auxDeclNGen_1641_; lean_object* v_cache_1642_; lean_object* v_messages_1643_; lean_object* v_infoState_1644_; lean_object* v_snapshotTasks_1645_; lean_object* v_newDecls_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1676_; 
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
v_newDecls_1646_ = lean_ctor_get(v___x_1636_, 9);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_newDecls_1646_);
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
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint64_t v_tid_1650_; lean_object* v_traces_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1675_; 
v_tid_1650_ = lean_ctor_get_uint64(v_traceState_1637_, sizeof(void*)*1);
v_traces_1651_ = lean_ctor_get(v_traceState_1637_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_traceState_1637_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1653_ = v_traceState_1637_;
v_isShared_1654_ = v_isSharedCheck_1675_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_traces_1651_);
lean_dec(v_traceState_1637_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1675_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; double v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1657_ = 0;
v___x_1658_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1659_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1659_, 0, v_cls_1623_);
lean_ctor_set(v___x_1659_, 1, v___x_1655_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
lean_ctor_set_float(v___x_1659_, sizeof(void*)*3, v___x_1656_);
lean_ctor_set_float(v___x_1659_, sizeof(void*)*3 + 8, v___x_1656_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*3 + 16, v___x_1657_);
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1661_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v_a_1632_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
lean_inc(v_ref_1630_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v_ref_1630_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_PersistentArray_push___redArg(v_traces_1651_, v___x_1662_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1663_);
v___x_1665_ = v___x_1653_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1663_);
lean_ctor_set_uint64(v_reuseFailAlloc_1674_, sizeof(void*)*1, v_tid_1650_);
v___x_1665_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v___x_1665_);
v___x_1667_ = v___x_1648_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_env_1638_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_nextMacroScope_1639_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_ngen_1640_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_auxDeclNGen_1641_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1673_, 5, v_cache_1642_);
lean_ctor_set(v_reuseFailAlloc_1673_, 6, v_messages_1643_);
lean_ctor_set(v_reuseFailAlloc_1673_, 7, v_infoState_1644_);
lean_ctor_set(v_reuseFailAlloc_1673_, 8, v_snapshotTasks_1645_);
lean_ctor_set(v_reuseFailAlloc_1673_, 9, v_newDecls_1646_);
v___x_1667_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_st_ref_set(v___y_1628_, v___x_1667_);
v___x_1669_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1669_);
v___x_1671_ = v___x_1634_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1678_, lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1678_, v_msg_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1685_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1688_ = l_Lean_stringToMessageData(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___f_1690_; 
v___x_1689_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1690_, 0, v___x_1689_);
return v___f_1690_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1695_; lean_object* v_recArgInfos_1696_; lean_object* v___x_1697_; 
v_report_1695_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1696_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_recArgInfos_1696_);
lean_ctor_set(v___x_1697_, 1, v_report_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1710_ = l_Lean_Name_append(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1714_, lean_object* v_fixedParamPerm_1715_, lean_object* v_xs_1716_, lean_object* v_fnName_1717_, lean_object* v_ys_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1714_) == 1)
{
lean_object* v_val_1725_; lean_object* v_ref_1726_; lean_object* v_fileName_1727_; lean_object* v_fileMap_1728_; lean_object* v_options_1729_; lean_object* v_currRecDepth_1730_; lean_object* v_maxRecDepth_1731_; lean_object* v_ref_1732_; lean_object* v_currNamespace_1733_; lean_object* v_openDecls_1734_; lean_object* v_initHeartbeats_1735_; lean_object* v_maxHeartbeats_1736_; lean_object* v_quotContext_1737_; lean_object* v_currMacroScope_1738_; uint8_t v_diag_1739_; lean_object* v_cancelTk_x3f_1740_; uint8_t v_suppressElabErrors_1741_; lean_object* v_inheritedTraceOptions_1742_; lean_object* v___f_1743_; lean_object* v_args_1744_; lean_object* v___f_1745_; lean_object* v_ref_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_val_1725_ = lean_ctor_get(v_termMeasure_x3f_1714_, 0);
lean_inc(v_val_1725_);
lean_dec_ref(v_termMeasure_x3f_1714_);
v_ref_1726_ = lean_ctor_get(v_val_1725_, 0);
lean_inc(v_ref_1726_);
v_fileName_1727_ = lean_ctor_get(v___y_1722_, 0);
v_fileMap_1728_ = lean_ctor_get(v___y_1722_, 1);
v_options_1729_ = lean_ctor_get(v___y_1722_, 2);
v_currRecDepth_1730_ = lean_ctor_get(v___y_1722_, 3);
v_maxRecDepth_1731_ = lean_ctor_get(v___y_1722_, 4);
v_ref_1732_ = lean_ctor_get(v___y_1722_, 5);
v_currNamespace_1733_ = lean_ctor_get(v___y_1722_, 6);
v_openDecls_1734_ = lean_ctor_get(v___y_1722_, 7);
v_initHeartbeats_1735_ = lean_ctor_get(v___y_1722_, 8);
v_maxHeartbeats_1736_ = lean_ctor_get(v___y_1722_, 9);
v_quotContext_1737_ = lean_ctor_get(v___y_1722_, 10);
v_currMacroScope_1738_ = lean_ctor_get(v___y_1722_, 11);
v_diag_1739_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*14);
v_cancelTk_x3f_1740_ = lean_ctor_get(v___y_1722_, 12);
v_suppressElabErrors_1741_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1742_ = lean_ctor_get(v___y_1722_, 13);
v___f_1743_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1715_);
v_args_1744_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1715_, v_xs_1716_, v_ys_1718_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1745_, 0, v_val_1725_);
lean_closure_set(v___f_1745_, 1, v_fnName_1717_);
lean_closure_set(v___f_1745_, 2, v_fixedParamPerm_1715_);
lean_closure_set(v___f_1745_, 3, v_args_1744_);
v_ref_1746_ = l_Lean_replaceRef(v_ref_1726_, v_ref_1732_);
lean_dec(v_ref_1726_);
lean_inc_ref(v_inheritedTraceOptions_1742_);
lean_inc(v_cancelTk_x3f_1740_);
lean_inc(v_currMacroScope_1738_);
lean_inc(v_quotContext_1737_);
lean_inc(v_maxHeartbeats_1736_);
lean_inc(v_initHeartbeats_1735_);
lean_inc(v_openDecls_1734_);
lean_inc(v_currNamespace_1733_);
lean_inc(v_maxRecDepth_1731_);
lean_inc(v_currRecDepth_1730_);
lean_inc_ref(v_options_1729_);
lean_inc_ref(v_fileMap_1728_);
lean_inc_ref(v_fileName_1727_);
v___x_1747_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1747_, 0, v_fileName_1727_);
lean_ctor_set(v___x_1747_, 1, v_fileMap_1728_);
lean_ctor_set(v___x_1747_, 2, v_options_1729_);
lean_ctor_set(v___x_1747_, 3, v_currRecDepth_1730_);
lean_ctor_set(v___x_1747_, 4, v_maxRecDepth_1731_);
lean_ctor_set(v___x_1747_, 5, v_ref_1746_);
lean_ctor_set(v___x_1747_, 6, v_currNamespace_1733_);
lean_ctor_set(v___x_1747_, 7, v_openDecls_1734_);
lean_ctor_set(v___x_1747_, 8, v_initHeartbeats_1735_);
lean_ctor_set(v___x_1747_, 9, v_maxHeartbeats_1736_);
lean_ctor_set(v___x_1747_, 10, v_quotContext_1737_);
lean_ctor_set(v___x_1747_, 11, v_currMacroScope_1738_);
lean_ctor_set(v___x_1747_, 12, v_cancelTk_x3f_1740_);
lean_ctor_set(v___x_1747_, 13, v_inheritedTraceOptions_1742_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*14, v_diag_1739_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*14 + 1, v_suppressElabErrors_1741_);
v___x_1748_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1745_, v___f_1743_, v___y_1720_, v___y_1721_, v___x_1747_, v___y_1723_);
lean_dec_ref(v___x_1747_);
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
lean_dec(v_termMeasure_x3f_1714_);
lean_inc_ref(v_fixedParamPerm_1715_);
v_args_1770_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1715_, v_xs_1716_, v_ys_1718_);
v___x_1771_ = lean_array_get_size(v_args_1770_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1774_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1771_, v_fnName_1717_, v_fixedParamPerm_1715_, v_args_1770_, v___x_1772_, v___x_1773_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec_ref(v_args_1770_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1809_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1809_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1809_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1808_; 
v_fst_1779_ = lean_ctor_get(v_a_1775_, 0);
v_snd_1780_ = lean_ctor_get(v_a_1775_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1782_ = v_a_1775_;
v_isShared_1783_ = v_isSharedCheck_1808_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_dec(v_a_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1808_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_options_1791_; uint8_t v_hasTrace_1792_; 
v_options_1791_ = lean_ctor_get(v___y_1722_, 2);
v_hasTrace_1792_ = lean_ctor_get_uint8(v_options_1791_, sizeof(void*)*1);
if (v_hasTrace_1792_ == 0)
{
goto v___jp_1784_;
}
else
{
lean_object* v_inheritedTraceOptions_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_inheritedTraceOptions_1793_ = lean_ctor_get(v___y_1722_, 13);
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1793_, v_options_1791_, v___x_1795_);
if (v___x_1796_ == 0)
{
goto v___jp_1784_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1780_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_snd_1780_);
v___x_1799_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1794_, v___x_1798_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref(v___x_1799_);
goto v___jp_1784_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_del_object(v___x_1782_);
lean_dec(v_snd_1780_);
lean_dec(v_fst_1779_);
lean_del_object(v___x_1777_);
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
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_nbuckets_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1917_ = lean_array_get_size(v_data_1916_);
v___x_1918_ = lean_unsigned_to_nat(2u);
v_nbuckets_1919_ = lean_nat_mul(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_mk_array(v_nbuckets_1919_, v___x_1921_);
v___x_1923_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1920_, v_data_1916_, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1924_, lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
return v___x_1926_;
}
else
{
lean_object* v_key_1927_; lean_object* v_tail_1928_; uint8_t v___x_1929_; 
v_key_1927_ = lean_ctor_get(v_x_1925_, 0);
v_tail_1928_ = lean_ctor_get(v_x_1925_, 2);
v___x_1929_ = lean_nat_dec_eq(v_key_1927_, v_a_1924_);
if (v___x_1929_ == 0)
{
v_x_1925_ = v_tail_1928_;
goto _start;
}
else
{
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1931_, lean_object* v_x_1932_){
_start:
{
uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_res_1933_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1931_, v_x_1932_);
lean_dec(v_x_1932_);
lean_dec(v_a_1931_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1935_, lean_object* v_a_1936_, lean_object* v_b_1937_){
_start:
{
lean_object* v_size_1938_; lean_object* v_buckets_1939_; lean_object* v___x_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v_fold_1944_; uint64_t v___x_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; lean_object* v_bkt_1953_; uint8_t v___x_1954_; 
v_size_1938_ = lean_ctor_get(v_m_1935_, 0);
v_buckets_1939_ = lean_ctor_get(v_m_1935_, 1);
v___x_1940_ = lean_array_get_size(v_buckets_1939_);
v___x_1941_ = lean_uint64_of_nat(v_a_1936_);
v___x_1942_ = 32ULL;
v___x_1943_ = lean_uint64_shift_right(v___x_1941_, v___x_1942_);
v_fold_1944_ = lean_uint64_xor(v___x_1941_, v___x_1943_);
v___x_1945_ = 16ULL;
v___x_1946_ = lean_uint64_shift_right(v_fold_1944_, v___x_1945_);
v___x_1947_ = lean_uint64_xor(v_fold_1944_, v___x_1946_);
v___x_1948_ = lean_uint64_to_usize(v___x_1947_);
v___x_1949_ = lean_usize_of_nat(v___x_1940_);
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_sub(v___x_1949_, v___x_1950_);
v___x_1952_ = lean_usize_land(v___x_1948_, v___x_1951_);
v_bkt_1953_ = lean_array_uget_borrowed(v_buckets_1939_, v___x_1952_);
v___x_1954_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1936_, v_bkt_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1975_; 
lean_inc_ref(v_buckets_1939_);
lean_inc(v_size_1938_);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_m_1935_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1976_ = lean_ctor_get(v_m_1935_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_m_1935_, 0);
lean_dec(v_unused_1977_);
v___x_1956_ = v_m_1935_;
v_isShared_1957_ = v_isSharedCheck_1975_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_m_1935_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1975_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v_size_x27_1959_; lean_object* v___x_1960_; lean_object* v_buckets_x27_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1958_ = lean_unsigned_to_nat(1u);
v_size_x27_1959_ = lean_nat_add(v_size_1938_, v___x_1958_);
lean_dec(v_size_1938_);
lean_inc(v_bkt_1953_);
v___x_1960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1960_, 0, v_a_1936_);
lean_ctor_set(v___x_1960_, 1, v_b_1937_);
lean_ctor_set(v___x_1960_, 2, v_bkt_1953_);
v_buckets_x27_1961_ = lean_array_uset(v_buckets_1939_, v___x_1952_, v___x_1960_);
v___x_1962_ = lean_unsigned_to_nat(4u);
v___x_1963_ = lean_nat_mul(v_size_x27_1959_, v___x_1962_);
v___x_1964_ = lean_unsigned_to_nat(3u);
v___x_1965_ = lean_nat_div(v___x_1963_, v___x_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_array_get_size(v_buckets_x27_1961_);
v___x_1967_ = lean_nat_dec_le(v___x_1965_, v___x_1966_);
lean_dec(v___x_1965_);
if (v___x_1967_ == 0)
{
lean_object* v_val_1968_; lean_object* v___x_1970_; 
v_val_1968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1961_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_val_1968_);
lean_ctor_set(v___x_1956_, 0, v_size_x27_1959_);
v___x_1970_ = v___x_1956_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_size_x27_1959_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_val_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
else
{
lean_object* v___x_1973_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_buckets_x27_1961_);
lean_ctor_set(v___x_1956_, 0, v_size_x27_1959_);
v___x_1973_ = v___x_1956_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_size_x27_1959_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_buckets_x27_1961_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_dec(v_b_1937_);
lean_dec(v_a_1936_);
return v_m_1935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1978_, size_t v_sz_1979_, size_t v_i_1980_, lean_object* v_b_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_usize_dec_lt(v_i_1980_, v_sz_1979_);
if (v___x_1982_ == 0)
{
return v_b_1981_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; size_t v___x_1986_; size_t v___x_1987_; 
v_a_1983_ = lean_array_uget_borrowed(v_as_1978_, v_i_1980_);
v___x_1984_ = lean_box(0);
lean_inc(v_a_1983_);
v___x_1985_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1981_, v_a_1983_, v___x_1984_);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1980_, v___x_1986_);
v_i_1980_ = v___x_1987_;
v_b_1981_ = v___x_1985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1989_, lean_object* v_sz_1990_, lean_object* v_i_1991_, lean_object* v_b_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1990_);
lean_dec(v_sz_1990_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1989_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1992_);
lean_dec_ref(v_as_1989_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1996_, size_t v_sz_1997_, size_t v_i_1998_, lean_object* v_b_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_usize_dec_lt(v_i_1998_, v_sz_1997_);
if (v___x_2000_ == 0)
{
return v_b_1999_;
}
else
{
lean_object* v_a_2001_; lean_object* v_indicesPos_2002_; size_t v_sz_2003_; size_t v___x_2004_; lean_object* v___x_2005_; size_t v___x_2006_; size_t v___x_2007_; 
v_a_2001_ = lean_array_uget_borrowed(v_as_1996_, v_i_1998_);
v_indicesPos_2002_ = lean_ctor_get(v_a_2001_, 3);
v_sz_2003_ = lean_array_size(v_indicesPos_2002_);
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2002_, v_sz_2003_, v___x_2004_, v_b_1999_);
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_add(v_i_1998_, v___x_2006_);
v_i_1998_ = v___x_2007_;
v_b_1999_ = v___x_2005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2009_, lean_object* v_sz_2010_, lean_object* v_i_2011_, lean_object* v_b_2012_){
_start:
{
size_t v_sz_boxed_2013_; size_t v_i_boxed_2014_; lean_object* v_res_2015_; 
v_sz_boxed_2013_ = lean_unbox_usize(v_sz_2010_);
lean_dec(v_sz_2010_);
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2009_, v_sz_boxed_2013_, v_i_boxed_2014_, v_b_2012_);
lean_dec_ref(v_as_2009_);
return v_res_2015_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_buckets_2018_; lean_object* v___x_2019_; uint64_t v___x_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint64_t v_fold_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_buckets_2018_ = lean_ctor_get(v_m_2016_, 1);
v___x_2019_ = lean_array_get_size(v_buckets_2018_);
v___x_2020_ = lean_uint64_of_nat(v_a_2017_);
v___x_2021_ = 32ULL;
v___x_2022_ = lean_uint64_shift_right(v___x_2020_, v___x_2021_);
v_fold_2023_ = lean_uint64_xor(v___x_2020_, v___x_2022_);
v___x_2024_ = 16ULL;
v___x_2025_ = lean_uint64_shift_right(v_fold_2023_, v___x_2024_);
v___x_2026_ = lean_uint64_xor(v_fold_2023_, v___x_2025_);
v___x_2027_ = lean_uint64_to_usize(v___x_2026_);
v___x_2028_ = lean_usize_of_nat(v___x_2019_);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_sub(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_usize_land(v___x_2027_, v___x_2030_);
v___x_2032_ = lean_array_uget_borrowed(v_buckets_2018_, v___x_2031_);
v___x_2033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2017_, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2034_, lean_object* v_a_2035_){
_start:
{
uint8_t v_res_2036_; lean_object* v_r_2037_; 
v_res_2036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_m_2034_);
v_r_2037_ = lean_box(v_res_2036_);
return v_r_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2038_, lean_object* v_as_2039_, size_t v_sz_2040_, size_t v_i_2041_, lean_object* v_b_2042_){
_start:
{
lean_object* v_a_2044_; uint8_t v___x_2048_; 
v___x_2048_ = lean_usize_dec_lt(v_i_2041_, v_sz_2040_);
if (v___x_2048_ == 0)
{
return v_b_2042_;
}
else
{
lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2065_; 
v_fst_2049_ = lean_ctor_get(v_b_2042_, 0);
v_snd_2050_ = lean_ctor_get(v_b_2042_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_b_2042_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2052_ = v_b_2042_;
v_isShared_2053_ = v_isSharedCheck_2065_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_snd_2050_);
lean_inc(v_fst_2049_);
lean_dec(v_b_2042_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2065_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_a_2054_; lean_object* v_recArgPos_2055_; uint8_t v___x_2056_; 
v_a_2054_ = lean_array_uget_borrowed(v_as_2039_, v_i_2041_);
v_recArgPos_2055_ = lean_ctor_get(v_a_2054_, 2);
v___x_2056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2038_, v_recArgPos_2055_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_inc(v_a_2054_);
v___x_2057_ = lean_array_push(v_snd_2050_, v_a_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2057_);
v___x_2059_ = v___x_2052_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_fst_2049_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
v_a_2044_ = v___x_2059_;
goto v___jp_2043_;
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_inc(v_a_2054_);
v___x_2061_ = lean_array_push(v_fst_2049_, v_a_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2061_);
v___x_2063_ = v___x_2052_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_snd_2050_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
v_a_2044_ = v___x_2063_;
goto v___jp_2043_;
}
}
}
}
v___jp_2043_:
{
size_t v___x_2045_; size_t v___x_2046_; 
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2041_, v___x_2045_);
v_i_2041_ = v___x_2046_;
v_b_2042_ = v_a_2044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2066_, lean_object* v_as_2067_, lean_object* v_sz_2068_, lean_object* v_i_2069_, lean_object* v_b_2070_){
_start:
{
size_t v_sz_boxed_2071_; size_t v_i_boxed_2072_; lean_object* v_res_2073_; 
v_sz_boxed_2071_ = lean_unbox_usize(v_sz_2068_);
lean_dec(v_sz_2068_);
v_i_boxed_2072_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_res_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2066_, v_as_2067_, v_sz_boxed_2071_, v_i_boxed_2072_, v_b_2070_);
lean_dec_ref(v_as_2067_);
lean_dec_ref(v___x_2066_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_unsigned_to_nat(16u);
v___x_2076_ = lean_mk_array(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_indicesPos_2079_; 
v___x_2077_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2078_ = lean_unsigned_to_nat(0u);
v_indicesPos_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2079_, 0, v___x_2078_);
lean_ctor_set(v_indicesPos_2079_, 1, v___x_2077_);
return v_indicesPos_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2082_){
_start:
{
lean_object* v_indicesPos_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_fst_2089_; lean_object* v_snd_2090_; lean_object* v___x_2091_; 
v_indicesPos_2083_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2084_ = lean_array_size(v_recArgInfos_2082_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2082_, v_sz_2084_, v___x_2085_, v_indicesPos_2083_);
v___x_2087_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2086_, v_recArgInfos_2082_, v_sz_2084_, v___x_2085_, v___x_2087_);
lean_dec_ref(v___x_2086_);
v_fst_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_fst_2089_);
v_snd_2090_ = lean_ctor_get(v___x_2088_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2088_);
v___x_2091_ = l_Array_append___redArg(v_snd_2090_, v_fst_2089_);
lean_dec(v_fst_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2092_);
lean_dec_ref(v_recArgInfos_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2094_, lean_object* v_m_2095_, lean_object* v_a_2096_, lean_object* v_b_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2095_, v_a_2096_, v_b_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2099_, lean_object* v_m_2100_, lean_object* v_a_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2100_, v_a_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2103_, lean_object* v_m_2104_, lean_object* v_a_2105_){
_start:
{
uint8_t v_res_2106_; lean_object* v_r_2107_; 
v_res_2106_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2103_, v_m_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_m_2104_);
v_r_2107_ = lean_box(v_res_2106_);
return v_r_2107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2108_, lean_object* v_a_2109_, lean_object* v_x_2110_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2109_, v_x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2112_, lean_object* v_a_2113_, lean_object* v_x_2114_){
_start:
{
uint8_t v_res_2115_; lean_object* v_r_2116_; 
v_res_2115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2112_, v_a_2113_, v_x_2114_);
lean_dec(v_x_2114_);
lean_dec(v_a_2113_);
v_r_2116_ = lean_box(v_res_2115_);
return v_r_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2117_, lean_object* v_data_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2120_, lean_object* v_i_2121_, lean_object* v_source_2122_, lean_object* v_target_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2121_, v_source_2122_, v_target_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2126_, v_x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2129_, lean_object* v_a_2130_, lean_object* v_toPure_2131_, uint8_t v_____do__lift_2132_){
_start:
{
if (v_____do__lift_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_array_push(v___y_2129_, v_a_2130_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_apply_2(v_toPure_2131_, lean_box(0), v___x_2134_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v_a_2130_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___y_2129_);
v___x_2137_ = lean_apply_2(v_toPure_2131_, lean_box(0), v___x_2136_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2138_, lean_object* v_a_2139_, lean_object* v_toPure_2140_, lean_object* v_____do__lift_2141_){
_start:
{
uint8_t v_____do__lift_192__boxed_2142_; lean_object* v_res_2143_; 
v_____do__lift_192__boxed_2142_ = lean_unbox(v_____do__lift_2141_);
v_res_2143_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2138_, v_a_2139_, v_toPure_2140_, v_____do__lift_192__boxed_2142_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2144_, lean_object* v_a_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_apply_2(v_eq_2144_, v_x_2146_, v_a_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2148_, lean_object* v___x_2149_, lean_object* v_toBind_2150_, lean_object* v_eq_2151_, lean_object* v_inst_2152_, lean_object* v_a_2153_, lean_object* v_x_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
lean_inc(v_toPure_2148_);
lean_inc(v_a_2153_);
lean_inc_ref(v___y_2155_);
v___f_2156_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2156_, 0, v___y_2155_);
lean_closure_set(v___f_2156_, 1, v_a_2153_);
lean_closure_set(v___f_2156_, 2, v_toPure_2148_);
v___x_2157_ = lean_array_get_size(v___y_2155_);
v___x_2158_ = lean_nat_dec_lt(v___x_2149_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___y_2155_);
lean_dec(v_a_2153_);
lean_dec_ref(v_inst_2152_);
lean_dec(v_eq_2151_);
v___x_2159_ = lean_box(v___x_2158_);
v___x_2160_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2159_);
v___x_2161_ = lean_apply_4(v_toBind_2150_, lean_box(0), lean_box(0), v___x_2160_, v___f_2156_);
return v___x_2161_;
}
else
{
if (v___x_2158_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v___y_2155_);
lean_dec(v_a_2153_);
lean_dec_ref(v_inst_2152_);
lean_dec(v_eq_2151_);
v___x_2162_ = lean_box(v___x_2158_);
v___x_2163_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2162_);
v___x_2164_ = lean_apply_4(v_toBind_2150_, lean_box(0), lean_box(0), v___x_2163_, v___f_2156_);
return v___x_2164_;
}
else
{
lean_object* v___f_2165_; size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_toPure_2148_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2165_, 0, v_eq_2151_);
lean_closure_set(v___f_2165_, 1, v_a_2153_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = lean_usize_of_nat(v___x_2157_);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2152_, v___f_2165_, v___y_2155_, v___x_2166_, v___x_2167_);
v___x_2169_ = lean_apply_4(v_toBind_2150_, lean_box(0), lean_box(0), v___x_2168_, v___f_2156_);
return v___x_2169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2170_, lean_object* v___x_2171_, lean_object* v_toBind_2172_, lean_object* v_eq_2173_, lean_object* v_inst_2174_, lean_object* v_a_2175_, lean_object* v_x_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2170_, v___x_2171_, v_toBind_2172_, v_eq_2173_, v_inst_2174_, v_a_2175_, v_x_2176_, v___y_2177_);
lean_dec(v___x_2171_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2179_, lean_object* v_____s_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_apply_2(v_toPure_2179_, lean_box(0), v_____s_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2184_, lean_object* v_eq_2185_, lean_object* v_xs_2186_){
_start:
{
lean_object* v_toApplicative_2187_; lean_object* v_toBind_2188_; lean_object* v_toPure_2189_; lean_object* v___x_2190_; lean_object* v_ret_2191_; lean_object* v___f_2192_; lean_object* v___f_2193_; size_t v_sz_2194_; size_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_toApplicative_2187_ = lean_ctor_get(v_inst_2184_, 0);
v_toBind_2188_ = lean_ctor_get(v_inst_2184_, 1);
lean_inc_n(v_toBind_2188_, 2);
v_toPure_2189_ = lean_ctor_get(v_toApplicative_2187_, 1);
v___x_2190_ = lean_unsigned_to_nat(0u);
v_ret_2191_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2184_);
lean_inc_n(v_toPure_2189_, 2);
v___f_2192_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2192_, 0, v_toPure_2189_);
lean_closure_set(v___f_2192_, 1, v___x_2190_);
lean_closure_set(v___f_2192_, 2, v_toBind_2188_);
lean_closure_set(v___f_2192_, 3, v_eq_2185_);
lean_closure_set(v___f_2192_, 4, v_inst_2184_);
v___f_2193_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2189_);
v_sz_2194_ = lean_array_size(v_xs_2186_);
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2184_, v_xs_2186_, v___f_2192_, v_sz_2194_, v___x_2195_, v_ret_2191_);
v___x_2197_ = lean_apply_4(v_toBind_2188_, lean_box(0), lean_box(0), v___x_2196_, v___f_2193_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2198_, lean_object* v_00_u03b1_2199_, lean_object* v_inst_2200_, lean_object* v_eq_2201_, lean_object* v_xs_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2200_, v_eq_2201_, v_xs_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_bs_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2207_ == 0)
{
return v_bs_2206_;
}
else
{
lean_object* v_v_2208_; lean_object* v_indGroupInst_2209_; lean_object* v___x_2210_; lean_object* v_bs_x27_2211_; size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v_v_2208_ = lean_array_uget_borrowed(v_bs_2206_, v_i_2205_);
v_indGroupInst_2209_ = lean_ctor_get(v_v_2208_, 4);
lean_inc_ref(v_indGroupInst_2209_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v_bs_x27_2211_ = lean_array_uset(v_bs_2206_, v_i_2205_, v___x_2210_);
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_add(v_i_2205_, v___x_2212_);
v___x_2214_ = lean_array_uset(v_bs_x27_2211_, v_i_2205_, v_indGroupInst_2209_);
v_i_2205_ = v___x_2213_;
v_bs_2206_ = v___x_2214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2216_, lean_object* v_i_2217_, lean_object* v_bs_2218_){
_start:
{
size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; lean_object* v_res_2221_; 
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2216_);
lean_dec(v_sz_2216_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2218_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2222_, lean_object* v_a_2223_, lean_object* v_as_2224_, size_t v_i_2225_, size_t v_stop_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v___x_2232_; 
v___x_2232_ = lean_usize_dec_eq(v_i_2225_, v_stop_2226_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_array_uget_borrowed(v_as_2224_, v_i_2225_);
lean_inc_ref(v_eq_2222_);
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2227_);
lean_inc(v_a_2223_);
lean_inc(v___x_2233_);
v___x_2234_ = lean_apply_7(v_eq_2222_, v___x_2233_, v_a_2223_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, lean_box(0));
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2246_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_unbox(v_a_2235_);
if (v___x_2239_ == 0)
{
size_t v___x_2240_; size_t v___x_2241_; 
lean_del_object(v___x_2237_);
lean_dec(v_a_2235_);
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2225_, v___x_2240_);
v_i_2225_ = v___x_2241_;
goto _start;
}
else
{
lean_object* v___x_2244_; 
lean_dec(v_a_2223_);
lean_dec_ref(v_eq_2222_);
if (v_isShared_2238_ == 0)
{
v___x_2244_ = v___x_2237_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2235_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_dec(v_a_2223_);
lean_dec_ref(v_eq_2222_);
return v___x_2234_;
}
}
else
{
uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec(v_a_2223_);
lean_dec_ref(v_eq_2222_);
v___x_2247_ = 0;
v___x_2248_ = lean_box(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2250_, lean_object* v_a_2251_, lean_object* v_as_2252_, lean_object* v_i_2253_, lean_object* v_stop_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2254_);
lean_dec(v_stop_2254_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2250_, v_a_2251_, v_as_2252_, v_i_boxed_2260_, v_stop_boxed_2261_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v_as_2252_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2263_, lean_object* v_a_2264_, uint8_t v_____do__lift_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
if (v_____do__lift_2265_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_array_push(v_b_2263_, v_a_2264_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v_a_2264_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_b_2263_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2276_, lean_object* v_a_2277_, lean_object* v_____do__lift_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_____do__lift_1292__boxed_2284_; lean_object* v_res_2285_; 
v_____do__lift_1292__boxed_2284_ = lean_unbox(v_____do__lift_2278_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2276_, v_a_2277_, v_____do__lift_1292__boxed_2284_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2286_, lean_object* v_as_2287_, size_t v_sz_2288_, size_t v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_a_2297_; lean_object* v___y_2302_; uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_lt(v_i_2289_, v_sz_2288_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
lean_dec_ref(v_eq_2286_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_b_2290_);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; lean_object* v_a_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v_a_2324_ = lean_array_uget_borrowed(v_as_2287_, v_i_2289_);
v___x_2325_ = lean_array_get_size(v_b_2290_);
v___x_2326_ = lean_nat_dec_lt(v___x_2323_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_inc(v_a_2324_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2290_, v_a_2324_, v___x_2326_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
v___y_2302_ = v___x_2327_;
goto v___jp_2301_;
}
else
{
if (v___x_2326_ == 0)
{
lean_object* v___x_2328_; 
lean_inc(v_a_2324_);
v___x_2328_ = lean_array_push(v_b_2290_, v_a_2324_);
v_a_2297_ = v___x_2328_;
goto v___jp_2296_;
}
else
{
size_t v___x_2329_; size_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2329_ = ((size_t)0ULL);
v___x_2330_ = lean_usize_of_nat(v___x_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_eq_2286_);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2286_, v_a_2324_, v_b_2290_, v___x_2329_, v___x_2330_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
lean_inc(v_a_2324_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2290_, v_a_2324_, v___x_2333_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
v___y_2302_ = v___x_2334_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_b_2290_);
lean_dec_ref(v_eq_2286_);
v_a_2335_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2331_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
v___jp_2296_:
{
size_t v___x_2298_; size_t v___x_2299_; 
v___x_2298_ = ((size_t)1ULL);
v___x_2299_ = lean_usize_add(v_i_2289_, v___x_2298_);
v_i_2289_ = v___x_2299_;
v_b_2290_ = v_a_2297_;
goto _start;
}
v___jp_2301_:
{
if (lean_obj_tag(v___y_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2312_; 
v_a_2303_ = lean_ctor_get(v___y_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___y_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2305_ = v___y_2302_;
v_isShared_2306_ = v_isSharedCheck_2312_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___y_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2312_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
if (lean_obj_tag(v_a_2303_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; 
lean_dec_ref(v_eq_2286_);
v_a_2307_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v_a_2303_);
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
lean_object* v_a_2311_; 
lean_del_object(v___x_2305_);
v_a_2311_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v_a_2303_);
v_a_2297_ = v_a_2311_;
goto v___jp_2296_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_eq_2286_);
v_a_2313_ = lean_ctor_get(v___y_2302_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___y_2302_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___y_2302_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___y_2302_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2343_, lean_object* v_as_2344_, lean_object* v_sz_2345_, lean_object* v_i_2346_, lean_object* v_b_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
size_t v_sz_boxed_2353_; size_t v_i_boxed_2354_; lean_object* v_res_2355_; 
v_sz_boxed_2353_ = lean_unbox_usize(v_sz_2345_);
lean_dec(v_sz_2345_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2343_, v_as_2344_, v_sz_boxed_2353_, v_i_boxed_2354_, v_b_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec_ref(v_as_2344_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2356_, lean_object* v_xs_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_ret_2363_; size_t v_sz_2364_; size_t v___x_2365_; lean_object* v___x_2366_; 
v_ret_2363_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2364_ = lean_array_size(v_xs_2357_);
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2356_, v_xs_2357_, v_sz_2364_, v___x_2365_, v_ret_2363_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2367_, lean_object* v_xs_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2367_, v_xs_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v_xs_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2383_ = lean_array_size(v_recArgInfos_2376_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2383_, v___x_2384_, v_recArgInfos_2376_);
v___x_2386_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2382_, v___x_2385_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec_ref(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2394_, lean_object* v_eq_2395_, lean_object* v_xs_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2395_, v_xs_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2403_, lean_object* v_eq_2404_, lean_object* v_xs_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2403_, v_eq_2404_, v_xs_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_xs_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2412_, lean_object* v_eq_2413_, lean_object* v_a_2414_, lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2413_, v_a_2414_, v_as_2415_, v_i_2416_, v_stop_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2424_, lean_object* v_eq_2425_, lean_object* v_a_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_stop_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
size_t v_i_boxed_2435_; size_t v_stop_boxed_2436_; lean_object* v_res_2437_; 
v_i_boxed_2435_ = lean_unbox_usize(v_i_2428_);
lean_dec(v_i_2428_);
v_stop_boxed_2436_ = lean_unbox_usize(v_stop_2429_);
lean_dec(v_stop_2429_);
v_res_2437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2424_, v_eq_2425_, v_a_2426_, v_as_2427_, v_i_boxed_2435_, v_stop_boxed_2436_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_as_2427_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2438_, lean_object* v_eq_2439_, lean_object* v_as_2440_, size_t v_sz_2441_, size_t v_i_2442_, lean_object* v_b_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2439_, v_as_2440_, v_sz_2441_, v_i_2442_, v_b_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_eq_2451_, lean_object* v_as_2452_, lean_object* v_sz_2453_, lean_object* v_i_2454_, lean_object* v_b_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2453_);
lean_dec(v_sz_2453_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2454_);
lean_dec(v_i_2454_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2450_, v_eq_2451_, v_as_2452_, v_sz_boxed_2461_, v_i_boxed_2462_, v_b_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_as_2452_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = l_Lean_Expr_hasMVar(v_e_2464_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_e_2464_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v_mctx_2470_; lean_object* v___x_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v_cache_2475_; lean_object* v_zetaDeltaFVarIds_2476_; lean_object* v_postponed_2477_; lean_object* v_diag_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2487_; 
v___x_2469_ = lean_st_ref_get(v___y_2465_);
v_mctx_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_mctx_2470_);
lean_dec(v___x_2469_);
v___x_2471_ = l_Lean_instantiateMVarsCore(v_mctx_2470_, v_e_2464_);
v_fst_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2471_);
v___x_2474_ = lean_st_ref_take(v___y_2465_);
v_cache_2475_ = lean_ctor_get(v___x_2474_, 1);
v_zetaDeltaFVarIds_2476_ = lean_ctor_get(v___x_2474_, 2);
v_postponed_2477_ = lean_ctor_get(v___x_2474_, 3);
v_diag_2478_ = lean_ctor_get(v___x_2474_, 4);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2474_, 0);
lean_dec(v_unused_2488_);
v___x_2480_ = v___x_2474_;
v_isShared_2481_ = v_isSharedCheck_2487_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_diag_2478_);
lean_inc(v_postponed_2477_);
lean_inc(v_zetaDeltaFVarIds_2476_);
lean_inc(v_cache_2475_);
lean_dec(v___x_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2487_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_snd_2473_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_snd_2473_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_cache_2475_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_zetaDeltaFVarIds_2476_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_postponed_2477_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_diag_2478_);
v___x_2483_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_st_ref_set(v___y_2465_, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_fst_2472_);
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2489_, v___y_2490_);
lean_dec(v___y_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2493_, v___y_2495_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2506_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2509_ = lean_unsigned_to_nat(113u);
v___x_2510_ = lean_unsigned_to_nat(214u);
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2513_ = l_mkPanicMessageWithDecl(v___x_2512_, v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2514_, size_t v_sz_2515_, size_t v_i_2516_, lean_object* v_bs_2517_){
_start:
{
uint8_t v___x_2518_; 
v___x_2518_ = lean_usize_dec_lt(v_i_2516_, v_sz_2515_);
if (v___x_2518_ == 0)
{
return v_bs_2517_;
}
else
{
lean_object* v_v_2519_; lean_object* v___x_2520_; lean_object* v_bs_x27_2521_; lean_object* v___y_2523_; lean_object* v___x_2528_; 
v_v_2519_ = lean_array_uget(v_bs_2517_, v_i_2516_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v_bs_x27_2521_ = lean_array_uset(v_bs_2517_, v_i_2516_, v___x_2520_);
v___x_2528_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2514_, v_v_2519_);
lean_dec(v_v_2519_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2530_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2529_);
v___y_2523_ = v___x_2530_;
goto v___jp_2522_;
}
else
{
lean_object* v_val_2531_; 
v_val_2531_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_val_2531_);
lean_dec_ref(v___x_2528_);
v___y_2523_ = v_val_2531_;
goto v___jp_2522_;
}
v___jp_2522_:
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2516_, v___x_2524_);
v___x_2526_ = lean_array_uset(v_bs_x27_2521_, v_i_2516_, v___y_2523_);
v_i_2516_ = v___x_2525_;
v_bs_2517_ = v___x_2526_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2532_, lean_object* v_sz_2533_, lean_object* v_i_2534_, lean_object* v_bs_2535_){
_start:
{
size_t v_sz_boxed_2536_; size_t v_i_boxed_2537_; lean_object* v_res_2538_; 
v_sz_boxed_2536_ = lean_unbox_usize(v_sz_2533_);
lean_dec(v_sz_2533_);
v_i_boxed_2537_ = lean_unbox_usize(v_i_2534_);
lean_dec(v_i_2534_);
v_res_2538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2532_, v_sz_boxed_2536_, v_i_boxed_2537_, v_bs_2535_);
lean_dec_ref(v___x_2532_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2539_, size_t v_i_2540_, lean_object* v_bs_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_usize_dec_lt(v_i_2540_, v_sz_2539_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_bs_2541_);
return v___x_2548_;
}
else
{
lean_object* v_v_2549_; lean_object* v___x_2550_; 
v_v_2549_ = lean_array_uget_borrowed(v_bs_2541_, v_i_2540_);
lean_inc(v_v_2549_);
v___x_2550_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2549_, v___y_2543_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; lean_object* v_bs_x27_2553_; size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v_bs_x27_2553_ = lean_array_uset(v_bs_2541_, v_i_2540_, v___x_2552_);
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_add(v_i_2540_, v___x_2554_);
v___x_2556_ = lean_array_uset(v_bs_x27_2553_, v_i_2540_, v_a_2551_);
v_i_2540_ = v___x_2555_;
v_bs_2541_ = v___x_2556_;
goto _start;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec_ref(v_bs_2541_);
v_a_2558_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2550_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2550_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2566_, lean_object* v_i_2567_, lean_object* v_bs_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
size_t v_sz_boxed_2574_; size_t v_i_boxed_2575_; lean_object* v_res_2576_; 
v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2575_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2574_, v_i_boxed_2575_, v_bs_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2576_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2577_, lean_object* v___x_2578_, lean_object* v_as_2579_, size_t v_i_2580_, size_t v_stop_2581_){
_start:
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_usize_dec_eq(v_i_2580_, v_stop_2581_);
if (v___x_2582_ == 0)
{
uint8_t v___x_2583_; uint8_t v___y_2585_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2583_ = 1;
v___x_2589_ = lean_array_uget_borrowed(v_as_2579_, v_i_2580_);
v___x_2590_ = l_Lean_Expr_isFVar(v___x_2589_);
if (v___x_2590_ == 0)
{
v___y_2585_ = v_a_2577_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_nat_dec_eq(v___x_2578_, v___x_2591_);
v___y_2585_ = v___x_2592_;
goto v___jp_2584_;
}
v___jp_2584_:
{
if (v___y_2585_ == 0)
{
size_t v___x_2586_; size_t v___x_2587_; 
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2580_, v___x_2586_);
v_i_2580_ = v___x_2587_;
goto _start;
}
else
{
return v___x_2583_;
}
}
}
else
{
uint8_t v___x_2593_; 
v___x_2593_ = 0;
return v___x_2593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2594_, lean_object* v___x_2595_, lean_object* v_as_2596_, lean_object* v_i_2597_, lean_object* v_stop_2598_){
_start:
{
uint8_t v_a_9818__boxed_2599_; size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_a_9818__boxed_2599_ = lean_unbox(v_a_2594_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2598_);
lean_dec(v_stop_2598_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9818__boxed_2599_, v___x_2595_, v_as_2596_, v_i_boxed_2600_, v_stop_boxed_2601_);
lean_dec_ref(v_as_2596_);
lean_dec(v___x_2595_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2604_, lean_object* v___x_2605_, lean_object* v_ys_2606_, lean_object* v___x_2607_, lean_object* v_recArgInfo_2608_, lean_object* v___x_2609_, lean_object* v_group_2610_, lean_object* v_as_2611_, size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_b_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_a_2621_; uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_lt(v_i_2613_, v_sz_2612_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2614_);
return v___x_2626_;
}
else
{
lean_object* v_snd_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2785_; 
v_snd_2627_ = lean_ctor_get(v_b_2614_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_b_2614_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_b_2614_, 0);
lean_dec(v_unused_2786_);
v___x_2629_ = v_b_2614_;
v_isShared_2630_ = v_isSharedCheck_2785_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_snd_2627_);
lean_dec(v_b_2614_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2785_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_next_2631_; lean_object* v_upperBound_2632_; lean_object* v___x_2633_; 
v_next_2631_ = lean_ctor_get(v_snd_2627_, 0);
lean_inc(v_next_2631_);
v_upperBound_2632_ = lean_ctor_get(v_snd_2627_, 1);
v___x_2633_ = lean_box(0);
if (lean_obj_tag(v_next_2631_) == 0)
{
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
goto v___jp_2634_;
}
else
{
lean_object* v_val_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2784_; 
v_val_2639_ = lean_ctor_get(v_next_2631_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_next_2631_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2641_ = v_next_2631_;
v_isShared_2642_ = v_isSharedCheck_2784_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_val_2639_);
lean_dec(v_next_2631_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2784_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_nat_dec_lt(v_val_2639_, v_upperBound_2632_);
if (v___x_2643_ == 0)
{
lean_del_object(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
goto v___jp_2634_;
}
else
{
lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2781_; 
lean_inc(v_upperBound_2632_);
lean_del_object(v___x_2629_);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_snd_2627_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2782_ = lean_ctor_get(v_snd_2627_, 1);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_snd_2627_, 0);
lean_dec(v_unused_2783_);
v___x_2645_ = v_snd_2627_;
v_isShared_2646_ = v_isSharedCheck_2781_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v_snd_2627_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2781_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; 
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc_ref(v___x_2604_);
v___x_2647_ = lean_infer_type(v___x_2604_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = l_Lean_Meta_whnfD(v_a_2648_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v_a_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
v_a_2651_ = lean_array_uget_borrowed(v_as_2611_, v_i_2613_);
v___x_2652_ = 0;
lean_inc(v_a_2651_);
v___x_2653_ = l_Lean_Meta_forallMetaTelescope(v_a_2651_, v___x_2652_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_snd_2655_; lean_object* v_fst_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2756_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2653_);
v_snd_2655_ = lean_ctor_get(v_a_2654_, 1);
v_fst_2656_ = lean_ctor_get(v_a_2654_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2658_ = v_a_2654_;
v_isShared_2659_ = v_isSharedCheck_2756_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2655_);
lean_inc(v_fst_2656_);
lean_dec(v_a_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2756_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_snd_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2754_; 
v_snd_2660_ = lean_ctor_get(v_snd_2655_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_snd_2655_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_snd_2655_, 0);
lean_dec(v_unused_2755_);
v___x_2662_ = v_snd_2655_;
v_isShared_2663_ = v_isSharedCheck_2754_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_snd_2660_);
lean_dec(v_snd_2655_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2754_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2660_, v_a_2650_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_add(v_val_2639_, v___x_2666_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2667_);
v___x_2669_ = v___x_2641_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2669_);
v___x_2671_ = v___x_2645_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_upperBound_2632_);
v___x_2671_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_unbox(v_a_2665_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2674_; 
lean_dec(v_a_2665_);
lean_del_object(v___x_2658_);
lean_dec(v_fst_2656_);
lean_dec(v_val_2639_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2671_);
lean_ctor_set(v___x_2662_, 0, v___x_2633_);
v___x_2674_ = v___x_2662_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2671_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v_a_2621_ = v___x_2674_;
goto v___jp_2620_;
}
}
else
{
size_t v_sz_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v_sz_2676_ = lean_array_size(v_fst_2656_);
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2676_, v___x_2677_, v_fst_2656_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_nat_dec_eq(v___x_2605_, v___x_2684_);
v___x_2731_ = lean_array_get_size(v_a_2679_);
v___x_2732_ = lean_nat_dec_lt(v___x_2684_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_dec(v_a_2665_);
goto v___jp_2686_;
}
else
{
if (v___x_2732_ == 0)
{
lean_dec(v_a_2665_);
goto v___jp_2686_;
}
else
{
size_t v___x_2733_; uint8_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = lean_usize_of_nat(v___x_2731_);
v___x_2734_ = lean_unbox(v_a_2665_);
lean_dec(v_a_2665_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2734_, v___x_2605_, v_a_2679_, v___x_2677_, v___x_2733_);
if (v___x_2735_ == 0)
{
goto v___jp_2686_;
}
else
{
if (v___x_2685_ == 0)
{
lean_dec(v_a_2679_);
lean_del_object(v___x_2658_);
lean_dec(v_val_2639_);
goto v___jp_2680_;
}
else
{
goto v___jp_2686_;
}
}
}
}
v___jp_2680_:
{
lean_object* v___x_2682_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2671_);
lean_ctor_set(v___x_2662_, 0, v___x_2633_);
v___x_2682_ = v___x_2662_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2671_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
v_a_2621_ = v___x_2682_;
goto v___jp_2620_;
}
}
v___jp_2686_:
{
if (v___x_2685_ == 0)
{
uint8_t v___x_2687_; 
lean_del_object(v___x_2662_);
v___x_2687_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2679_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2689_; 
lean_dec(v_a_2679_);
lean_dec(v_val_2639_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2671_);
lean_ctor_set(v___x_2658_, 0, v___x_2633_);
v___x_2689_ = v___x_2658_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2671_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2621_ = v___x_2689_;
goto v___jp_2620_;
}
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2606_, v_a_2679_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2722_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2722_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2722_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_object* v___x_2697_; 
lean_dec_ref(v_a_2692_);
lean_del_object(v___x_2694_);
lean_dec(v_a_2679_);
lean_dec(v_val_2639_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2671_);
lean_ctor_set(v___x_2658_, 0, v___x_2633_);
v___x_2697_ = v___x_2658_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2671_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
v_a_2621_ = v___x_2697_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_fnName_2699_; lean_object* v_fixedParamPerm_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_a_2692_);
lean_dec_ref(v___x_2604_);
v_fnName_2699_ = lean_ctor_get(v_recArgInfo_2608_, 0);
v_fixedParamPerm_2700_ = lean_ctor_get(v_recArgInfo_2608_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_recArgInfo_2608_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; lean_object* v_unused_2719_; lean_object* v_unused_2720_; lean_object* v_unused_2721_; 
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2608_, 5);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_recArgInfo_2608_, 4);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_recArgInfo_2608_, 3);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_recArgInfo_2608_, 2);
lean_dec(v_unused_2721_);
v___x_2702_ = v_recArgInfo_2608_;
v_isShared_2703_ = v_isSharedCheck_2717_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_fixedParamPerm_2700_);
lean_inc(v_fnName_2699_);
lean_dec(v_recArgInfo_2608_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2717_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
size_t v_sz_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v_sz_2704_ = lean_array_size(v_a_2679_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2607_, v_sz_2704_, v___x_2677_, v_a_2679_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 5, v_val_2639_);
lean_ctor_set(v___x_2702_, 4, v_group_2610_);
lean_ctor_set(v___x_2702_, 3, v___x_2705_);
lean_ctor_set(v___x_2702_, 2, v___x_2609_);
v___x_2707_ = v___x_2702_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_fnName_2699_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_fixedParamPerm_2700_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2716_, 4, v_group_2610_);
lean_ctor_set(v_reuseFailAlloc_2716_, 5, v_val_2639_);
v___x_2707_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2671_);
lean_ctor_set(v___x_2658_, 0, v___x_2709_);
v___x_2711_ = v___x_2658_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2671_);
v___x_2711_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2711_);
v___x_2713_ = v___x_2694_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_a_2679_);
lean_dec_ref(v___x_2671_);
lean_del_object(v___x_2658_);
lean_dec(v_val_2639_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2723_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2691_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2691_);
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
else
{
lean_dec(v_a_2679_);
lean_del_object(v___x_2658_);
lean_dec(v_val_2639_);
goto v___jp_2680_;
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v___x_2671_);
lean_dec(v_a_2665_);
lean_del_object(v___x_2662_);
lean_del_object(v___x_2658_);
lean_dec(v_val_2639_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2736_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2678_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2678_);
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
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_del_object(v___x_2662_);
lean_del_object(v___x_2658_);
lean_dec(v_fst_2656_);
lean_del_object(v___x_2645_);
lean_del_object(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec(v_upperBound_2632_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2746_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2664_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2664_);
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
lean_dec(v_a_2650_);
lean_del_object(v___x_2645_);
lean_del_object(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec(v_upperBound_2632_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2757_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2653_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2653_);
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
lean_del_object(v___x_2645_);
lean_del_object(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec(v_upperBound_2632_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2765_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2649_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2649_);
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
lean_del_object(v___x_2645_);
lean_del_object(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec(v_upperBound_2632_);
lean_dec_ref(v_group_2610_);
lean_dec(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2773_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2647_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2647_);
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
v___jp_2634_:
{
lean_object* v___x_2636_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2633_);
v___x_2636_ = v___x_2629_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_snd_2627_);
v___x_2636_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
}
}
v___jp_2620_:
{
size_t v___x_2622_; size_t v___x_2623_; 
v___x_2622_ = ((size_t)1ULL);
v___x_2623_ = lean_usize_add(v_i_2613_, v___x_2622_);
v_i_2613_ = v___x_2623_;
v_b_2614_ = v_a_2621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_ys_2789_, lean_object* v___x_2790_, lean_object* v_recArgInfo_2791_, lean_object* v___x_2792_, lean_object* v_group_2793_, lean_object* v_as_2794_, lean_object* v_sz_2795_, lean_object* v_i_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2795_);
lean_dec(v_sz_2795_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2787_, v___x_2788_, v_ys_2789_, v___x_2790_, v_recArgInfo_2791_, v___x_2792_, v_group_2793_, v_as_2794_, v_sz_boxed_2803_, v_i_boxed_2804_, v_b_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v_as_2794_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_ys_2789_);
lean_dec(v___x_2788_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v_ys_2809_, lean_object* v_recArgInfo_2810_, lean_object* v___x_2811_, lean_object* v_group_2812_, lean_object* v_as_2813_, size_t v_sz_2814_, size_t v_i_2815_, lean_object* v_b_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_a_2823_; uint8_t v___x_2827_; 
v___x_2827_ = lean_usize_dec_lt(v_i_2815_, v_sz_2814_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_b_2816_);
return v___x_2828_;
}
else
{
lean_object* v_snd_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2987_; 
v_snd_2829_ = lean_ctor_get(v_b_2816_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_b_2816_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_b_2816_, 0);
lean_dec(v_unused_2988_);
v___x_2831_ = v_b_2816_;
v_isShared_2832_ = v_isSharedCheck_2987_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_snd_2829_);
lean_dec(v_b_2816_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2987_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_next_2833_; lean_object* v_upperBound_2834_; lean_object* v___x_2835_; 
v_next_2833_ = lean_ctor_get(v_snd_2829_, 0);
lean_inc(v_next_2833_);
v_upperBound_2834_ = lean_ctor_get(v_snd_2829_, 1);
v___x_2835_ = lean_box(0);
if (lean_obj_tag(v_next_2833_) == 0)
{
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
goto v___jp_2836_;
}
else
{
lean_object* v_val_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2986_; 
v_val_2841_ = lean_ctor_get(v_next_2833_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_next_2833_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2843_ = v_next_2833_;
v_isShared_2844_ = v_isSharedCheck_2986_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_val_2841_);
lean_dec(v_next_2833_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2986_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_nat_dec_lt(v_val_2841_, v_upperBound_2834_);
if (v___x_2845_ == 0)
{
lean_del_object(v___x_2843_);
lean_dec(v_val_2841_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
goto v___jp_2836_;
}
else
{
lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2983_; 
lean_inc(v_upperBound_2834_);
lean_del_object(v___x_2831_);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_snd_2829_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; lean_object* v_unused_2985_; 
v_unused_2984_ = lean_ctor_get(v_snd_2829_, 1);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_snd_2829_, 0);
lean_dec(v_unused_2985_);
v___x_2847_ = v_snd_2829_;
v_isShared_2848_ = v_isSharedCheck_2983_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v_snd_2829_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2983_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; 
lean_inc(v___y_2820_);
lean_inc_ref(v___y_2819_);
lean_inc(v___y_2818_);
lean_inc_ref(v___y_2817_);
lean_inc_ref(v___x_2806_);
v___x_2849_ = lean_infer_type(v___x_2806_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Lean_Meta_whnfD(v_a_2850_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v_a_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v_a_2853_ = lean_array_uget_borrowed(v_as_2813_, v_i_2815_);
v___x_2854_ = 0;
lean_inc(v_a_2853_);
v___x_2855_ = l_Lean_Meta_forallMetaTelescope(v_a_2853_, v___x_2854_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v_snd_2857_; lean_object* v_fst_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2958_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v_snd_2857_ = lean_ctor_get(v_a_2856_, 1);
v_fst_2858_ = lean_ctor_get(v_a_2856_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2856_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2860_ = v_a_2856_;
v_isShared_2861_ = v_isSharedCheck_2958_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_snd_2857_);
lean_inc(v_fst_2858_);
lean_dec(v_a_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2958_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_snd_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2956_; 
v_snd_2862_ = lean_ctor_get(v_snd_2857_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_snd_2857_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v_snd_2857_, 0);
lean_dec(v_unused_2957_);
v___x_2864_ = v_snd_2857_;
v_isShared_2865_ = v_isSharedCheck_2956_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_snd_2862_);
lean_dec(v_snd_2857_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2956_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2862_, v_a_2852_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_val_2841_, v___x_2868_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2869_);
v___x_2871_ = v___x_2843_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2871_);
v___x_2873_ = v___x_2847_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_upperBound_2834_);
v___x_2873_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_unbox(v_a_2867_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2876_; 
lean_dec(v_a_2867_);
lean_del_object(v___x_2860_);
lean_dec(v_fst_2858_);
lean_dec(v_val_2841_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v___x_2873_);
lean_ctor_set(v___x_2864_, 0, v___x_2835_);
v___x_2876_ = v___x_2864_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2873_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
v_a_2823_ = v___x_2876_;
goto v___jp_2822_;
}
}
else
{
size_t v_sz_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
v_sz_2878_ = lean_array_size(v_fst_2858_);
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2878_, v___x_2879_, v_fst_2858_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_nat_dec_eq(v___x_2807_, v___x_2886_);
v___x_2933_ = lean_array_get_size(v_a_2881_);
v___x_2934_ = lean_nat_dec_lt(v___x_2886_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_dec(v_a_2867_);
goto v___jp_2888_;
}
else
{
if (v___x_2934_ == 0)
{
lean_dec(v_a_2867_);
goto v___jp_2888_;
}
else
{
size_t v___x_2935_; uint8_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = lean_usize_of_nat(v___x_2933_);
v___x_2936_ = lean_unbox(v_a_2867_);
lean_dec(v_a_2867_);
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2936_, v___x_2807_, v_a_2881_, v___x_2879_, v___x_2935_);
if (v___x_2937_ == 0)
{
goto v___jp_2888_;
}
else
{
if (v___x_2887_ == 0)
{
lean_dec(v_a_2881_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2841_);
goto v___jp_2882_;
}
else
{
goto v___jp_2888_;
}
}
}
}
v___jp_2882_:
{
lean_object* v___x_2884_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v___x_2873_);
lean_ctor_set(v___x_2864_, 0, v___x_2835_);
v___x_2884_ = v___x_2864_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2873_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_a_2823_ = v___x_2884_;
goto v___jp_2822_;
}
}
v___jp_2888_:
{
if (v___x_2887_ == 0)
{
uint8_t v___x_2889_; 
lean_del_object(v___x_2864_);
v___x_2889_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2881_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_a_2881_);
lean_dec(v_val_2841_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2873_);
lean_ctor_set(v___x_2860_, 0, v___x_2835_);
v___x_2891_ = v___x_2860_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2873_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
v_a_2823_ = v___x_2891_;
goto v___jp_2822_;
}
}
else
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2809_, v_a_2881_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2924_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2924_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2924_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
if (lean_obj_tag(v_a_2894_) == 1)
{
lean_object* v___x_2899_; 
lean_dec_ref(v_a_2894_);
lean_del_object(v___x_2896_);
lean_dec(v_a_2881_);
lean_dec(v_val_2841_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2873_);
lean_ctor_set(v___x_2860_, 0, v___x_2835_);
v___x_2899_ = v___x_2860_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2873_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2823_ = v___x_2899_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_fnName_2901_; lean_object* v_fixedParamPerm_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2894_);
lean_dec_ref(v___x_2806_);
v_fnName_2901_ = lean_ctor_get(v_recArgInfo_2810_, 0);
v_fixedParamPerm_2902_ = lean_ctor_get(v_recArgInfo_2810_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_recArgInfo_2810_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; 
v_unused_2920_ = lean_ctor_get(v_recArgInfo_2810_, 5);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_recArgInfo_2810_, 4);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_recArgInfo_2810_, 3);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_recArgInfo_2810_, 2);
lean_dec(v_unused_2923_);
v___x_2904_ = v_recArgInfo_2810_;
v_isShared_2905_ = v_isSharedCheck_2919_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_fixedParamPerm_2902_);
lean_inc(v_fnName_2901_);
lean_dec(v_recArgInfo_2810_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2919_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
size_t v_sz_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v_sz_2906_ = lean_array_size(v_a_2881_);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2808_, v_sz_2906_, v___x_2879_, v_a_2881_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 5, v_val_2841_);
lean_ctor_set(v___x_2904_, 4, v_group_2812_);
lean_ctor_set(v___x_2904_, 3, v___x_2907_);
lean_ctor_set(v___x_2904_, 2, v___x_2811_);
v___x_2909_ = v___x_2904_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_fnName_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_fixedParamPerm_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_group_2812_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v_val_2841_);
v___x_2909_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2873_);
lean_ctor_set(v___x_2860_, 0, v___x_2911_);
v___x_2913_ = v___x_2860_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2873_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2913_);
v___x_2915_ = v___x_2896_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2881_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2841_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2925_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2893_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2893_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_dec(v_a_2881_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2841_);
goto v___jp_2882_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v___x_2873_);
lean_dec(v_a_2867_);
lean_del_object(v___x_2864_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2841_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2938_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2880_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2880_);
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
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_del_object(v___x_2864_);
lean_del_object(v___x_2860_);
lean_dec(v_fst_2858_);
lean_del_object(v___x_2847_);
lean_del_object(v___x_2843_);
lean_dec(v_val_2841_);
lean_dec(v_upperBound_2834_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2948_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2866_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2866_);
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
lean_dec(v_a_2852_);
lean_del_object(v___x_2847_);
lean_del_object(v___x_2843_);
lean_dec(v_val_2841_);
lean_dec(v_upperBound_2834_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2959_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2855_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2855_);
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
lean_del_object(v___x_2847_);
lean_del_object(v___x_2843_);
lean_dec(v_val_2841_);
lean_dec(v_upperBound_2834_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2967_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2851_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2851_);
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
lean_del_object(v___x_2847_);
lean_del_object(v___x_2843_);
lean_dec(v_val_2841_);
lean_dec(v_upperBound_2834_);
lean_dec_ref(v_group_2812_);
lean_dec(v___x_2811_);
lean_dec_ref(v_recArgInfo_2810_);
lean_dec_ref(v___x_2806_);
v_a_2975_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2849_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2849_);
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
v___jp_2836_:
{
lean_object* v___x_2838_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2835_);
v___x_2838_ = v___x_2831_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_snd_2829_);
v___x_2838_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
}
}
v___jp_2822_:
{
size_t v___x_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = ((size_t)1ULL);
v___x_2825_ = lean_usize_add(v_i_2815_, v___x_2824_);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2806_, v___x_2807_, v_ys_2809_, v___x_2808_, v_recArgInfo_2810_, v___x_2811_, v_group_2812_, v_as_2813_, v_sz_2814_, v___x_2825_, v_a_2823_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object* v___x_2989_, lean_object* v___x_2990_, lean_object* v___x_2991_, lean_object* v_ys_2992_, lean_object* v_recArgInfo_2993_, lean_object* v___x_2994_, lean_object* v_group_2995_, lean_object* v_as_2996_, lean_object* v_sz_2997_, lean_object* v_i_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
size_t v_sz_boxed_3005_; size_t v_i_boxed_3006_; lean_object* v_res_3007_; 
v_sz_boxed_3005_ = lean_unbox_usize(v_sz_2997_);
lean_dec(v_sz_2997_);
v_i_boxed_3006_ = lean_unbox_usize(v_i_2998_);
lean_dec(v_i_2998_);
v_res_3007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2989_, v___x_2990_, v___x_2991_, v_ys_2992_, v_recArgInfo_2993_, v___x_2994_, v_group_2995_, v_as_2996_, v_sz_boxed_3005_, v_i_boxed_3006_, v_b_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v_as_2996_);
lean_dec_ref(v_ys_2992_);
lean_dec_ref(v___x_2991_);
lean_dec(v___x_2990_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3008_, lean_object* v_xs_3009_, lean_object* v_recArgPos_3010_, lean_object* v_a_3011_, lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v_ys_3014_, lean_object* v_x_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_toIndGroupInfo_3021_; lean_object* v_all_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3061_; 
v_toIndGroupInfo_3021_ = lean_ctor_get(v_group_3008_, 0);
lean_inc_ref(v_toIndGroupInfo_3021_);
v_all_3022_ = lean_ctor_get(v_toIndGroupInfo_3021_, 0);
v___x_3023_ = l_Lean_instInhabitedExpr;
v___x_3024_ = l_Array_append___redArg(v_xs_3009_, v_ys_3014_);
v___x_3025_ = lean_array_get(v___x_3023_, v___x_3024_, v_recArgPos_3010_);
v___x_3026_ = lean_array_get_size(v_all_3022_);
v___x_3027_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3021_);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_toIndGroupInfo_3021_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; lean_object* v_unused_3063_; 
v_unused_3062_ = lean_ctor_get(v_toIndGroupInfo_3021_, 1);
lean_dec(v_unused_3062_);
v_unused_3063_ = lean_ctor_get(v_toIndGroupInfo_3021_, 0);
lean_dec(v_unused_3063_);
v___x_3029_ = v_toIndGroupInfo_3021_;
v_isShared_3030_ = v_isSharedCheck_3061_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v_toIndGroupInfo_3021_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3061_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3026_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3033_ = v___x_3029_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3027_);
v___x_3033_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; size_t v_sz_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3033_);
v_sz_3036_ = lean_array_size(v_a_3011_);
v___x_3037_ = ((size_t)0ULL);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3025_, v___x_3012_, v___x_3024_, v_ys_3014_, v___x_3013_, v_recArgPos_3010_, v_group_3008_, v_a_3011_, v_sz_3036_, v___x_3037_, v___x_3035_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec_ref(v___x_3024_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3051_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3051_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3051_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_fst_3043_; 
v_fst_3043_ = lean_ctor_get(v_a_3039_, 0);
lean_inc(v_fst_3043_);
lean_dec(v_a_3039_);
if (lean_obj_tag(v_fst_3043_) == 0)
{
lean_object* v___x_3045_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3034_);
v___x_3045_ = v___x_3041_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3034_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
else
{
lean_object* v_val_3047_; lean_object* v___x_3049_; 
v_val_3047_ = lean_ctor_get(v_fst_3043_, 0);
lean_inc(v_val_3047_);
lean_dec_ref(v_fst_3043_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v_val_3047_);
v___x_3049_ = v___x_3041_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_val_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3038_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3038_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3064_, lean_object* v_xs_3065_, lean_object* v_recArgPos_3066_, lean_object* v_a_3067_, lean_object* v___x_3068_, lean_object* v___x_3069_, lean_object* v_ys_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3064_, v_xs_3065_, v_recArgPos_3066_, v_a_3067_, v___x_3068_, v___x_3069_, v_ys_3070_, v_x_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_x_3071_);
lean_dec_ref(v_ys_3070_);
lean_dec(v___x_3068_);
lean_dec_ref(v_a_3067_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3078_, lean_object* v_a_3079_, lean_object* v_xs_3080_, lean_object* v_value_3081_, lean_object* v_as_3082_, size_t v_i_3083_, size_t v_stop_3084_, lean_object* v_b_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_a_3092_; lean_object* v_val_3097_; uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_eq(v_i_3083_, v_stop_3084_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v_recArgPos_3101_; lean_object* v_indGroupInst_3102_; lean_object* v___x_3103_; 
v___x_3100_ = lean_array_uget_borrowed(v_as_3082_, v_i_3083_);
v_recArgPos_3101_ = lean_ctor_get(v___x_3100_, 2);
v_indGroupInst_3102_ = lean_ctor_get(v___x_3100_, 4);
lean_inc_ref(v_indGroupInst_3102_);
lean_inc_ref(v_group_3078_);
v___x_3103_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3078_, v_indGroupInst_3102_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; uint8_t v___x_3105_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_array_get_size(v_a_3079_);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___f_3109_; lean_object* v___x_3110_; 
lean_inc(v___x_3100_);
lean_inc_ref(v_a_3079_);
lean_inc(v_recArgPos_3101_);
lean_inc_ref(v_xs_3080_);
lean_inc_ref(v_group_3078_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3109_, 0, v_group_3078_);
lean_closure_set(v___f_3109_, 1, v_xs_3080_);
lean_closure_set(v___f_3109_, 2, v_recArgPos_3101_);
lean_closure_set(v___f_3109_, 3, v_a_3079_);
lean_closure_set(v___f_3109_, 4, v___x_3106_);
lean_closure_set(v___f_3109_, 5, v___x_3100_);
lean_inc_ref(v_value_3081_);
v___x_3110_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3081_, v___f_3109_, v___x_3108_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
if (lean_obj_tag(v_a_3111_) == 0)
{
v_a_3092_ = v_b_3085_;
goto v___jp_3091_;
}
else
{
lean_object* v_val_3112_; 
v_val_3112_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_val_3112_);
lean_dec_ref(v_a_3111_);
v_val_3097_ = v_val_3112_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_b_3085_);
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v_a_3113_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3110_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3110_);
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
v_a_3092_ = v_b_3085_;
goto v___jp_3091_;
}
}
else
{
lean_inc(v___x_3100_);
v_val_3097_ = v___x_3100_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v_b_3085_);
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v_a_3121_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3103_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3103_);
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
lean_object* v___x_3129_; 
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_b_3085_);
return v___x_3129_;
}
v___jp_3091_:
{
size_t v___x_3093_; size_t v___x_3094_; 
v___x_3093_ = ((size_t)1ULL);
v___x_3094_ = lean_usize_add(v_i_3083_, v___x_3093_);
v_i_3083_ = v___x_3094_;
v_b_3085_ = v_a_3092_;
goto _start;
}
v___jp_3096_:
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_array_push(v_b_3085_, v_val_3097_);
v_a_3092_ = v___x_3098_;
goto v___jp_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3130_, lean_object* v_a_3131_, lean_object* v_xs_3132_, lean_object* v_value_3133_, lean_object* v_as_3134_, lean_object* v_i_3135_, lean_object* v_stop_3136_, lean_object* v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
size_t v_i_boxed_3143_; size_t v_stop_boxed_3144_; lean_object* v_res_3145_; 
v_i_boxed_3143_ = lean_unbox_usize(v_i_3135_);
lean_dec(v_i_3135_);
v_stop_boxed_3144_ = lean_unbox_usize(v_stop_3136_);
lean_dec(v_stop_3136_);
v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3130_, v_a_3131_, v_xs_3132_, v_value_3133_, v_as_3134_, v_i_boxed_3143_, v_stop_boxed_3144_, v_b_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v_as_3134_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3146_, lean_object* v_a_3147_, lean_object* v_xs_3148_, lean_object* v_value_3149_, lean_object* v_as_3150_, lean_object* v_start_3151_, lean_object* v_stop_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3159_ = lean_nat_dec_lt(v_start_3151_, v_stop_3152_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref(v_value_3149_);
lean_dec_ref(v_xs_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v_group_3146_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = lean_array_get_size(v_as_3150_);
v___x_3162_ = lean_nat_dec_le(v_stop_3152_, v___x_3161_);
if (v___x_3162_ == 0)
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_nat_dec_lt(v_start_3151_, v___x_3161_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
lean_dec_ref(v_value_3149_);
lean_dec_ref(v_xs_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v_group_3146_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3158_);
return v___x_3164_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_usize_of_nat(v_start_3151_);
v___x_3166_ = lean_usize_of_nat(v___x_3161_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3146_, v_a_3147_, v_xs_3148_, v_value_3149_, v_as_3150_, v___x_3165_, v___x_3166_, v___x_3158_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3167_;
}
}
else
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_usize_of_nat(v_start_3151_);
v___x_3169_ = lean_usize_of_nat(v_stop_3152_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3146_, v_a_3147_, v_xs_3148_, v_value_3149_, v_as_3150_, v___x_3168_, v___x_3169_, v___x_3158_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3171_, lean_object* v_a_3172_, lean_object* v_xs_3173_, lean_object* v_value_3174_, lean_object* v_as_3175_, lean_object* v_start_3176_, lean_object* v_stop_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3171_, v_a_3172_, v_xs_3173_, v_value_3174_, v_as_3175_, v_start_3176_, v_stop_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v_stop_3177_);
lean_dec(v_start_3176_);
lean_dec_ref(v_as_3175_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3184_, lean_object* v_xs_3185_, lean_object* v_value_3186_, lean_object* v_recArgInfos_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3193_; 
lean_inc_ref(v_group_3184_);
v___x_3193_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3184_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = lean_array_get_size(v_recArgInfos_3187_);
v___x_3197_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3184_, v_a_3194_, v_xs_3185_, v_value_3186_, v_recArgInfos_3187_, v___x_3195_, v___x_3196_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
return v___x_3197_;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_value_3186_);
lean_dec_ref(v_xs_3185_);
lean_dec_ref(v_group_3184_);
v_a_3198_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3193_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3193_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3206_, lean_object* v_xs_3207_, lean_object* v_value_3208_, lean_object* v_recArgInfos_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_Elab_Structural_argsInGroup(v_group_3206_, v_xs_3207_, v_value_3208_, v_recArgInfos_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec_ref(v_recArgInfos_3209_);
return v_res_3215_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_unsigned_to_nat(10u);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3219_, lean_object* v_i_3220_, lean_object* v_acc_3221_){
_start:
{
lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = lean_array_get_size(v_xss_3219_);
v___x_3223_ = lean_nat_dec_lt(v_i_3220_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_unsigned_to_nat(1u);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_3224_);
v___x_3226_ = lean_array_push(v___x_3225_, v_acc_3221_);
return v___x_3226_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3227_ = lean_array_fget_borrowed(v_xss_3219_, v_i_3220_);
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3230_ = lean_array_get_size(v___x_3227_);
v___x_3231_ = lean_nat_dec_lt(v___x_3228_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_dec_ref(v_acc_3221_);
return v___x_3229_;
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = lean_nat_dec_le(v___x_3230_, v___x_3230_);
if (v___x_3232_ == 0)
{
if (v___x_3231_ == 0)
{
lean_dec_ref(v_acc_3221_);
return v___x_3229_;
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_usize_of_nat(v___x_3230_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3220_, v_acc_3221_, v_xss_3219_, v___x_3227_, v___x_3233_, v___x_3234_, v___x_3229_);
return v___x_3235_;
}
}
else
{
size_t v___x_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = lean_usize_of_nat(v___x_3230_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3220_, v_acc_3221_, v_xss_3219_, v___x_3227_, v___x_3236_, v___x_3237_, v___x_3229_);
return v___x_3238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3239_, lean_object* v_acc_3240_, lean_object* v_xss_3241_, lean_object* v_as_3242_, size_t v_i_3243_, size_t v_stop_3244_, lean_object* v_b_3245_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_usize_dec_eq(v_i_3243_, v_stop_3244_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; 
v___x_3247_ = lean_array_uget_borrowed(v_as_3242_, v_i_3243_);
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_nat_add(v_i_3239_, v___x_3248_);
lean_inc(v___x_3247_);
lean_inc_ref(v_acc_3240_);
v___x_3250_ = lean_array_push(v_acc_3240_, v___x_3247_);
v___x_3251_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3241_, v___x_3249_, v___x_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = l_Array_append___redArg(v_b_3245_, v___x_3251_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = ((size_t)1ULL);
v___x_3254_ = lean_usize_add(v_i_3243_, v___x_3253_);
v_i_3243_ = v___x_3254_;
v_b_3245_ = v___x_3252_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3240_);
return v_b_3245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3256_, lean_object* v_acc_3257_, lean_object* v_xss_3258_, lean_object* v_as_3259_, lean_object* v_i_3260_, lean_object* v_stop_3261_, lean_object* v_b_3262_){
_start:
{
size_t v_i_boxed_3263_; size_t v_stop_boxed_3264_; lean_object* v_res_3265_; 
v_i_boxed_3263_ = lean_unbox_usize(v_i_3260_);
lean_dec(v_i_3260_);
v_stop_boxed_3264_ = lean_unbox_usize(v_stop_3261_);
lean_dec(v_stop_3261_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3256_, v_acc_3257_, v_xss_3258_, v_as_3259_, v_i_boxed_3263_, v_stop_boxed_3264_, v_b_3262_);
lean_dec_ref(v_as_3259_);
lean_dec_ref(v_xss_3258_);
lean_dec(v_i_3256_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3266_, lean_object* v_i_3267_, lean_object* v_acc_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3266_, v_i_3267_, v_acc_3268_);
lean_dec(v_i_3267_);
lean_dec_ref(v_xss_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3270_, lean_object* v_xss_3271_, lean_object* v_i_3272_, lean_object* v_acc_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3271_, v_i_3272_, v_acc_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3275_, lean_object* v_xss_3276_, lean_object* v_i_3277_, lean_object* v_acc_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3275_, v_xss_3276_, v_i_3277_, v_acc_3278_);
lean_dec(v_i_3277_);
lean_dec_ref(v_xss_3276_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3280_, lean_object* v_i_3281_, lean_object* v_acc_3282_, lean_object* v_xss_3283_, lean_object* v_as_3284_, size_t v_i_3285_, size_t v_stop_3286_, lean_object* v_b_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3281_, v_acc_3282_, v_xss_3283_, v_as_3284_, v_i_3285_, v_stop_3286_, v_b_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_i_3290_, lean_object* v_acc_3291_, lean_object* v_xss_3292_, lean_object* v_as_3293_, lean_object* v_i_3294_, lean_object* v_stop_3295_, lean_object* v_b_3296_){
_start:
{
size_t v_i_boxed_3297_; size_t v_stop_boxed_3298_; lean_object* v_res_3299_; 
v_i_boxed_3297_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_stop_boxed_3298_ = lean_unbox_usize(v_stop_3295_);
lean_dec(v_stop_3295_);
v_res_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3289_, v_i_3290_, v_acc_3291_, v_xss_3292_, v_as_3293_, v_i_boxed_3297_, v_stop_boxed_3298_, v_b_3296_);
lean_dec_ref(v_as_3293_);
lean_dec_ref(v_xss_3292_);
lean_dec(v_i_3290_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3300_, size_t v_i_3301_, size_t v_stop_3302_, lean_object* v_b_3303_){
_start:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_usize_dec_eq(v_i_3301_, v_stop_3302_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; size_t v___x_3308_; size_t v___x_3309_; 
v___x_3305_ = lean_array_uget_borrowed(v_as_3300_, v_i_3301_);
v___x_3306_ = lean_array_get_size(v___x_3305_);
v___x_3307_ = lean_nat_mul(v_b_3303_, v___x_3306_);
lean_dec(v_b_3303_);
v___x_3308_ = ((size_t)1ULL);
v___x_3309_ = lean_usize_add(v_i_3301_, v___x_3308_);
v_i_3301_ = v___x_3309_;
v_b_3303_ = v___x_3307_;
goto _start;
}
else
{
return v_b_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3311_, lean_object* v_i_3312_, lean_object* v_stop_3313_, lean_object* v_b_3314_){
_start:
{
size_t v_i_boxed_3315_; size_t v_stop_boxed_3316_; lean_object* v_res_3317_; 
v_i_boxed_3315_ = lean_unbox_usize(v_i_3312_);
lean_dec(v_i_3312_);
v_stop_boxed_3316_ = lean_unbox_usize(v_stop_3313_);
lean_dec(v_stop_3313_);
v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3311_, v_i_boxed_3315_, v_stop_boxed_3316_, v_b_3314_);
lean_dec_ref(v_as_3311_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___y_3323_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3319_ = lean_unsigned_to_nat(10u);
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_array_get_size(v_xss_3318_);
v___x_3330_ = lean_nat_dec_lt(v___x_3321_, v___x_3329_);
if (v___x_3330_ == 0)
{
v___y_3323_ = v___x_3320_;
goto v___jp_3322_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_le(v___x_3329_, v___x_3329_);
if (v___x_3331_ == 0)
{
if (v___x_3330_ == 0)
{
v___y_3323_ = v___x_3320_;
goto v___jp_3322_;
}
else
{
size_t v___x_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = lean_usize_of_nat(v___x_3329_);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3318_, v___x_3332_, v___x_3333_, v___x_3320_);
v___y_3323_ = v___x_3334_;
goto v___jp_3322_;
}
}
else
{
size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = ((size_t)0ULL);
v___x_3336_ = lean_usize_of_nat(v___x_3329_);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3318_, v___x_3335_, v___x_3336_, v___x_3320_);
v___y_3323_ = v___x_3337_;
goto v___jp_3322_;
}
}
v___jp_3322_:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_nat_dec_lt(v___x_3319_, v___y_3323_);
lean_dec(v___y_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3326_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3318_, v___x_3321_, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_box(0);
return v___x_3328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3338_);
lean_dec_ref(v_xss_3338_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3340_, lean_object* v_xss_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3343_, lean_object* v_xss_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3343_, v_xss_3344_);
lean_dec_ref(v_xss_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3346_, lean_object* v_as_3347_, size_t v_i_3348_, size_t v_stop_3349_, lean_object* v_b_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3347_, v_i_3348_, v_stop_3349_, v_b_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3352_, lean_object* v_as_3353_, lean_object* v_i_3354_, lean_object* v_stop_3355_, lean_object* v_b_3356_){
_start:
{
size_t v_i_boxed_3357_; size_t v_stop_boxed_3358_; lean_object* v_res_3359_; 
v_i_boxed_3357_ = lean_unbox_usize(v_i_3354_);
lean_dec(v_i_3354_);
v_stop_boxed_3358_ = lean_unbox_usize(v_stop_3355_);
lean_dec(v_stop_3355_);
v_res_3359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3352_, v_as_3353_, v_i_boxed_3357_, v_stop_boxed_3358_, v_b_3356_);
lean_dec_ref(v_as_3353_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3360_, size_t v_i_3361_, size_t v_stop_3362_, lean_object* v_b_3363_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_eq(v_i_3361_, v_stop_3362_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; size_t v___x_3367_; size_t v___x_3368_; 
v___x_3365_ = lean_array_uget_borrowed(v_as_3360_, v_i_3361_);
v___x_3366_ = l_Array_append___redArg(v_b_3363_, v___x_3365_);
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_add(v_i_3361_, v___x_3367_);
v_i_3361_ = v___x_3368_;
v_b_3363_ = v___x_3366_;
goto _start;
}
else
{
return v_b_3363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3370_, lean_object* v_i_3371_, lean_object* v_stop_3372_, lean_object* v_b_3373_){
_start:
{
size_t v_i_boxed_3374_; size_t v_stop_boxed_3375_; lean_object* v_res_3376_; 
v_i_boxed_3374_ = lean_unbox_usize(v_i_3371_);
lean_dec(v_i_3371_);
v_stop_boxed_3375_ = lean_unbox_usize(v_stop_3372_);
lean_dec(v_stop_3372_);
v_res_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3370_, v_i_boxed_3374_, v_stop_boxed_3375_, v_b_3373_);
lean_dec_ref(v_as_3370_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
if (lean_obj_tag(v_a_3377_) == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = l_List_reverse___redArg(v_a_3378_);
return v___x_3379_;
}
else
{
lean_object* v_head_3380_; lean_object* v_tail_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3391_; 
v_head_3380_ = lean_ctor_get(v_a_3377_, 0);
v_tail_3381_ = lean_ctor_get(v_a_3377_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3383_ = v_a_3377_;
v_isShared_3384_ = v_isSharedCheck_3391_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_tail_3381_);
lean_inc(v_head_3380_);
lean_dec(v_a_3377_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3391_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3385_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3380_);
v___x_3386_ = l_Lean_MessageData_ofFormat(v___x_3385_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 1, v_a_3378_);
lean_ctor_set(v___x_3383_, 0, v___x_3386_);
v___x_3388_ = v___x_3383_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_a_3378_);
v___x_3388_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
v_a_3377_ = v_tail_3381_;
v_a_3378_ = v___x_3388_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_bs_3394_){
_start:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3395_ == 0)
{
return v_bs_3394_;
}
else
{
lean_object* v_v_3396_; lean_object* v___x_3397_; lean_object* v_bs_x27_3398_; lean_object* v___x_3399_; size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v_v_3396_ = lean_array_uget(v_bs_3394_, v_i_3393_);
v___x_3397_ = lean_unsigned_to_nat(0u);
v_bs_x27_3398_ = lean_array_uset(v_bs_3394_, v_i_3393_, v___x_3397_);
v___x_3399_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3396_);
lean_dec(v_v_3396_);
v___x_3400_ = ((size_t)1ULL);
v___x_3401_ = lean_usize_add(v_i_3393_, v___x_3400_);
v___x_3402_ = lean_array_uset(v_bs_x27_3398_, v_i_3393_, v___x_3399_);
v_i_3393_ = v___x_3401_;
v_bs_3394_ = v___x_3402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_bs_3406_){
_start:
{
size_t v_sz_boxed_3407_; size_t v_i_boxed_3408_; lean_object* v_res_3409_; 
v_sz_boxed_3407_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3408_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3407_, v_i_boxed_3408_, v_bs_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3410_, lean_object* v_as_3411_, size_t v_sz_3412_, size_t v_i_3413_, lean_object* v_b_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3413_, v_sz_3412_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec_ref(v_xs_3410_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3414_);
return v___x_3421_;
}
else
{
lean_object* v_snd_3422_; lean_object* v_snd_3423_; lean_object* v_snd_3424_; lean_object* v_snd_3425_; lean_object* v_fst_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3570_; 
v_snd_3422_ = lean_ctor_get(v_b_3414_, 1);
lean_inc(v_snd_3422_);
v_snd_3423_ = lean_ctor_get(v_snd_3422_, 1);
lean_inc(v_snd_3423_);
v_snd_3424_ = lean_ctor_get(v_snd_3423_, 1);
lean_inc(v_snd_3424_);
v_snd_3425_ = lean_ctor_get(v_snd_3424_, 1);
lean_inc(v_snd_3425_);
v_fst_3426_ = lean_ctor_get(v_b_3414_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_b_3414_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_b_3414_, 1);
lean_dec(v_unused_3571_);
v___x_3428_ = v_b_3414_;
v_isShared_3429_ = v_isSharedCheck_3570_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_fst_3426_);
lean_dec(v_b_3414_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3570_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_fst_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3568_; 
v_fst_3430_ = lean_ctor_get(v_snd_3422_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_snd_3422_, 1);
lean_dec(v_unused_3569_);
v___x_3432_ = v_snd_3422_;
v_isShared_3433_ = v_isSharedCheck_3568_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_fst_3430_);
lean_dec(v_snd_3422_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3568_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_fst_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3566_; 
v_fst_3434_ = lean_ctor_get(v_snd_3423_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_snd_3423_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_snd_3423_, 1);
lean_dec(v_unused_3567_);
v___x_3436_ = v_snd_3423_;
v_isShared_3437_ = v_isSharedCheck_3566_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_fst_3434_);
lean_dec(v_snd_3423_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3566_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_fst_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3564_; 
v_fst_3438_ = lean_ctor_get(v_snd_3424_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_snd_3424_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_snd_3424_, 1);
lean_dec(v_unused_3565_);
v___x_3440_ = v_snd_3424_;
v_isShared_3441_ = v_isSharedCheck_3564_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_fst_3438_);
lean_dec(v_snd_3424_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3564_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_array_3442_; lean_object* v_start_3443_; lean_object* v_stop_3444_; uint8_t v___x_3445_; 
v_array_3442_ = lean_ctor_get(v_snd_3425_, 0);
v_start_3443_ = lean_ctor_get(v_snd_3425_, 1);
v_stop_3444_ = lean_ctor_get(v_snd_3425_, 2);
v___x_3445_ = lean_nat_dec_lt(v_start_3443_, v_stop_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v_xs_3410_);
if (v_isShared_3441_ == 0)
{
v___x_3447_ = v___x_3440_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3425_);
v___x_3447_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3447_);
v___x_3449_ = v___x_3436_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3449_);
v___x_3451_ = v___x_3432_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3451_);
v___x_3453_ = v___x_3428_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
return v___x_3454_;
}
}
}
}
}
else
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3560_; 
lean_inc(v_stop_3444_);
lean_inc(v_start_3443_);
lean_inc_ref(v_array_3442_);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_snd_3425_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3561_ = lean_ctor_get(v_snd_3425_, 2);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_snd_3425_, 1);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_snd_3425_, 0);
lean_dec(v_unused_3563_);
v___x_3460_ = v_snd_3425_;
v_isShared_3461_ = v_isSharedCheck_3560_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v_snd_3425_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3560_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_array_3462_; lean_object* v_start_3463_; lean_object* v_stop_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v_array_3462_ = lean_ctor_get(v_fst_3438_, 0);
v_start_3463_ = lean_ctor_get(v_fst_3438_, 1);
v_stop_3464_ = lean_ctor_get(v_fst_3438_, 2);
v___x_3465_ = lean_array_fget(v_array_3442_, v_start_3443_);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_add(v_start_3443_, v___x_3466_);
lean_dec(v_start_3443_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___x_3467_);
v___x_3469_ = v___x_3460_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_array_3442_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_stop_3444_);
v___x_3469_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
uint8_t v___x_3470_; 
v___x_3470_ = lean_nat_dec_lt(v_start_3463_, v_stop_3464_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3472_; 
lean_dec(v___x_3465_);
lean_dec_ref(v_xs_3410_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3469_);
v___x_3472_ = v___x_3440_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___x_3469_);
v___x_3472_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3472_);
v___x_3474_ = v___x_3436_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3474_);
v___x_3476_ = v___x_3432_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3476_);
v___x_3478_ = v___x_3428_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
return v___x_3479_;
}
}
}
}
}
else
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3555_; 
lean_inc(v_stop_3464_);
lean_inc(v_start_3463_);
lean_inc_ref(v_array_3462_);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_fst_3438_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; lean_object* v_unused_3557_; lean_object* v_unused_3558_; 
v_unused_3556_ = lean_ctor_get(v_fst_3438_, 2);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_fst_3438_, 1);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_fst_3438_, 0);
lean_dec(v_unused_3558_);
v___x_3485_ = v_fst_3438_;
v_isShared_3486_ = v_isSharedCheck_3555_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v_fst_3438_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3555_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v_array_3487_; lean_object* v_start_3488_; lean_object* v_stop_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v_array_3487_ = lean_ctor_get(v_fst_3434_, 0);
v_start_3488_ = lean_ctor_get(v_fst_3434_, 1);
v_stop_3489_ = lean_ctor_get(v_fst_3434_, 2);
v___x_3490_ = lean_array_fget(v_array_3462_, v_start_3463_);
v___x_3491_ = lean_nat_add(v_start_3463_, v___x_3466_);
lean_dec(v_start_3463_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___x_3491_);
v___x_3493_ = v___x_3485_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_array_3462_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_stop_3464_);
v___x_3493_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_nat_dec_lt(v_start_3488_, v_stop_3489_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3496_; 
lean_dec(v___x_3490_);
lean_dec(v___x_3465_);
lean_dec_ref(v_xs_3410_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3469_);
lean_ctor_set(v___x_3440_, 0, v___x_3493_);
v___x_3496_ = v___x_3440_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3469_);
v___x_3496_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3498_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3496_);
v___x_3498_ = v___x_3436_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3498_);
v___x_3500_ = v___x_3432_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_fst_3430_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3500_);
v___x_3502_ = v___x_3428_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
return v___x_3503_;
}
}
}
}
}
else
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3550_; 
lean_inc(v_stop_3489_);
lean_inc(v_start_3488_);
lean_inc_ref(v_array_3487_);
lean_del_object(v___x_3428_);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_fst_3434_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; lean_object* v_unused_3552_; lean_object* v_unused_3553_; 
v_unused_3551_ = lean_ctor_get(v_fst_3434_, 2);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_fst_3434_, 1);
lean_dec(v_unused_3552_);
v_unused_3553_ = lean_ctor_get(v_fst_3434_, 0);
lean_dec(v_unused_3553_);
v___x_3509_ = v_fst_3434_;
v_isShared_3510_ = v_isSharedCheck_3550_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v_fst_3434_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3550_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3511_ = lean_array_uget_borrowed(v_as_3411_, v_i_3413_);
v___x_3512_ = lean_array_fget_borrowed(v_array_3487_, v_start_3488_);
lean_inc(v___x_3512_);
lean_inc_ref(v_xs_3410_);
lean_inc(v_a_3511_);
v___x_3513_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3511_, v___x_3465_, v_xs_3410_, v___x_3512_, v___x_3490_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v_fst_3515_; lean_object* v_snd_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3541_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
v_fst_3515_ = lean_ctor_get(v_a_3514_, 0);
v_snd_3516_ = lean_ctor_get(v_a_3514_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3518_ = v_a_3514_;
v_isShared_3519_ = v_isSharedCheck_3541_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_snd_3516_);
lean_inc(v_fst_3515_);
lean_dec(v_a_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3541_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = lean_nat_add(v_start_3488_, v___x_3466_);
lean_dec(v_start_3488_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v___x_3520_);
v___x_3522_ = v___x_3509_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_array_3487_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_stop_3489_);
v___x_3522_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v_fst_3426_);
lean_ctor_set(v___x_3523_, 1, v_snd_3516_);
v___x_3524_ = lean_array_push(v_fst_3430_, v_fst_3515_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3469_);
lean_ctor_set(v___x_3518_, 0, v___x_3493_);
v___x_3526_ = v___x_3518_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3469_);
v___x_3526_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3526_);
lean_ctor_set(v___x_3440_, 0, v___x_3522_);
v___x_3528_ = v___x_3440_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3528_);
lean_ctor_set(v___x_3436_, 0, v___x_3524_);
v___x_3530_ = v___x_3436_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3530_);
lean_ctor_set(v___x_3432_, 0, v___x_3523_);
v___x_3532_ = v___x_3432_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
size_t v___x_3533_; size_t v___x_3534_; 
v___x_3533_ = ((size_t)1ULL);
v___x_3534_ = lean_usize_add(v_i_3413_, v___x_3533_);
v_i_3413_ = v___x_3534_;
v_b_3414_ = v___x_3532_;
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
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_3509_);
lean_dec_ref(v___x_3493_);
lean_dec(v_stop_3489_);
lean_dec(v_start_3488_);
lean_dec_ref(v_array_3487_);
lean_dec_ref(v___x_3469_);
lean_del_object(v___x_3440_);
lean_del_object(v___x_3436_);
lean_del_object(v___x_3432_);
lean_dec(v_fst_3430_);
lean_dec(v_fst_3426_);
lean_dec_ref(v_xs_3410_);
v_a_3542_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3513_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3513_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3572_, lean_object* v_as_3573_, lean_object* v_sz_3574_, lean_object* v_i_3575_, lean_object* v_b_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
size_t v_sz_boxed_3582_; size_t v_i_boxed_3583_; lean_object* v_res_3584_; 
v_sz_boxed_3582_ = lean_unbox_usize(v_sz_3574_);
lean_dec(v_sz_3574_);
v_i_boxed_3583_ = lean_unbox_usize(v_i_3575_);
lean_dec(v_i_3575_);
v_res_3584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3572_, v_as_3573_, v_sz_boxed_3582_, v_i_boxed_3583_, v_b_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_as_3573_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
if (lean_obj_tag(v_a_3585_) == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = l_List_reverse___redArg(v_a_3586_);
return v___x_3587_;
}
else
{
lean_object* v_head_3588_; lean_object* v_tail_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3598_; 
v_head_3588_ = lean_ctor_get(v_a_3585_, 0);
v_tail_3589_ = lean_ctor_get(v_a_3585_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_a_3585_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3591_ = v_a_3585_;
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_tail_3589_);
lean_inc(v_head_3588_);
lean_dec(v_a_3585_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3588_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 1, v_a_3586_);
lean_ctor_set(v___x_3591_, 0, v___x_3593_);
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_a_3586_);
v___x_3595_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
v_a_3585_ = v_tail_3589_;
v_a_3586_ = v___x_3595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3599_, lean_object* v_j_3600_){
_start:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = lean_array_get_size(v_as_3599_);
v___x_3602_ = lean_nat_dec_lt(v_j_3600_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; 
lean_dec(v_j_3600_);
v___x_3603_ = lean_box(0);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3604_ = lean_array_fget_borrowed(v_as_3599_, v_j_3600_);
v___x_3605_ = lean_array_get_size(v___x_3604_);
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = lean_nat_dec_eq(v___x_3605_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_j_3600_, v___x_3608_);
lean_dec(v_j_3600_);
v_j_3600_ = v___x_3609_;
goto _start;
}
else
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_j_3600_);
return v___x_3611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3612_, lean_object* v_j_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3612_, v_j_3613_);
lean_dec_ref(v_as_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3615_, lean_object* v_as_3616_, size_t v_sz_3617_, size_t v_i_3618_, lean_object* v_b_3619_){
_start:
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_usize_dec_lt(v_i_3618_, v_sz_3617_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref(v_a_3615_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v_b_3619_);
return v___x_3622_;
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; 
v_a_3623_ = lean_array_uget_borrowed(v_as_3616_, v_i_3618_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3615_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3615_);
lean_ctor_set(v___x_3624_, 1, v_a_3623_);
v___x_3625_ = lean_array_push(v_b_3619_, v___x_3624_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3618_, v___x_3626_);
v_i_3618_ = v___x_3627_;
v_b_3619_ = v___x_3625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_){
_start:
{
size_t v_sz_boxed_3635_; size_t v_i_boxed_3636_; lean_object* v_res_3637_; 
v_sz_boxed_3635_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3636_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3629_, v_as_3630_, v_sz_boxed_3635_, v_i_boxed_3636_, v_b_3633_);
lean_dec_ref(v_as_3630_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3638_, lean_object* v_xs_3639_, lean_object* v_as_3640_, size_t v_sz_3641_, size_t v_i_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_usize_dec_lt(v_i_3642_, v_sz_3641_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec_ref(v_xs_3639_);
lean_dec_ref(v_a_3638_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_b_3643_);
return v___x_3650_;
}
else
{
lean_object* v_snd_3651_; lean_object* v_fst_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3695_; 
v_snd_3651_ = lean_ctor_get(v_b_3643_, 1);
v_fst_3652_ = lean_ctor_get(v_b_3643_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_b_3643_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3654_ = v_b_3643_;
v_isShared_3655_ = v_isSharedCheck_3695_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_snd_3651_);
lean_inc(v_fst_3652_);
lean_dec(v_b_3643_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3695_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_array_3656_; lean_object* v_start_3657_; lean_object* v_stop_3658_; uint8_t v___x_3659_; 
v_array_3656_ = lean_ctor_get(v_snd_3651_, 0);
v_start_3657_ = lean_ctor_get(v_snd_3651_, 1);
v_stop_3658_ = lean_ctor_get(v_snd_3651_, 2);
v___x_3659_ = lean_nat_dec_lt(v_start_3657_, v_stop_3658_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3661_; 
lean_dec_ref(v_xs_3639_);
lean_dec_ref(v_a_3638_);
if (v_isShared_3655_ == 0)
{
v___x_3661_ = v___x_3654_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_fst_3652_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_snd_3651_);
v___x_3661_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
return v___x_3662_;
}
}
else
{
lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3691_; 
lean_inc(v_stop_3658_);
lean_inc(v_start_3657_);
lean_inc_ref(v_array_3656_);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_snd_3651_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3692_ = lean_ctor_get(v_snd_3651_, 2);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_snd_3651_, 1);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_snd_3651_, 0);
lean_dec(v_unused_3694_);
v___x_3665_ = v_snd_3651_;
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v_snd_3651_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3667_ = lean_array_uget_borrowed(v_as_3640_, v_i_3642_);
v___x_3668_ = lean_array_fget_borrowed(v_array_3656_, v_start_3657_);
lean_inc(v_a_3667_);
lean_inc_ref(v_xs_3639_);
lean_inc_ref(v_a_3638_);
v___x_3669_ = l_Lean_Elab_Structural_argsInGroup(v_a_3638_, v_xs_3639_, v_a_3667_, v___x_3668_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_nat_add(v_start_3657_, v___x_3671_);
lean_dec(v_start_3657_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 1, v___x_3672_);
v___x_3674_ = v___x_3665_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_array_3656_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_stop_3658_);
v___x_3674_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = lean_array_push(v_fst_3652_, v_a_3670_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v___x_3674_);
lean_ctor_set(v___x_3654_, 0, v___x_3675_);
v___x_3677_ = v___x_3654_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v___x_3674_);
v___x_3677_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
size_t v___x_3678_; size_t v___x_3679_; 
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_add(v_i_3642_, v___x_3678_);
v_i_3642_ = v___x_3679_;
v_b_3643_ = v___x_3677_;
goto _start;
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3665_);
lean_dec(v_stop_3658_);
lean_dec(v_start_3657_);
lean_dec_ref(v_array_3656_);
lean_del_object(v___x_3654_);
lean_dec(v_fst_3652_);
lean_dec_ref(v_xs_3639_);
lean_dec_ref(v_a_3638_);
v_a_3683_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3669_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3669_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3696_, lean_object* v_xs_3697_, lean_object* v_as_3698_, lean_object* v_sz_3699_, lean_object* v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
size_t v_sz_boxed_3707_; size_t v_i_boxed_3708_; lean_object* v_res_3709_; 
v_sz_boxed_3707_ = lean_unbox_usize(v_sz_3699_);
lean_dec(v_sz_3699_);
v_i_boxed_3708_ = lean_unbox_usize(v_i_3700_);
lean_dec(v_i_3700_);
v_res_3709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3696_, v_xs_3697_, v_as_3698_, v_sz_boxed_3707_, v_i_boxed_3708_, v_b_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_as_3698_);
return v_res_3709_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3714_ = l_Lean_stringToMessageData(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3717_ = l_Lean_stringToMessageData(v___x_3716_);
return v___x_3717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3729_ = l_Lean_stringToMessageData(v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3730_, lean_object* v_values_3731_, lean_object* v_xs_3732_, lean_object* v_fnNames_3733_, lean_object* v_as_3734_, size_t v_sz_3735_, size_t v_i_3736_, lean_object* v_b_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_a_3744_; uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3736_, v_sz_3735_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
lean_dec_ref(v_xs_3732_);
lean_dec_ref(v___x_3730_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_b_3737_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; lean_object* v_recArgInfoss_3751_; lean_object* v_a_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; size_t v_sz_3756_; size_t v___x_3757_; lean_object* v___x_3758_; 
v___x_3750_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3752_ = lean_array_uget_borrowed(v_as_3734_, v_i_3736_);
v___x_3753_ = lean_array_get_size(v___x_3730_);
lean_inc_ref(v___x_3730_);
v___x_3754_ = l_Array_toSubarray___redArg(v___x_3730_, v___x_3750_, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v_recArgInfoss_3751_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v_sz_3756_ = lean_array_size(v_values_3731_);
v___x_3757_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3732_);
lean_inc(v_a_3752_);
v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3752_, v_xs_3732_, v_values_3731_, v_sz_3756_, v___x_3757_, v___x_3755_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v_fst_3760_; lean_object* v_snd_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3819_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v_fst_3760_ = lean_ctor_get(v_b_3737_, 0);
v_snd_3761_ = lean_ctor_get(v_b_3737_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_b_3737_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3763_ = v_b_3737_;
v_isShared_3764_ = v_isSharedCheck_3819_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_snd_3761_);
lean_inc(v_fst_3760_);
lean_dec(v_b_3737_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3819_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_fst_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3817_; 
v_fst_3765_ = lean_ctor_get(v_a_3759_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_a_3759_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; 
v_unused_3818_ = lean_ctor_get(v_a_3759_, 1);
lean_dec(v_unused_3818_);
v___x_3767_ = v_a_3759_;
v_isShared_3768_ = v_isSharedCheck_3817_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_fst_3765_);
lean_dec(v_a_3759_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3817_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3765_, v___x_3750_);
if (lean_obj_tag(v___x_3769_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
lean_dec(v_fst_3765_);
v_val_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3752_);
v___x_3773_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3752_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 7);
lean_ctor_set(v___x_3763_, 1, v___x_3773_);
lean_ctor_set(v___x_3763_, 0, v___x_3772_);
v___x_3775_ = v___x_3763_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3776_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_array_get_borrowed(v___x_3771_, v_fnNames_3733_, v_val_3770_);
lean_dec(v_val_3770_);
lean_inc(v___x_3778_);
v___x_3779_ = l_Lean_MessageData_ofName(v___x_3778_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3777_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_fst_3760_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_snd_3761_);
lean_ctor_set(v___x_3767_, 0, v___x_3783_);
v___x_3785_ = v___x_3767_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_snd_3761_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
v_a_3744_ = v___x_3785_;
goto v___jp_3743_;
}
}
}
else
{
lean_object* v___x_3788_; 
lean_dec(v___x_3769_);
v___x_3788_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3765_);
lean_dec(v_fst_3765_);
if (lean_obj_tag(v___x_3788_) == 1)
{
lean_object* v_val_3789_; size_t v_sz_3790_; lean_object* v___x_3791_; 
lean_del_object(v___x_3763_);
v_val_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_val_3789_);
lean_dec_ref(v___x_3788_);
v_sz_3790_ = lean_array_size(v_val_3789_);
lean_inc(v_a_3752_);
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3752_, v_val_3789_, v_sz_3790_, v___x_3757_, v_snd_3761_);
lean_dec(v_val_3789_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3794_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_a_3792_);
lean_ctor_set(v___x_3767_, 0, v_fst_3760_);
v___x_3794_ = v___x_3767_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_fst_3760_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_a_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
v_a_3744_ = v___x_3794_;
goto v___jp_3743_;
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3767_);
lean_dec(v_fst_3760_);
lean_dec_ref(v_xs_3732_);
lean_dec_ref(v___x_3730_);
v_a_3796_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3791_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3791_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
lean_dec(v___x_3788_);
v___x_3804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3752_);
v___x_3805_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3752_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 7);
lean_ctor_set(v___x_3763_, 1, v___x_3805_);
lean_ctor_set(v___x_3763_, 0, v___x_3804_);
v___x_3807_ = v___x_3763_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v_fst_3760_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_snd_3761_);
lean_ctor_set(v___x_3767_, 0, v___x_3812_);
v___x_3814_ = v___x_3767_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_snd_3761_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
v_a_3744_ = v___x_3814_;
goto v___jp_3743_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_b_3737_);
lean_dec_ref(v_xs_3732_);
lean_dec_ref(v___x_3730_);
v_a_3820_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3758_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3758_);
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
v___jp_3743_:
{
size_t v___x_3745_; size_t v___x_3746_; 
v___x_3745_ = ((size_t)1ULL);
v___x_3746_ = lean_usize_add(v_i_3736_, v___x_3745_);
v_i_3736_ = v___x_3746_;
v_b_3737_ = v_a_3744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3828_, lean_object* v_values_3829_, lean_object* v_xs_3830_, lean_object* v_fnNames_3831_, lean_object* v_as_3832_, lean_object* v_sz_3833_, lean_object* v_i_3834_, lean_object* v_b_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
size_t v_sz_boxed_3841_; size_t v_i_boxed_3842_; lean_object* v_res_3843_; 
v_sz_boxed_3841_ = lean_unbox_usize(v_sz_3833_);
lean_dec(v_sz_3833_);
v_i_boxed_3842_ = lean_unbox_usize(v_i_3834_);
lean_dec(v_i_3834_);
v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3828_, v_values_3829_, v_xs_3830_, v_fnNames_3831_, v_as_3832_, v_sz_boxed_3841_, v_i_boxed_3842_, v_b_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v_as_3832_);
lean_dec_ref(v_fnNames_3831_);
lean_dec_ref(v_values_3829_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3844_, lean_object* v___x_3845_, lean_object* v_values_3846_, lean_object* v_fnNames_3847_, lean_object* v_as_3848_, size_t v_sz_3849_, size_t v_i_3850_, lean_object* v_b_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_a_3858_; uint8_t v___x_3862_; 
v___x_3862_ = lean_usize_dec_lt(v_i_3850_, v_sz_3849_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_xs_3844_);
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_b_3851_);
return v___x_3863_;
}
else
{
lean_object* v___x_3864_; lean_object* v_recArgInfoss_3865_; lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; size_t v_sz_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
v___x_3864_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3866_ = lean_array_uget_borrowed(v_as_3848_, v_i_3850_);
v___x_3867_ = lean_array_get_size(v___x_3845_);
lean_inc_ref(v___x_3845_);
v___x_3868_ = l_Array_toSubarray___redArg(v___x_3845_, v___x_3864_, v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v_recArgInfoss_3865_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v_sz_3870_ = lean_array_size(v_values_3846_);
v___x_3871_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3844_);
lean_inc(v_a_3866_);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3866_, v_xs_3844_, v_values_3846_, v_sz_3870_, v___x_3871_, v___x_3869_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v_fst_3874_; lean_object* v_snd_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3933_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3872_);
v_fst_3874_ = lean_ctor_get(v_b_3851_, 0);
v_snd_3875_ = lean_ctor_get(v_b_3851_, 1);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_b_3851_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3877_ = v_b_3851_;
v_isShared_3878_ = v_isSharedCheck_3933_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_snd_3875_);
lean_inc(v_fst_3874_);
lean_dec(v_b_3851_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3933_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_fst_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3931_; 
v_fst_3879_ = lean_ctor_get(v_a_3873_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_a_3873_, 1);
lean_dec(v_unused_3932_);
v___x_3881_ = v_a_3873_;
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_fst_3879_);
lean_dec(v_a_3873_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3879_, v___x_3864_);
if (lean_obj_tag(v___x_3883_) == 1)
{
lean_object* v_val_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
lean_dec(v_fst_3879_);
v_val_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_val_3884_);
lean_dec_ref(v___x_3883_);
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3866_);
v___x_3887_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3866_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 7);
lean_ctor_set(v___x_3877_, 1, v___x_3887_);
lean_ctor_set(v___x_3877_, 0, v___x_3886_);
v___x_3889_ = v___x_3877_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_array_get_borrowed(v___x_3885_, v_fnNames_3847_, v_val_3884_);
lean_dec(v_val_3884_);
lean_inc(v___x_3892_);
v___x_3893_ = l_Lean_MessageData_ofName(v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3891_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_fst_3874_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_snd_3875_);
lean_ctor_set(v___x_3881_, 0, v___x_3897_);
v___x_3899_ = v___x_3881_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_snd_3875_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
v_a_3858_ = v___x_3899_;
goto v___jp_3857_;
}
}
}
else
{
lean_object* v___x_3902_; 
lean_dec(v___x_3883_);
v___x_3902_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3879_);
lean_dec(v_fst_3879_);
if (lean_obj_tag(v___x_3902_) == 1)
{
lean_object* v_val_3903_; size_t v_sz_3904_; lean_object* v___x_3905_; 
lean_del_object(v___x_3877_);
v_val_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_val_3903_);
lean_dec_ref(v___x_3902_);
v_sz_3904_ = lean_array_size(v_val_3903_);
lean_inc(v_a_3866_);
v___x_3905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3866_, v_val_3903_, v_sz_3904_, v___x_3871_, v_snd_3875_);
lean_dec(v_val_3903_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3905_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_a_3906_);
lean_ctor_set(v___x_3881_, 0, v_fst_3874_);
v___x_3908_ = v___x_3881_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_fst_3874_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_a_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
v_a_3858_ = v___x_3908_;
goto v___jp_3857_;
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_del_object(v___x_3881_);
lean_dec(v_fst_3874_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_xs_3844_);
v_a_3910_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3905_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3905_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_dec(v___x_3902_);
v___x_3918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3866_);
v___x_3919_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3866_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 7);
lean_ctor_set(v___x_3877_, 1, v___x_3919_);
lean_ctor_set(v___x_3877_, 0, v___x_3918_);
v___x_3921_ = v___x_3877_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v_fst_3874_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_snd_3875_);
lean_ctor_set(v___x_3881_, 0, v___x_3926_);
v___x_3928_ = v___x_3881_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_snd_3875_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
v_a_3858_ = v___x_3928_;
goto v___jp_3857_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v_b_3851_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_xs_3844_);
v_a_3934_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3872_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3872_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
v___jp_3857_:
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((size_t)1ULL);
v___x_3860_ = lean_usize_add(v_i_3850_, v___x_3859_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3845_, v_values_3846_, v_xs_3844_, v_fnNames_3847_, v_as_3848_, v_sz_3849_, v___x_3860_, v_a_3858_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3861_;
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
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3962_ = l_Lean_MessageData_ofFormat(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3965_ = l_Lean_stringToMessageData(v___x_3964_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3970_ = l_Lean_stringToMessageData(v___x_3969_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_box(1);
v___x_3972_ = l_Lean_MessageData_ofFormat(v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3973_, lean_object* v_fixedParamPerms_3974_, lean_object* v_xs_3975_, lean_object* v_values_3976_, lean_object* v_termMeasure_x3fs_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3983_; lean_object* v_recArgInfoss_3984_; lean_object* v___x_3985_; lean_object* v_perms_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_report_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; size_t v_sz_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3983_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3985_ = lean_array_get_size(v_values_3976_);
v_perms_3986_ = lean_ctor_get(v_fixedParamPerms_3974_, 1);
lean_inc_ref(v_perms_3986_);
lean_dec_ref(v_fixedParamPerms_3974_);
lean_inc_ref(v_values_3976_);
v___x_3987_ = l_Array_toSubarray___redArg(v_values_3976_, v___x_3983_, v___x_3985_);
v___x_3988_ = lean_array_get_size(v_termMeasure_x3fs_3977_);
v_report_3989_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3990_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3977_, v___x_3983_, v___x_3988_);
v___x_3991_ = lean_array_get_size(v_perms_3986_);
v___x_3992_ = l_Array_toSubarray___redArg(v_perms_3986_, v___x_3983_, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3990_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3987_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v_recArgInfoss_3984_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v_report_3989_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v_sz_3997_ = lean_array_size(v_fnNames_3973_);
v___x_3998_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3975_);
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3975_, v_fnNames_3973_, v_sz_3997_, v___x_3998_, v___x_3996_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_snd_4001_; lean_object* v_options_4002_; lean_object* v_fst_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4146_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
v_snd_4001_ = lean_ctor_get(v_a_4000_, 1);
lean_inc(v_snd_4001_);
v_options_4002_ = lean_ctor_get(v_a_3980_, 2);
v_fst_4003_ = lean_ctor_get(v_a_4000_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_a_4000_, 1);
lean_dec(v_unused_4147_);
v___x_4005_ = v_a_4000_;
v_isShared_4006_ = v_isSharedCheck_4146_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_fst_4003_);
lean_dec(v_a_4000_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4146_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_fst_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4144_; 
v_fst_4007_ = lean_ctor_get(v_snd_4001_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_snd_4001_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_snd_4001_, 1);
lean_dec(v_unused_4145_);
v___x_4009_ = v_snd_4001_;
v_isShared_4010_ = v_isSharedCheck_4144_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_fst_4007_);
lean_dec(v_snd_4001_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4144_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v_inheritedTraceOptions_4011_; uint8_t v_hasTrace_4012_; size_t v_sz_4013_; lean_object* v___x_4014_; lean_object* v___y_4016_; lean_object* v_report_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___x_4064_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; 
v_inheritedTraceOptions_4011_ = lean_ctor_get(v_a_3980_, 13);
v_hasTrace_4012_ = lean_ctor_get_uint8(v_options_4002_, sizeof(void*)*1);
v_sz_4013_ = lean_array_size(v_fst_4007_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4013_, v___x_3998_, v_fst_4007_);
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4012_ == 0)
{
v___y_4103_ = v_a_3978_;
v___y_4104_ = v_a_3979_;
v___y_4105_ = v_a_3980_;
v___y_4106_ = v_a_3981_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4115_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4011_, v_options_4002_, v___x_4115_);
if (v___x_4116_ == 0)
{
v___y_4103_ = v_a_3978_;
v___y_4104_ = v_a_3979_;
v___y_4105_ = v_a_3980_;
v___y_4106_ = v_a_3981_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4117_; lean_object* v___y_4119_; lean_object* v___x_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4117_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4136_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4137_ = lean_array_get_size(v___x_4014_);
v___x_4138_ = lean_nat_dec_lt(v___x_3983_, v___x_4137_);
if (v___x_4138_ == 0)
{
v___y_4119_ = v___x_4136_;
goto v___jp_4118_;
}
else
{
uint8_t v___x_4139_; 
v___x_4139_ = lean_nat_dec_le(v___x_4137_, v___x_4137_);
if (v___x_4139_ == 0)
{
if (v___x_4138_ == 0)
{
v___y_4119_ = v___x_4136_;
goto v___jp_4118_;
}
else
{
size_t v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_usize_of_nat(v___x_4137_);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4014_, v___x_3998_, v___x_4140_, v___x_4136_);
v___y_4119_ = v___x_4141_;
goto v___jp_4118_;
}
}
else
{
size_t v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_usize_of_nat(v___x_4137_);
v___x_4143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4014_, v___x_3998_, v___x_4142_, v___x_4136_);
v___y_4119_ = v___x_4143_;
goto v___jp_4118_;
}
}
v___jp_4118_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4120_ = lean_array_to_list(v___y_4119_);
v___x_4121_ = lean_box(0);
v___x_4122_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4120_, v___x_4121_);
v___x_4123_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4124_ = l_Lean_MessageData_joinSep(v___x_4122_, v___x_4123_);
v___x_4125_ = l_Lean_indentD(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4117_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4064_, v___x_4126_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_dec_ref(v___x_4127_);
v___y_4103_ = v_a_3978_;
v___y_4104_ = v_a_3979_;
v___y_4105_ = v_a_3980_;
v___y_4106_ = v_a_3981_;
goto v___jp_4102_;
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec_ref(v___x_4014_);
lean_del_object(v___x_4009_);
lean_del_object(v___x_4005_);
lean_dec(v_fst_4003_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
}
}
v___jp_4015_:
{
lean_object* v___x_4023_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v_recArgInfoss_3984_);
lean_ctor_set(v___x_4009_, 0, v_report_4017_);
v___x_4023_ = v___x_4009_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_report_4017_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_recArgInfoss_3984_);
v___x_4023_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
size_t v_sz_4024_; lean_object* v___x_4025_; 
v_sz_4024_ = lean_array_size(v___y_4016_);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3975_, v___x_4014_, v_values_3976_, v_fnNames_3973_, v___y_4016_, v_sz_4024_, v___x_3998_, v___x_4023_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_values_3976_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4042_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4028_ = v___x_4025_;
v_isShared_4029_ = v_isSharedCheck_4042_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4025_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4042_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4041_; 
v_fst_4030_ = lean_ctor_get(v_a_4026_, 0);
v_snd_4031_ = lean_ctor_get(v_a_4026_, 1);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_a_4026_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4033_ = v_a_4026_;
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_snd_4031_);
lean_inc(v_fst_4030_);
lean_dec(v_a_4026_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4041_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v_fst_4030_);
lean_ctor_set(v___x_4033_, 0, v_snd_4031_);
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_snd_4031_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_fst_4030_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4036_);
v___x_4038_ = v___x_4028_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4025_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4025_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
v___jp_4052_:
{
lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4058_ = lean_array_get_size(v___y_4053_);
v___x_4059_ = lean_nat_dec_eq(v___x_4058_, v___x_3983_);
if (v___x_4059_ == 0)
{
lean_del_object(v___x_4005_);
v___y_4016_ = v___y_4053_;
v_report_4017_ = v_fst_4003_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
v___y_4021_ = v___y_4057_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4060_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4006_ == 0)
{
lean_ctor_set_tag(v___x_4005_, 7);
lean_ctor_set(v___x_4005_, 1, v___x_4060_);
v___x_4062_ = v___x_4005_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_fst_4003_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
v___y_4016_ = v___y_4053_;
v_report_4017_ = v___x_4062_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
v___y_4021_ = v___y_4057_;
goto v___jp_4015_;
}
}
}
v___jp_4065_:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4070_, v___y_4069_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_options_4072_; uint8_t v_hasTrace_4073_; 
v_options_4072_ = lean_ctor_get(v___y_4067_, 2);
v_hasTrace_4073_ = lean_ctor_get_uint8(v_options_4072_, sizeof(void*)*1);
if (v_hasTrace_4073_ == 0)
{
lean_object* v_a_4074_; 
v_a_4074_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4074_);
lean_dec_ref(v___x_4071_);
v___y_4053_ = v_a_4074_;
v___y_4054_ = v___y_4069_;
v___y_4055_ = v___y_4066_;
v___y_4056_ = v___y_4067_;
v___y_4057_ = v___y_4068_;
goto v___jp_4052_;
}
else
{
lean_object* v_a_4075_; lean_object* v_inheritedTraceOptions_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_a_4075_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4075_);
lean_dec_ref(v___x_4071_);
v_inheritedTraceOptions_4076_ = lean_ctor_get(v___y_4067_, 13);
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4076_, v_options_4072_, v___x_4077_);
if (v___x_4078_ == 0)
{
v___y_4053_ = v_a_4075_;
v___y_4054_ = v___y_4069_;
v___y_4055_ = v___y_4066_;
v___y_4056_ = v___y_4067_;
v___y_4057_ = v___y_4068_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4079_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4075_);
v___x_4080_ = lean_array_to_list(v_a_4075_);
v___x_4081_ = lean_box(0);
v___x_4082_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4080_, v___x_4081_);
v___x_4083_ = l_Lean_MessageData_ofList(v___x_4082_);
v___x_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4079_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4064_, v___x_4084_, v___y_4069_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_dec_ref(v___x_4085_);
v___y_4053_ = v_a_4075_;
v___y_4054_ = v___y_4069_;
v___y_4055_ = v___y_4066_;
v___y_4056_ = v___y_4067_;
v___y_4057_ = v___y_4068_;
goto v___jp_4052_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_a_4075_);
lean_dec_ref(v___x_4014_);
lean_del_object(v___x_4009_);
lean_del_object(v___x_4005_);
lean_dec(v_fst_4003_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4085_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4085_);
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
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec_ref(v___x_4014_);
lean_del_object(v___x_4009_);
lean_del_object(v___x_4005_);
lean_dec(v_fst_4003_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4094_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4071_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4071_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
v___jp_4102_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4108_ = lean_array_get_size(v___x_4014_);
v___x_4109_ = lean_nat_dec_lt(v___x_3983_, v___x_4108_);
if (v___x_4109_ == 0)
{
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4103_;
v___y_4070_ = v___x_4107_;
goto v___jp_4065_;
}
else
{
uint8_t v___x_4110_; 
v___x_4110_ = lean_nat_dec_le(v___x_4108_, v___x_4108_);
if (v___x_4110_ == 0)
{
if (v___x_4109_ == 0)
{
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4103_;
v___y_4070_ = v___x_4107_;
goto v___jp_4065_;
}
else
{
size_t v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_usize_of_nat(v___x_4108_);
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4014_, v___x_3998_, v___x_4111_, v___x_4107_);
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4103_;
v___y_4070_ = v___x_4112_;
goto v___jp_4065_;
}
}
else
{
size_t v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_usize_of_nat(v___x_4108_);
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4014_, v___x_3998_, v___x_4113_, v___x_4107_);
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4103_;
v___y_4070_ = v___x_4114_;
goto v___jp_4065_;
}
}
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4148_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_3999_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_3999_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4156_, lean_object* v_fixedParamPerms_4157_, lean_object* v_xs_4158_, lean_object* v_values_4159_, lean_object* v_termMeasure_x3fs_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4156_, v_fixedParamPerms_4157_, v_xs_4158_, v_values_4159_, v_termMeasure_x3fs_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec_ref(v_fnNames_4156_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4167_, lean_object* v_as_4168_, size_t v_sz_4169_, size_t v_i_4170_, lean_object* v_b_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4167_, v_as_4168_, v_sz_4169_, v_i_4170_, v_b_4171_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4178_, lean_object* v_as_4179_, lean_object* v_sz_4180_, lean_object* v_i_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
size_t v_sz_boxed_4188_; size_t v_i_boxed_4189_; lean_object* v_res_4190_; 
v_sz_boxed_4188_ = lean_unbox_usize(v_sz_4180_);
lean_dec(v_sz_4180_);
v_i_boxed_4189_ = lean_unbox_usize(v_i_4181_);
lean_dec(v_i_4181_);
v_res_4190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4178_, v_as_4179_, v_sz_boxed_4188_, v_i_boxed_4189_, v_b_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec_ref(v_as_4179_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4191_, uint8_t v_skipRealize_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; lean_object* v_env_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4195_ = lean_st_ref_get(v___y_4193_);
v_env_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc_ref(v_env_4196_);
lean_dec(v___x_4195_);
v___x_4197_ = l_Lean_Environment_contains(v_env_4196_, v_constName_4191_, v_skipRealize_4192_);
v___x_4198_ = lean_box(v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4200_, lean_object* v_skipRealize_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
uint8_t v_skipRealize_boxed_4204_; lean_object* v_res_4205_; 
v_skipRealize_boxed_4204_ = lean_unbox(v_skipRealize_4201_);
v_res_4205_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4200_, v_skipRealize_boxed_4204_, v___y_4202_);
lean_dec(v___y_4202_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4206_, uint8_t v_skipRealize_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4206_, v_skipRealize_4207_, v___y_4211_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4214_, lean_object* v_skipRealize_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
uint8_t v_skipRealize_boxed_4221_; lean_object* v_res_4222_; 
v_skipRealize_boxed_4221_ = lean_unbox(v_skipRealize_4215_);
v_res_4222_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4214_, v_skipRealize_boxed_4221_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l_Lean_Meta_saveState___redArg(v___y_4225_, v___y_4227_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4231_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref(v___x_4229_);
lean_inc(v___y_4227_);
lean_inc_ref(v___y_4226_);
lean_inc(v___y_4225_);
lean_inc_ref(v___y_4224_);
v___x_4231_ = lean_apply_5(v_x_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, lean_box(0));
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_dec(v_a_4230_);
return v___x_4231_;
}
else
{
lean_object* v_a_4232_; uint8_t v___y_4234_; uint8_t v___x_4252_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
v___x_4252_ = l_Lean_Exception_isInterrupt(v_a_4232_);
if (v___x_4252_ == 0)
{
uint8_t v___x_4253_; 
lean_inc(v_a_4232_);
v___x_4253_ = l_Lean_Exception_isRuntime(v_a_4232_);
v___y_4234_ = v___x_4253_;
goto v___jp_4233_;
}
else
{
v___y_4234_ = v___x_4252_;
goto v___jp_4233_;
}
v___jp_4233_:
{
if (v___y_4234_ == 0)
{
lean_object* v___x_4235_; 
lean_dec_ref(v___x_4231_);
v___x_4235_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4230_, v___y_4225_, v___y_4227_);
lean_dec(v_a_4230_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; 
v_unused_4243_ = lean_ctor_get(v___x_4235_, 0);
lean_dec(v_unused_4243_);
v___x_4237_ = v___x_4235_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_dec(v___x_4235_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
lean_ctor_set_tag(v___x_4237_, 1);
lean_ctor_set(v___x_4237_, 0, v_a_4232_);
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4232_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v_a_4232_);
v_a_4244_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4235_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4235_);
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
else
{
lean_dec(v_a_4232_);
lean_dec(v_a_4230_);
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec_ref(v_x_4223_);
v_a_4254_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4229_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4229_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4277_, v_x_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
return v_res_4284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4287_ = l_Lean_stringToMessageData(v___x_4286_);
return v___x_4287_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4290_ = l_Lean_stringToMessageData(v___x_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4291_, uint8_t v___x_4292_, lean_object* v_group_4293_, lean_object* v_k_4294_, lean_object* v_comb_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4291_, v___x_4292_, v___y_4299_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; uint8_t v___x_4303_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref(v___x_4301_);
v___x_4303_ = lean_unbox(v_a_4302_);
lean_dec(v_a_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4304_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4305_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4293_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4308_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v___x_4310_; 
lean_dec_ref(v___x_4309_);
v___x_4310_ = lean_apply_6(v_k_4294_, v_comb_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
return v___x_4310_;
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_comb_4295_);
lean_dec_ref(v_k_4294_);
v_a_4311_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4309_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4309_);
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
else
{
lean_object* v___x_4319_; 
lean_dec_ref(v_group_4293_);
v___x_4319_ = lean_apply_6(v_k_4294_, v_comb_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
return v___x_4319_;
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_comb_4295_);
lean_dec_ref(v_k_4294_);
lean_dec_ref(v_group_4293_);
v_a_4320_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4301_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4301_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4328_, lean_object* v___x_4329_, lean_object* v_group_4330_, lean_object* v_k_4331_, lean_object* v_comb_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
uint8_t v___x_4420__boxed_4338_; lean_object* v_res_4339_; 
v___x_4420__boxed_4338_ = lean_unbox(v___x_4329_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4328_, v___x_4420__boxed_4338_, v_group_4330_, v_k_4331_, v_comb_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
return v_res_4339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
return v___x_4342_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4344_ = l_Lean_stringToMessageData(v___x_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4345_, lean_object* v_fnNames_4346_, lean_object* v_xs_4347_, lean_object* v_values_4348_, lean_object* v_as_4349_, size_t v_sz_4350_, size_t v_i_4351_, lean_object* v_b_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_usize_dec_lt(v_i_4351_, v_sz_4350_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; 
lean_dec_ref(v_values_4348_);
lean_dec_ref(v_xs_4347_);
lean_dec_ref(v_k_4345_);
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v_b_4352_);
return v___x_4359_;
}
else
{
lean_object* v_snd_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4430_; 
v_snd_4360_ = lean_ctor_get(v_b_4352_, 1);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_b_4352_);
if (v_isSharedCheck_4430_ == 0)
{
lean_object* v_unused_4431_; 
v_unused_4431_ = lean_ctor_get(v_b_4352_, 0);
lean_dec(v_unused_4431_);
v___x_4362_ = v_b_4352_;
v_isShared_4363_ = v_isSharedCheck_4430_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_snd_4360_);
lean_dec(v_b_4352_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4430_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_a_4364_; lean_object* v_group_4365_; lean_object* v_comb_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4429_; 
v_a_4364_ = lean_array_uget(v_as_4349_, v_i_4351_);
v_group_4365_ = lean_ctor_get(v_a_4364_, 0);
v_comb_4366_ = lean_ctor_get(v_a_4364_, 1);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_a_4364_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4368_ = v_a_4364_;
v_isShared_4369_ = v_isSharedCheck_4429_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_comb_4366_);
lean_inc(v_group_4365_);
lean_dec(v_a_4364_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4429_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v_toIndGroupInfo_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___f_4374_; lean_object* v___x_4375_; 
v_toIndGroupInfo_4370_ = lean_ctor_get(v_group_4365_, 0);
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4370_, v___x_4371_);
v___x_4373_ = lean_box(v___x_4358_);
lean_inc_ref(v_comb_4366_);
lean_inc_ref(v_k_4345_);
v___f_4374_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4374_, 0, v___x_4372_);
lean_closure_set(v___f_4374_, 1, v___x_4373_);
lean_closure_set(v___f_4374_, 2, v_group_4365_);
lean_closure_set(v___f_4374_, 3, v_k_4345_);
lean_closure_set(v___f_4374_, 4, v_comb_4366_);
v___x_4375_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4374_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4387_; 
lean_del_object(v___x_4368_);
lean_dec_ref(v_comb_4366_);
lean_dec_ref(v_values_4348_);
lean_dec_ref(v_xs_4347_);
lean_dec_ref(v_k_4345_);
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4387_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4387_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v_a_4376_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v___x_4380_);
v___x_4382_ = v___x_4362_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_snd_4360_);
v___x_4382_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4384_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4382_);
v___x_4384_ = v___x_4378_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4428_; 
v_a_4388_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4390_ = v___x_4375_;
v_isShared_4391_ = v_isSharedCheck_4428_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4375_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4428_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; uint8_t v___y_4394_; uint8_t v___x_4426_; 
v___x_4392_ = lean_box(0);
v___x_4426_ = l_Lean_Exception_isInterrupt(v_a_4388_);
if (v___x_4426_ == 0)
{
uint8_t v___x_4427_; 
lean_inc(v_a_4388_);
v___x_4427_ = l_Lean_Exception_isRuntime(v_a_4388_);
v___y_4394_ = v___x_4427_;
goto v___jp_4393_;
}
else
{
v___y_4394_ = v___x_4426_;
goto v___jp_4393_;
}
v___jp_4393_:
{
if (v___y_4394_ == 0)
{
lean_object* v___x_4395_; 
lean_del_object(v___x_4390_);
lean_inc_ref(v_values_4348_);
lean_inc_ref(v_xs_4347_);
v___x_4395_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4346_, v_xs_4347_, v_values_4348_, v_comb_4366_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref(v___x_4395_);
v___x_4397_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 7);
lean_ctor_set(v___x_4368_, 1, v_a_4396_);
lean_ctor_set(v___x_4368_, 0, v___x_4397_);
v___x_4399_ = v___x_4368_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_a_4396_);
v___x_4399_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4400_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = l_Lean_Exception_toMessageData(v_a_4388_);
v___x_4403_ = l_Lean_indentD(v___x_4402_);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4401_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_snd_4360_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 1, v___x_4407_);
lean_ctor_set(v___x_4362_, 0, v___x_4392_);
v___x_4409_ = v___x_4362_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
size_t v___x_4410_; size_t v___x_4411_; 
v___x_4410_ = ((size_t)1ULL);
v___x_4411_ = lean_usize_add(v_i_4351_, v___x_4410_);
v_i_4351_ = v___x_4411_;
v_b_4352_ = v___x_4409_;
goto _start;
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_a_4388_);
lean_del_object(v___x_4368_);
lean_del_object(v___x_4362_);
lean_dec(v_snd_4360_);
lean_dec_ref(v_values_4348_);
lean_dec_ref(v_xs_4347_);
lean_dec_ref(v_k_4345_);
v_a_4415_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4395_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4395_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
else
{
lean_object* v___x_4424_; 
lean_del_object(v___x_4368_);
lean_dec_ref(v_comb_4366_);
lean_del_object(v___x_4362_);
lean_dec(v_snd_4360_);
lean_dec_ref(v_values_4348_);
lean_dec_ref(v_xs_4347_);
lean_dec_ref(v_k_4345_);
if (v_isShared_4391_ == 0)
{
v___x_4424_ = v___x_4390_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4388_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4432_, lean_object* v_fnNames_4433_, lean_object* v_xs_4434_, lean_object* v_values_4435_, lean_object* v_as_4436_, lean_object* v_sz_4437_, lean_object* v_i_4438_, lean_object* v_b_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4437_);
lean_dec(v_sz_4437_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4438_);
lean_dec(v_i_4438_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4432_, v_fnNames_4433_, v_xs_4434_, v_values_4435_, v_as_4436_, v_sz_boxed_4445_, v_i_boxed_4446_, v_b_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v_as_4436_);
lean_dec_ref(v_fnNames_4433_);
return v_res_4447_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4450_ = l_Lean_stringToMessageData(v___x_4449_);
return v___x_4450_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4453_ = l_Lean_stringToMessageData(v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4454_, lean_object* v_xs_4455_, lean_object* v_values_4456_, lean_object* v_candidates_4457_, lean_object* v_k_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_candidates_4464_; lean_object* v_report_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4524_; 
v_candidates_4464_ = lean_ctor_get(v_candidates_4457_, 0);
v_report_4465_ = lean_ctor_get(v_candidates_4457_, 1);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_candidates_4457_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4467_ = v_candidates_4457_;
v_isShared_4468_ = v_isSharedCheck_4524_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_report_4465_);
lean_inc(v_candidates_4464_);
lean_dec(v_candidates_4457_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4524_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4469_ = lean_box(0);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 0, v___x_4469_);
v___x_4471_ = v___x_4467_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_report_4465_);
v___x_4471_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
size_t v_sz_4472_; size_t v___x_4473_; lean_object* v___x_4474_; 
v_sz_4472_ = lean_array_size(v_candidates_4464_);
v___x_4473_ = ((size_t)0ULL);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4458_, v_fnNames_4454_, v_xs_4455_, v_values_4456_, v_candidates_4464_, v_sz_4472_, v___x_4473_, v___x_4471_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
lean_dec_ref(v_candidates_4464_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4514_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4477_ = v___x_4474_;
v_isShared_4478_ = v_isSharedCheck_4514_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4474_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4514_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v_fst_4479_; 
v_fst_4479_ = lean_ctor_get(v_a_4475_, 0);
if (lean_obj_tag(v_fst_4479_) == 0)
{
lean_object* v_options_4480_; lean_object* v_snd_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4508_; 
lean_del_object(v___x_4477_);
v_options_4480_ = lean_ctor_get(v_a_4461_, 2);
v_snd_4481_ = lean_ctor_get(v_a_4475_, 1);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_a_4475_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v_a_4475_, 0);
lean_dec(v_unused_4509_);
v___x_4483_ = v_a_4475_;
v_isShared_4484_ = v_isSharedCheck_4508_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_snd_4481_);
lean_dec(v_a_4475_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4508_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_inheritedTraceOptions_4485_; uint8_t v_hasTrace_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v_inheritedTraceOptions_4485_ = lean_ctor_get(v_a_4461_, 13);
v_hasTrace_4486_ = lean_ctor_get_uint8(v_options_4480_, sizeof(void*)*1);
v___x_4487_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 7);
lean_ctor_set(v___x_4483_, 0, v___x_4487_);
v___x_4489_ = v___x_4483_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4487_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_snd_4481_);
v___x_4489_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
if (v_hasTrace_4486_ == 0)
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4489_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
return v___x_4490_;
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4491_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4492_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4485_, v_options_4480_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4489_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
return v___x_4494_;
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4489_);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
lean_ctor_set(v___x_4496_, 1, v___x_4489_);
v___x_4497_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4491_, v___x_4496_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4498_; 
lean_dec_ref(v___x_4497_);
v___x_4498_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4489_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
return v___x_4498_;
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v___x_4489_);
v_a_4499_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4497_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4497_);
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
}
}
}
}
else
{
lean_object* v_val_4510_; lean_object* v___x_4512_; 
lean_inc_ref(v_fst_4479_);
lean_dec(v_a_4475_);
v_val_4510_ = lean_ctor_get(v_fst_4479_, 0);
lean_inc(v_val_4510_);
lean_dec_ref(v_fst_4479_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v_val_4510_);
v___x_4512_ = v___x_4477_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_val_4510_);
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
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_a_4515_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4474_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4474_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4525_, lean_object* v_xs_4526_, lean_object* v_values_4527_, lean_object* v_candidates_4528_, lean_object* v_k_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4525_, v_xs_4526_, v_values_4527_, v_candidates_4528_, v_k_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec_ref(v_fnNames_4525_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4536_, lean_object* v_fnNames_4537_, lean_object* v_xs_4538_, lean_object* v_values_4539_, lean_object* v_candidates_4540_, lean_object* v_k_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; 
v___x_4547_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4537_, v_xs_4538_, v_values_4539_, v_candidates_4540_, v_k_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4548_, lean_object* v_fnNames_4549_, lean_object* v_xs_4550_, lean_object* v_values_4551_, lean_object* v_candidates_4552_, lean_object* v_k_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4548_, v_fnNames_4549_, v_xs_4550_, v_values_4551_, v_candidates_4552_, v_k_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec_ref(v_fnNames_4549_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4560_, lean_object* v_k_4561_, lean_object* v_fnNames_4562_, lean_object* v_xs_4563_, lean_object* v_values_4564_, lean_object* v_as_4565_, size_t v_sz_4566_, size_t v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4561_, v_fnNames_4562_, v_xs_4563_, v_values_4564_, v_as_4565_, v_sz_4566_, v_i_4567_, v_b_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4575_, lean_object* v_k_4576_, lean_object* v_fnNames_4577_, lean_object* v_xs_4578_, lean_object* v_values_4579_, lean_object* v_as_4580_, lean_object* v_sz_4581_, lean_object* v_i_4582_, lean_object* v_b_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
size_t v_sz_boxed_4589_; size_t v_i_boxed_4590_; lean_object* v_res_4591_; 
v_sz_boxed_4589_ = lean_unbox_usize(v_sz_4581_);
lean_dec(v_sz_4581_);
v_i_boxed_4590_ = lean_unbox_usize(v_i_4582_);
lean_dec(v_i_4582_);
v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4575_, v_k_4576_, v_fnNames_4577_, v_xs_4578_, v_values_4579_, v_as_4580_, v_sz_boxed_4589_, v_i_boxed_4590_, v_b_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec_ref(v_as_4580_);
lean_dec_ref(v_fnNames_4577_);
return v_res_4591_;
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
