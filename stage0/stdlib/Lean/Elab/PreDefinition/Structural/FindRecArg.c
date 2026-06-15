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
lean_object* v___x_478_; uint8_t v_fst_480_; lean_object* v_mctx_481_; lean_object* v___y_499_; lean_object* v_mctx_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_478_ = lean_st_ref_get(v___y_476_);
v_mctx_504_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref_n(v_mctx_504_, 2);
lean_dec(v___x_478_);
v___f_505_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_506_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_506_, 0, v_fvarId_475_);
v___x_507_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_mctx_504_);
v___x_509_ = l_Lean_Expr_hasFVar(v_e_474_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; 
v___x_510_ = l_Lean_Expr_hasMVar(v_e_474_);
if (v___x_510_ == 0)
{
lean_dec_ref_known(v___x_508_, 2);
lean_dec_ref(v___f_506_);
lean_dec_ref(v_e_474_);
v_fst_480_ = v___x_510_;
v_mctx_481_ = v_mctx_504_;
goto v___jp_479_;
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_mctx_504_);
v___x_511_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_506_, v___f_505_, v_e_474_, v___x_508_);
v___y_499_ = v___x_511_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_mctx_504_);
v___x_512_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_506_, v___f_505_, v_e_474_, v___x_508_);
v___y_499_ = v___x_512_;
goto v___jp_498_;
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
v___jp_498_:
{
lean_object* v_snd_500_; lean_object* v_fst_501_; lean_object* v_mctx_502_; uint8_t v___x_503_; 
v_snd_500_ = lean_ctor_get(v___y_499_, 1);
lean_inc(v_snd_500_);
v_fst_501_ = lean_ctor_get(v___y_499_, 0);
lean_inc(v_fst_501_);
lean_dec_ref(v___y_499_);
v_mctx_502_ = lean_ctor_get(v_snd_500_, 1);
lean_inc_ref(v_mctx_502_);
lean_dec(v_snd_500_);
v___x_503_ = lean_unbox(v_fst_501_);
lean_dec(v_fst_501_);
v_fst_480_ = v___x_503_;
v_mctx_481_ = v_mctx_502_;
goto v___jp_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_513_, lean_object* v_fvarId_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_513_, v_fvarId_514_, v___y_515_);
lean_dec(v___y_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_518_, lean_object* v_fvarId_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_518_, v_fvarId_519_, v___y_521_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_526_, lean_object* v_fvarId_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_526_, v_fvarId_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_534_, lean_object* v_as_535_, size_t v_i_536_, size_t v_stop_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_eq(v_i_536_, v_stop_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_uget_borrowed(v_as_535_, v_i_536_);
v___x_540_ = lean_expr_eqv(v_a_534_, v___x_539_);
if (v___x_540_ == 0)
{
size_t v___x_541_; size_t v___x_542_; 
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_536_, v___x_541_);
v_i_536_ = v___x_542_;
goto _start;
}
else
{
return v___x_540_;
}
}
else
{
uint8_t v___x_544_; 
v___x_544_ = 0;
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_545_, lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_stop_548_){
_start:
{
size_t v_i_boxed_549_; size_t v_stop_boxed_550_; uint8_t v_res_551_; lean_object* v_r_552_; 
v_i_boxed_549_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_stop_boxed_550_ = lean_unbox_usize(v_stop_548_);
lean_dec(v_stop_548_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_545_, v_as_546_, v_i_boxed_549_, v_stop_boxed_550_);
lean_dec_ref(v_as_546_);
lean_dec_ref(v_a_545_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_array_get_size(v_as_553_);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
return v___x_557_;
}
else
{
if (v___x_557_ == 0)
{
return v___x_557_;
}
else
{
size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_556_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_554_, v_as_553_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_561_, lean_object* v_a_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_561_, v_a_562_);
lean_dec_ref(v_a_562_);
lean_dec_ref(v_as_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_568_, lean_object* v_indices_569_, lean_object* v_a_570_, lean_object* v_as_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_b_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_a_570_);
lean_dec_ref(v_a_568_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_b_574_);
return v___x_581_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v_b_574_);
v_a_582_ = lean_array_uget_borrowed(v_as_571_, v_i_573_);
v___x_583_ = l_Lean_Expr_fvarId_x21(v_a_582_);
lean_inc_ref(v_a_568_);
v___x_584_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_568_, v___x_583_, v___y_576_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_605_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_605_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_605_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_605_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_a_590_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_box(0);
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_596_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_569_, v_a_582_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
v___x_597_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_597_ == 0)
{
lean_del_object(v___x_587_);
v_a_590_ = v___x_595_;
goto v___jp_589_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec_ref(v_a_568_);
lean_inc(v_a_582_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_570_);
lean_ctor_set(v___x_598_, 1, v_a_582_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_594_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_601_);
v___x_603_ = v___x_587_;
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
else
{
lean_del_object(v___x_587_);
lean_dec(v_a_585_);
v_a_590_ = v___x_595_;
goto v___jp_589_;
}
v___jp_589_:
{
size_t v___x_591_; size_t v___x_592_; 
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_i_573_, v___x_591_);
lean_inc_ref(v_a_590_);
v_i_573_ = v___x_592_;
v_b_574_ = v_a_590_;
goto _start;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_a_570_);
lean_dec_ref(v_a_568_);
v_a_606_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_584_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_584_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_614_, lean_object* v_indices_615_, lean_object* v_a_616_, lean_object* v_as_617_, lean_object* v_sz_618_, lean_object* v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
size_t v_sz_boxed_626_; size_t v_i_boxed_627_; lean_object* v_res_628_; 
v_sz_boxed_626_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v_i_boxed_627_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_614_, v_indices_615_, v_a_616_, v_as_617_, v_sz_boxed_626_, v_i_boxed_627_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_as_617_);
lean_dec_ref(v_indices_615_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_629_, lean_object* v_indices_630_, lean_object* v_as_631_, size_t v_sz_632_, size_t v_i_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_633_, v_sz_632_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_b_634_);
return v___x_641_;
}
else
{
lean_object* v_a_642_; lean_object* v___x_643_; 
lean_dec_ref(v_b_634_);
v_a_642_ = lean_array_uget_borrowed(v_as_631_, v_i_633_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v_a_642_);
v___x_643_ = lean_infer_type(v_a_642_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_647_ = lean_array_size(v_ys_629_);
v___x_648_ = ((size_t)0ULL);
lean_inc(v_a_642_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_644_, v_indices_630_, v_a_642_, v_ys_629_, v_sz_647_, v___x_648_, v___x_646_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_669_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_669_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_fst_654_ = lean_ctor_get(v_a_650_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_650_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_a_650_, 1);
lean_dec(v_unused_668_);
v___x_656_ = v_a_650_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_fst_654_);
lean_dec(v_a_650_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
if (lean_obj_tag(v_fst_654_) == 0)
{
size_t v___x_658_; size_t v___x_659_; 
lean_del_object(v___x_656_);
lean_del_object(v___x_652_);
v___x_658_ = ((size_t)1ULL);
v___x_659_ = lean_usize_add(v_i_633_, v___x_658_);
v_i_633_ = v___x_659_;
v_b_634_ = v___x_646_;
goto _start;
}
else
{
lean_object* v___x_662_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_645_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_645_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_662_);
v___x_664_ = v___x_652_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
else
{
return v___x_649_;
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_643_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_643_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_678_, lean_object* v_indices_679_, lean_object* v_as_680_, lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_690_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_678_, v_indices_679_, v_as_680_, v_sz_boxed_689_, v_i_boxed_690_, v_b_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v_as_680_);
lean_dec_ref(v_indices_679_);
lean_dec_ref(v_ys_678_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_692_, lean_object* v_ys_693_, lean_object* v_as_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_b_697_);
return v___x_704_;
}
else
{
lean_object* v_a_705_; lean_object* v___x_706_; 
lean_dec_ref(v_b_697_);
v_a_705_ = lean_array_uget_borrowed(v_as_694_, v_i_696_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v_a_705_);
v___x_706_ = lean_infer_type(v_a_705_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; size_t v_sz_710_; size_t v___x_711_; lean_object* v___x_712_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = lean_box(0);
v___x_709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_710_ = lean_array_size(v_ys_693_);
v___x_711_ = ((size_t)0ULL);
lean_inc(v_a_705_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_707_, v_indices_692_, v_a_705_, v_ys_693_, v_sz_710_, v___x_711_, v___x_709_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_732_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_732_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_732_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_732_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_fst_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_730_; 
v_fst_717_ = lean_ctor_get(v_a_713_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_a_713_, 1);
lean_dec(v_unused_731_);
v___x_719_ = v_a_713_;
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_fst_717_);
lean_dec(v_a_713_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
if (lean_obj_tag(v_fst_717_) == 0)
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
lean_del_object(v___x_719_);
lean_del_object(v___x_715_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_696_, v___x_721_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_693_, v_indices_692_, v_as_694_, v_sz_695_, v___x_722_, v___x_709_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_723_;
}
else
{
lean_object* v___x_725_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_708_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_708_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_725_);
v___x_727_ = v___x_715_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
else
{
return v___x_712_;
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_706_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_706_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_741_, lean_object* v_ys_742_, lean_object* v_as_743_, lean_object* v_sz_744_, lean_object* v_i_745_, lean_object* v_b_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
size_t v_sz_boxed_752_; size_t v_i_boxed_753_; lean_object* v_res_754_; 
v_sz_boxed_752_ = lean_unbox_usize(v_sz_744_);
lean_dec(v_sz_744_);
v_i_boxed_753_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_res_754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_741_, v_ys_742_, v_as_743_, v_sz_boxed_752_, v_i_boxed_753_, v_b_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_as_743_);
lean_dec_ref(v_ys_742_);
lean_dec_ref(v_indices_741_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_755_, lean_object* v_indices_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_762_ = lean_box(0);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_764_ = lean_array_size(v_indices_756_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_756_, v_ys_755_, v_indices_756_, v_sz_764_, v___x_765_, v___x_763_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_779_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_fst_771_; 
v_fst_771_ = lean_ctor_get(v_a_767_, 0);
lean_inc(v_fst_771_);
lean_dec(v_a_767_);
if (lean_obj_tag(v_fst_771_) == 0)
{
lean_object* v___x_773_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_762_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_762_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v_val_775_; lean_object* v___x_777_; 
v_val_775_ = lean_ctor_get(v_fst_771_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v_fst_771_, 1);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_val_775_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_val_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_766_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_766_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_788_, lean_object* v_indices_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_788_, v_indices_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec_ref(v_indices_789_);
lean_dec_ref(v_ys_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_796_, lean_object* v_as_797_, size_t v_sz_798_, size_t v_i_799_, lean_object* v_b_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v_a_796_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_800_);
return v___x_804_;
}
else
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref(v_b_800_);
v_a_805_ = lean_array_uget_borrowed(v_as_797_, v_i_799_);
v___x_806_ = l_Lean_Expr_fvarId_x21(v_a_805_);
lean_inc_ref(v_a_796_);
v___x_807_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_796_, v___x_806_, v___y_801_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_825_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_825_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_825_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_box(0);
v___x_813_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; size_t v___x_815_; size_t v___x_816_; 
lean_del_object(v___x_810_);
v___x_814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_799_, v___x_815_);
v_i_799_ = v___x_816_;
v_b_800_ = v___x_814_;
goto _start;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
lean_inc(v_a_805_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_a_796_);
lean_ctor_set(v___x_818_, 1, v_a_805_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_812_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_821_);
v___x_823_ = v___x_810_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v_a_796_);
v_a_826_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_807_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_807_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_834_, lean_object* v_as_835_, lean_object* v_sz_836_, lean_object* v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
size_t v_sz_boxed_841_; size_t v_i_boxed_842_; lean_object* v_res_843_; 
v_sz_boxed_841_ = lean_unbox_usize(v_sz_836_);
lean_dec(v_sz_836_);
v_i_boxed_842_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_834_, v_as_835_, v_sz_boxed_841_, v_i_boxed_842_, v_b_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v_as_835_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_844_, lean_object* v_as_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_848_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_a_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_b_848_);
v___x_856_ = lean_box(0);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_858_ = lean_array_uget_borrowed(v_as_845_, v_i_847_);
v_sz_859_ = lean_array_size(v_ys_844_);
v___x_860_ = ((size_t)0ULL);
lean_inc(v_a_858_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_858_, v_ys_844_, v_sz_859_, v___x_860_, v___x_857_, v___y_850_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_881_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_881_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_fst_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_879_; 
v_fst_866_ = lean_ctor_get(v_a_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_a_862_, 1);
lean_dec(v_unused_880_);
v___x_868_ = v_a_862_;
v_isShared_869_ = v_isSharedCheck_879_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_fst_866_);
lean_dec(v_a_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_879_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_fst_866_) == 0)
{
size_t v___x_870_; size_t v___x_871_; 
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_847_, v___x_870_);
v_i_847_ = v___x_871_;
v_b_848_ = v___x_857_;
goto _start;
}
else
{
lean_object* v___x_874_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_856_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_fst_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_856_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_874_);
v___x_876_ = v___x_864_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
else
{
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_882_, lean_object* v_as_883_, lean_object* v_sz_884_, lean_object* v_i_885_, lean_object* v_b_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_884_);
lean_dec(v_sz_884_);
v_i_boxed_893_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_882_, v_as_883_, v_sz_boxed_892_, v_i_boxed_893_, v_b_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec_ref(v_as_883_);
lean_dec_ref(v_ys_882_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_895_, lean_object* v_indParams_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; size_t v_sz_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_902_ = lean_box(0);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_904_ = lean_array_size(v_indParams_896_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_895_, v_indParams_896_, v_sz_904_, v___x_905_, v___x_903_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_919_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_919_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_919_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_919_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_fst_911_; 
v_fst_911_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v_fst_911_);
lean_dec(v_a_907_);
if (lean_obj_tag(v_fst_911_) == 0)
{
lean_object* v___x_913_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_902_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_902_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v_val_915_; lean_object* v___x_917_; 
v_val_915_ = lean_ctor_get(v_fst_911_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_fst_911_, 1);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_val_915_);
v___x_917_ = v___x_909_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_val_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_906_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_906_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_928_, lean_object* v_indParams_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_928_, v_indParams_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec_ref(v_indParams_929_);
lean_dec_ref(v_ys_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_936_, v_as_937_, v_sz_938_, v_i_939_, v_b_940_, v___y_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_947_, lean_object* v_as_948_, lean_object* v_sz_949_, lean_object* v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_949_);
lean_dec(v_sz_949_);
v_i_boxed_958_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_947_, v_as_948_, v_sz_boxed_957_, v_i_boxed_958_, v_b_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_as_948_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_panic_fn_borrowed(v___x_961_, v_msg_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_6888__overap_971_; lean_object* v___x_972_; 
v___f_970_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6888__overap_971_ = lean_panic_fn_borrowed(v___f_970_, v_msg_964_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
v___x_972_ = lean_apply_5(v___x_6888__overap_971_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, lean_box(0));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_ref_986_; lean_object* v___x_987_; lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_ref_986_ = lean_ctor_get(v___y_983_, 5);
v___x_987_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
lean_inc(v_ref_986_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_ref_986_);
lean_ctor_set(v___x_992_, 1, v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_1008_ = lean_unsigned_to_nat(107u);
v___x_1009_ = lean_unsigned_to_nat(97u);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1012_ = l_mkPanicMessageWithDecl(v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1013_, size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_bs_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1017_ == 0)
{
return v_bs_1016_;
}
else
{
lean_object* v_v_1018_; lean_object* v___x_1019_; lean_object* v_bs_x27_1020_; lean_object* v___y_1022_; lean_object* v___x_1027_; 
v_v_1018_ = lean_array_uget(v_bs_1016_, v_i_1015_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_bs_x27_1020_ = lean_array_uset(v_bs_1016_, v_i_1015_, v___x_1019_);
v___x_1027_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_1013_, v_v_1018_);
lean_dec(v_v_1018_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3);
v___x_1029_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1028_);
v___y_1022_ = v___x_1029_;
goto v___jp_1021_;
}
else
{
lean_object* v_val_1030_; 
v_val_1030_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___x_1027_, 1);
v___y_1022_ = v_val_1030_;
goto v___jp_1021_;
}
v___jp_1021_:
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1015_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1020_, v_i_1015_, v___y_1022_);
v_i_1015_ = v___x_1024_;
v_bs_1016_ = v___x_1025_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_bs_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1031_, v_sz_boxed_1035_, v_i_boxed_1036_, v_bs_1034_);
lean_dec_ref(v_xs_1031_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(lean_object* v_as_1038_, lean_object* v_a_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v_zero_1041_; uint8_t v_isZero_1042_; 
v_zero_1041_ = lean_unsigned_to_nat(0u);
v_isZero_1042_ = lean_nat_dec_eq(v_x_1040_, v_zero_1041_);
if (v_isZero_1042_ == 1)
{
lean_dec(v_x_1040_);
return v_isZero_1042_;
}
else
{
lean_object* v_one_1043_; lean_object* v_n_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_one_1043_ = lean_unsigned_to_nat(1u);
v_n_1044_ = lean_nat_sub(v_x_1040_, v_one_1043_);
lean_dec(v_x_1040_);
v___x_1045_ = lean_array_fget_borrowed(v_as_1038_, v_n_1044_);
v___x_1046_ = lean_expr_eqv(v_a_1039_, v___x_1045_);
if (v___x_1046_ == 0)
{
v_x_1040_ = v_n_1044_;
goto _start;
}
else
{
lean_dec(v_n_1044_);
return v_isZero_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_as_1048_, lean_object* v_a_1049_, lean_object* v_x_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1048_, v_a_1049_, v_x_1050_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_as_1048_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(lean_object* v_as_1053_, lean_object* v_i_1054_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_array_get_size(v_as_1053_);
v___x_1056_ = lean_nat_dec_lt(v_i_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
lean_dec(v_i_1054_);
v___x_1057_ = 1;
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_array_fget_borrowed(v_as_1053_, v_i_1054_);
lean_inc(v_i_1054_);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1053_, v___x_1058_, v_i_1054_);
if (v___x_1059_ == 0)
{
lean_dec(v_i_1054_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_i_1054_, v___x_1060_);
lean_dec(v_i_1054_);
v_i_1054_ = v___x_1061_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(lean_object* v_as_1063_, lean_object* v_i_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1063_, v_i_1064_);
lean_dec_ref(v_as_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_as_1067_){
_start:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_1067_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_as_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_as_1070_);
lean_dec_ref(v_as_1070_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_as_1073_, size_t v_i_1074_, size_t v_stop_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_eq(v_i_1074_, v_stop_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = 1;
v___x_1078_ = lean_array_uget_borrowed(v_as_1073_, v_i_1074_);
v___x_1079_ = l_Lean_Expr_isFVar(v___x_1078_);
if (v___x_1079_ == 0)
{
return v___x_1077_;
}
else
{
if (v___x_1076_ == 0)
{
size_t v___x_1080_; size_t v___x_1081_; 
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_add(v_i_1074_, v___x_1080_);
v_i_1074_ = v___x_1081_;
goto _start;
}
else
{
return v___x_1077_;
}
}
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = 0;
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_){
_start:
{
size_t v_i_boxed_1087_; size_t v_stop_boxed_1088_; uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_i_boxed_1087_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1088_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_as_1084_, v_i_boxed_1087_, v_stop_boxed_1088_);
lean_dec_ref(v_as_1084_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(lean_object* v_xs_1091_, lean_object* v_v_1092_, lean_object* v_i_1093_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_array_get_size(v_xs_1091_);
v___x_1095_ = lean_nat_dec_lt(v_i_1093_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec(v_i_1093_);
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_fget_borrowed(v_xs_1091_, v_i_1093_);
v___x_1098_ = lean_name_eq(v___x_1097_, v_v_1092_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v_i_1093_, v___x_1099_);
lean_dec(v_i_1093_);
v_i_1093_ = v___x_1100_;
goto _start;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_i_1093_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(lean_object* v_xs_1103_, lean_object* v_v_1104_, lean_object* v_i_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1103_, v_v_1104_, v_i_1105_);
lean_dec(v_v_1104_);
lean_dec_ref(v_xs_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(lean_object* v_xs_1107_, lean_object* v_v_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_1107_, v_v_1108_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(lean_object* v_xs_1111_, lean_object* v_v_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1111_, v_v_1112_);
lean_dec(v_v_1112_);
lean_dec_ref(v_xs_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_xs_1114_, lean_object* v_v_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_1114_, v_v_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_val_1118_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1116_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v___x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_xs_1126_, lean_object* v_v_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_xs_1126_, v_v_1127_);
lean_dec(v_v_1127_);
lean_dec_ref(v_xs_1126_);
return v_res_1128_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1140_ = lean_unsigned_to_nat(59u);
v___x_1141_ = lean_unsigned_to_nat(96u);
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1144_ = l_mkPanicMessageWithDecl(v___x_1143_, v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1169_; lean_object* v_dummy_1170_; 
v___x_1169_ = lean_box(0);
v_dummy_1170_ = l_Lean_Expr_sort___override(v___x_1169_);
return v_dummy_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1176_ = lean_unsigned_to_nat(2u);
v___x_1177_ = lean_unsigned_to_nat(68u);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1));
v___x_1179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_1180_ = l_mkPanicMessageWithDecl(v___x_1179_, v___x_1178_, v___x_1177_, v___x_1176_, v___x_1175_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1186_ = l_Lean_stringToMessageData(v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1193_, lean_object* v_fixedParamPerm_1194_, lean_object* v_xs_1195_, lean_object* v_i_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v_lower_1341_; lean_object* v_upper_1342_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_array_get_size(v_fixedParamPerm_1194_);
v___x_1428_ = lean_array_get_size(v_xs_1195_);
v___x_1429_ = lean_nat_dec_eq(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___x_1430_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1431_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1430_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
return v___x_1431_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_lt(v_i_1196_, v___x_1428_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___x_1433_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_i_1196_, v___x_1434_);
lean_dec(v_i_1196_);
v___x_1436_ = l_Nat_reprFast(v___x_1435_);
v___x_1437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
v___x_1438_ = l_Lean_MessageData_ofFormat(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1433_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Nat_reprFast(v___x_1428_);
v___x_1443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___x_1444_ = l_Lean_MessageData_ofFormat(v___x_1443_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1441_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1447_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
return v___x_1448_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1194_, v_i_1196_);
if (v___x_1449_ == 0)
{
v___y_1400_ = v_a_1197_;
v___y_1401_ = v_a_1198_;
v___y_1402_ = v_a_1199_;
v___y_1403_ = v_a_1200_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___x_1450_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1451_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1450_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
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
}
v___jp_1202_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1208_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1207_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1208_;
}
v___jp_1209_:
{
uint8_t v___x_1221_; 
v___x_1221_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1219_);
if (v___x_1221_ == 0)
{
lean_object* v_name_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_name_1222_ = lean_ctor_get(v___y_1220_, 0);
lean_inc(v_name_1222_);
lean_dec_ref(v___y_1220_);
v___x_1223_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1224_ = l_Lean_MessageData_ofName(v_name_1222_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_indentExpr(v___y_1218_);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1229_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1194_, v_xs_1195_);
v___x_1232_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1231_, v___y_1219_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1231_, v___y_1216_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1285_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1285_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1285_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_object* v_name_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v___y_1218_);
v_name_1239_ = lean_ctor_get(v___y_1220_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___y_1220_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; lean_object* v_unused_1261_; 
v_unused_1260_ = lean_ctor_get(v___y_1220_, 2);
lean_dec(v_unused_1260_);
v_unused_1261_ = lean_ctor_get(v___y_1220_, 1);
lean_dec(v_unused_1261_);
v___x_1241_ = v___y_1220_;
v_isShared_1242_ = v_isSharedCheck_1259_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_name_1239_);
lean_dec(v___y_1220_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1259_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_array_mk(v___y_1211_);
v___x_1244_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___x_1243_, v_name_1239_);
lean_dec(v_name_1239_);
lean_dec_ref(v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_val_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v_sz_1246_ = lean_array_size(v___y_1219_);
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1195_, v_sz_1246_, v___x_1247_, v___y_1219_);
v___x_1249_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1213_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 2, v___y_1216_);
lean_ctor_set(v___x_1241_, 1, v___y_1210_);
lean_ctor_set(v___x_1241_, 0, v___x_1249_);
v___x_1251_ = v___x_1241_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___y_1210_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v___y_1216_);
v___x_1251_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1252_, 0, v_fnName_1193_);
lean_ctor_set(v___x_1252_, 1, v_fixedParamPerm_1194_);
lean_ctor_set(v___x_1252_, 2, v_i_1196_);
lean_ctor_set(v___x_1252_, 3, v___x_1248_);
lean_ctor_set(v___x_1252_, 4, v___x_1251_);
lean_ctor_set(v___x_1252_, 5, v_val_1245_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1252_);
v___x_1254_ = v___x_1237_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v___x_1244_);
lean_del_object(v___x_1241_);
lean_del_object(v___x_1237_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___x_1257_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1258_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1257_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
return v___x_1258_;
}
}
}
else
{
lean_object* v_val_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1237_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_val_1262_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_a_1235_, 1);
v_fst_1263_ = lean_ctor_get(v_val_1262_, 0);
v_snd_1264_ = lean_ctor_get(v_val_1262_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_val_1262_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1266_ = v_val_1262_;
v_isShared_1267_ = v_isSharedCheck_1284_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v_val_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1284_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1268_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1269_ = l_Lean_indentExpr(v___y_1218_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 7);
lean_ctor_set(v___x_1266_, 1, v___x_1269_);
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1272_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_indentExpr(v_fst_1263_);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_indentExpr(v_snd_1264_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1281_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_a_1286_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1234_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1234_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_val_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v___x_1231_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_val_1294_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v_a_1233_, 1);
v_fst_1295_ = lean_ctor_get(v_val_1294_, 0);
v_snd_1296_ = lean_ctor_get(v_val_1294_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_val_1294_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1298_ = v_val_1294_;
v_isShared_1299_ = v_isSharedCheck_1319_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_snd_1296_);
lean_inc(v_fst_1295_);
lean_dec(v_val_1294_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1319_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_name_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v_name_1300_ = lean_ctor_get(v___y_1220_, 0);
lean_inc(v_name_1300_);
lean_dec_ref(v___y_1220_);
v___x_1301_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1302_ = l_Lean_MessageData_ofName(v_name_1300_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 7);
lean_ctor_set(v___x_1298_, 1, v___x_1302_);
lean_ctor_set(v___x_1298_, 0, v___x_1301_);
v___x_1304_ = v___x_1298_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_indentExpr(v___y_1218_);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_indentExpr(v_fst_1295_);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_indentExpr(v_snd_1296_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1316_, v___y_1215_, v___y_1217_, v___y_1212_, v___y_1214_);
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___x_1231_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_a_1320_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1232_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1232_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
v___jp_1328_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1343_ = l_Array_toSubarray___redArg(v___y_1329_, v_lower_1341_, v_upper_1342_);
v___x_1344_ = l_Subarray_copy___redArg(v___x_1343_);
v___x_1345_ = lean_array_get_size(v___x_1344_);
v___x_1346_ = lean_nat_dec_lt(v___y_1336_, v___x_1345_);
lean_dec(v___y_1336_);
if (v___x_1346_ == 0)
{
v___y_1210_ = v___y_1330_;
v___y_1211_ = v___y_1338_;
v___y_1212_ = v___y_1339_;
v___y_1213_ = v___y_1331_;
v___y_1214_ = v___y_1332_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1340_;
v___y_1218_ = v___y_1335_;
v___y_1219_ = v___x_1344_;
v___y_1220_ = v___y_1337_;
goto v___jp_1209_;
}
else
{
if (v___x_1346_ == 0)
{
v___y_1210_ = v___y_1330_;
v___y_1211_ = v___y_1338_;
v___y_1212_ = v___y_1339_;
v___y_1213_ = v___y_1331_;
v___y_1214_ = v___y_1332_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1340_;
v___y_1218_ = v___y_1335_;
v___y_1219_ = v___x_1344_;
v___y_1220_ = v___y_1337_;
goto v___jp_1209_;
}
else
{
size_t v___x_1347_; size_t v___x_1348_; uint8_t v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1345_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v___x_1344_, v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
v___y_1210_ = v___y_1330_;
v___y_1211_ = v___y_1338_;
v___y_1212_ = v___y_1339_;
v___y_1213_ = v___y_1331_;
v___y_1214_ = v___y_1332_;
v___y_1215_ = v___y_1333_;
v___y_1216_ = v___y_1334_;
v___y_1217_ = v___y_1340_;
v___y_1218_ = v___y_1335_;
v___y_1219_ = v___x_1344_;
v___y_1220_ = v___y_1337_;
goto v___jp_1209_;
}
else
{
lean_object* v_name_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1344_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1334_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_name_1350_ = lean_ctor_get(v___y_1337_, 0);
lean_inc(v_name_1350_);
lean_dec_ref(v___y_1337_);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1352_ = l_Lean_MessageData_ofName(v_name_1350_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_indentExpr(v___y_1335_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1357_, v___y_1333_, v___y_1340_, v___y_1339_, v___y_1332_);
return v___x_1358_;
}
}
}
}
v___jp_1359_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = l_Lean_LocalDecl_type(v___y_1360_);
lean_dec_ref(v___y_1360_);
v___x_1366_ = l_Lean_Meta_whnfD(v___x_1365_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lean_Expr_getAppFn(v_a_1367_);
if (lean_obj_tag(v___x_1368_) == 4)
{
lean_object* v_declName_1369_; lean_object* v_us_1370_; lean_object* v___x_1371_; lean_object* v_env_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v_declName_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_declName_1369_);
v_us_1370_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_us_1370_);
lean_dec_ref_known(v___x_1368_, 2);
v___x_1371_ = lean_st_ref_get(v___y_1364_);
v_env_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_env_1372_);
lean_dec(v___x_1371_);
v___x_1373_ = 0;
v___x_1374_ = l_Lean_Environment_find_x3f(v_env_1372_, v_declName_1369_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec(v_us_1370_);
lean_dec(v_a_1367_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
goto v___jp_1202_;
}
else
{
lean_object* v_val_1375_; 
v_val_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v___x_1374_, 1);
if (lean_obj_tag(v_val_1375_) == 5)
{
lean_object* v_val_1376_; lean_object* v_toConstantVal_1377_; lean_object* v_numParams_1378_; lean_object* v_all_1379_; lean_object* v_nargs_1380_; lean_object* v_dummy_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_val_1376_ = lean_ctor_get(v_val_1375_, 0);
lean_inc_ref(v_val_1376_);
lean_dec_ref_known(v_val_1375_, 1);
v_toConstantVal_1377_ = lean_ctor_get(v_val_1376_, 0);
lean_inc_ref(v_toConstantVal_1377_);
v_numParams_1378_ = lean_ctor_get(v_val_1376_, 1);
v_all_1379_ = lean_ctor_get(v_val_1376_, 3);
lean_inc(v_all_1379_);
v_nargs_1380_ = l_Lean_Expr_getAppNumArgs(v_a_1367_);
v_dummy_1381_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1380_);
v___x_1382_ = lean_mk_array(v_nargs_1380_, v_dummy_1381_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_sub(v_nargs_1380_, v___x_1383_);
lean_dec(v_nargs_1380_);
lean_inc(v_a_1367_);
v___x_1385_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1367_, v___x_1382_, v___x_1384_);
v___x_1386_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1378_);
lean_inc_ref(v___x_1385_);
v___x_1387_ = l_Array_toSubarray___redArg(v___x_1385_, v___x_1386_, v_numParams_1378_);
v___x_1388_ = l_Subarray_copy___redArg(v___x_1387_);
v___x_1389_ = lean_array_get_size(v___x_1385_);
v___x_1390_ = lean_nat_dec_le(v_numParams_1378_, v___x_1386_);
if (v___x_1390_ == 0)
{
lean_inc(v_numParams_1378_);
v___y_1329_ = v___x_1385_;
v___y_1330_ = v_us_1370_;
v___y_1331_ = v_val_1376_;
v___y_1332_ = v___y_1364_;
v___y_1333_ = v___y_1361_;
v___y_1334_ = v___x_1388_;
v___y_1335_ = v_a_1367_;
v___y_1336_ = v___x_1386_;
v___y_1337_ = v_toConstantVal_1377_;
v___y_1338_ = v_all_1379_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1362_;
v_lower_1341_ = v_numParams_1378_;
v_upper_1342_ = v___x_1389_;
goto v___jp_1328_;
}
else
{
v___y_1329_ = v___x_1385_;
v___y_1330_ = v_us_1370_;
v___y_1331_ = v_val_1376_;
v___y_1332_ = v___y_1364_;
v___y_1333_ = v___y_1361_;
v___y_1334_ = v___x_1388_;
v___y_1335_ = v_a_1367_;
v___y_1336_ = v___x_1386_;
v___y_1337_ = v_toConstantVal_1377_;
v___y_1338_ = v_all_1379_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1362_;
v_lower_1341_ = v___x_1386_;
v_upper_1342_ = v___x_1389_;
goto v___jp_1328_;
}
}
else
{
lean_dec(v_val_1375_);
lean_dec(v_us_1370_);
lean_dec(v_a_1367_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
goto v___jp_1202_;
}
}
}
else
{
lean_dec_ref(v___x_1368_);
lean_dec(v_a_1367_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___y_1203_ = v___y_1361_;
v___y_1204_ = v___y_1362_;
v___y_1205_ = v___y_1363_;
v___y_1206_ = v___y_1364_;
goto v___jp_1202_;
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_a_1391_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1366_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1366_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
v___jp_1399_:
{
lean_object* v_x_1404_; lean_object* v___x_1405_; 
v_x_1404_ = lean_array_fget_borrowed(v_xs_1195_, v_i_1196_);
v___x_1405_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1404_, v___y_1400_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = 0;
v___x_1408_ = l_Lean_LocalDecl_isLet(v_a_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
v___y_1360_ = v_a_1406_;
v___y_1361_ = v___y_1400_;
v___y_1362_ = v___y_1401_;
v___y_1363_ = v___y_1402_;
v___y_1364_ = v___y_1403_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_a_1406_);
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v___x_1409_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1410_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1409_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_i_1196_);
lean_dec_ref(v_fixedParamPerm_1194_);
lean_dec(v_fnName_1193_);
v_a_1419_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1405_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1405_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1460_, lean_object* v_fixedParamPerm_1461_, lean_object* v_xs_1462_, lean_object* v_i_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1460_, v_fixedParamPerm_1461_, v_xs_1462_, v_i_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v_xs_1462_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_msg_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1478_, v_msg_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(lean_object* v_as_1486_, lean_object* v_a_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_1486_, v_a_1487_, v_x_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(lean_object* v_as_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
uint8_t v_res_1495_; lean_object* v_r_1496_; 
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(v_as_1491_, v_a_1492_, v_x_1493_, v_x_1494_);
lean_dec_ref(v_a_1492_);
lean_dec_ref(v_as_1491_);
v_r_1496_ = lean_box(v_res_1495_);
return v_r_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1497_, lean_object* v_e_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l_Lean_indentD(v_e_1498_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1497_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1501_, lean_object* v_fnName_1502_, lean_object* v_fixedParamPerm_1503_, lean_object* v_args_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1501_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1502_, v_fixedParamPerm_1503_, v_args_1504_, v_a_1511_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1512_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_fixedParamPerm_1503_);
lean_dec(v_fnName_1502_);
v_a_1513_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1510_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1510_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1521_, lean_object* v_fnName_1522_, lean_object* v_fixedParamPerm_1523_, lean_object* v_args_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1521_, v_fnName_1522_, v_fixedParamPerm_1523_, v_args_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_args_1524_);
return v_res_1530_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1541_ = l_Lean_MessageData_ofFormat(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1542_, lean_object* v_fnName_1543_, lean_object* v_fixedParamPerm_1544_, lean_object* v_args_1545_, lean_object* v_a_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_fst_1554_; lean_object* v_snd_1555_; uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_lt(v_a_1546_, v_upperBound_1542_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_dec(v_a_1546_);
lean_dec_ref(v_fixedParamPerm_1544_);
lean_dec(v_fnName_1543_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_b_1547_);
return v___x_1561_;
}
else
{
lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1608_; 
v_fst_1562_ = lean_ctor_get(v_b_1547_, 0);
v_snd_1563_ = lean_ctor_get(v_b_1547_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_b_1547_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1565_ = v_b_1547_;
v_isShared_1566_ = v_isSharedCheck_1608_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snd_1563_);
lean_inc(v_fst_1562_);
lean_dec(v_b_1547_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1608_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; 
lean_inc(v_a_1546_);
lean_inc_ref(v_fixedParamPerm_1544_);
lean_inc(v_fnName_1543_);
v___x_1567_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1543_, v_fixedParamPerm_1544_, v_args_1545_, v_a_1546_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
lean_del_object(v___x_1565_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = lean_array_push(v_fst_1562_, v_a_1568_);
v_fst_1554_ = v___x_1569_;
v_snd_1555_ = v_snd_1563_;
goto v___jp_1553_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1607_; 
v_a_1570_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1572_ = v___x_1567_;
v_isShared_1573_ = v_isSharedCheck_1607_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1567_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1607_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint8_t v___y_1575_; uint8_t v___x_1605_; 
v___x_1605_ = l_Lean_Exception_isInterrupt(v_a_1570_);
if (v___x_1605_ == 0)
{
uint8_t v___x_1606_; 
lean_inc(v_a_1570_);
v___x_1606_ = l_Lean_Exception_isRuntime(v_a_1570_);
v___y_1575_ = v___x_1606_;
goto v___jp_1574_;
}
else
{
v___y_1575_ = v___x_1605_;
goto v___jp_1574_;
}
v___jp_1574_:
{
if (v___y_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_del_object(v___x_1572_);
v___x_1576_ = l_Lean_Elab_Structural_prettyParam(v_args_1545_, v_a_1546_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 7);
lean_ctor_set(v___x_1565_, 1, v_a_1577_);
lean_ctor_set(v___x_1565_, 0, v___x_1578_);
v___x_1580_ = v___x_1565_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1577_);
v___x_1580_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
lean_inc(v_fnName_1543_);
v___x_1583_ = l_Lean_MessageData_ofName(v_fnName_1543_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_Exception_toMessageData(v_a_1570_);
v___x_1588_ = l_Lean_indentD(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1586_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_snd_1563_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v_fst_1554_ = v_fst_1562_;
v_snd_1555_ = v___x_1592_;
goto v___jp_1553_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1570_);
lean_del_object(v___x_1565_);
lean_dec(v_snd_1563_);
lean_dec(v_fst_1562_);
lean_dec(v_a_1546_);
lean_dec_ref(v_fixedParamPerm_1544_);
lean_dec(v_fnName_1543_);
v_a_1594_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1576_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1576_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v___x_1603_; 
lean_del_object(v___x_1565_);
lean_dec(v_snd_1563_);
lean_dec(v_fst_1562_);
lean_dec(v_a_1546_);
lean_dec_ref(v_fixedParamPerm_1544_);
lean_dec(v_fnName_1543_);
if (v_isShared_1573_ == 0)
{
v___x_1603_ = v___x_1572_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1570_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
v___jp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_fst_1554_);
lean_ctor_set(v___x_1556_, 1, v_snd_1555_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_a_1546_, v___x_1557_);
lean_dec(v_a_1546_);
v_a_1546_ = v___x_1558_;
v_b_1547_ = v___x_1556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1609_, lean_object* v_fnName_1610_, lean_object* v_fixedParamPerm_1611_, lean_object* v_args_1612_, lean_object* v_a_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1609_, v_fnName_1610_, v_fixedParamPerm_1611_, v_args_1612_, v_a_1613_, v_b_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_args_1612_);
lean_dec(v_upperBound_1609_);
return v_res_1620_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1621_; double v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_float_of_nat(v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1624_, lean_object* v_msg_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_ref_1631_; lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1677_; 
v_ref_1631_ = lean_ctor_get(v___y_1628_, 5);
v___x_1632_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1677_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1677_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v_traceState_1638_; lean_object* v_env_1639_; lean_object* v_nextMacroScope_1640_; lean_object* v_ngen_1641_; lean_object* v_auxDeclNGen_1642_; lean_object* v_cache_1643_; lean_object* v_messages_1644_; lean_object* v_infoState_1645_; lean_object* v_snapshotTasks_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1676_; 
v___x_1637_ = lean_st_ref_take(v___y_1629_);
v_traceState_1638_ = lean_ctor_get(v___x_1637_, 4);
v_env_1639_ = lean_ctor_get(v___x_1637_, 0);
v_nextMacroScope_1640_ = lean_ctor_get(v___x_1637_, 1);
v_ngen_1641_ = lean_ctor_get(v___x_1637_, 2);
v_auxDeclNGen_1642_ = lean_ctor_get(v___x_1637_, 3);
v_cache_1643_ = lean_ctor_get(v___x_1637_, 5);
v_messages_1644_ = lean_ctor_get(v___x_1637_, 6);
v_infoState_1645_ = lean_ctor_get(v___x_1637_, 7);
v_snapshotTasks_1646_ = lean_ctor_get(v___x_1637_, 8);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1648_ = v___x_1637_;
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snapshotTasks_1646_);
lean_inc(v_infoState_1645_);
lean_inc(v_messages_1644_);
lean_inc(v_cache_1643_);
lean_inc(v_traceState_1638_);
lean_inc(v_auxDeclNGen_1642_);
lean_inc(v_ngen_1641_);
lean_inc(v_nextMacroScope_1640_);
lean_inc(v_env_1639_);
lean_dec(v___x_1637_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint64_t v_tid_1650_; lean_object* v_traces_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1675_; 
v_tid_1650_ = lean_ctor_get_uint64(v_traceState_1638_, sizeof(void*)*1);
v_traces_1651_ = lean_ctor_get(v_traceState_1638_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_traceState_1638_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1653_ = v_traceState_1638_;
v_isShared_1654_ = v_isSharedCheck_1675_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_traces_1651_);
lean_dec(v_traceState_1638_);
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
lean_ctor_set(v___x_1659_, 0, v_cls_1624_);
lean_ctor_set(v___x_1659_, 1, v___x_1655_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
lean_ctor_set_float(v___x_1659_, sizeof(void*)*3, v___x_1656_);
lean_ctor_set_float(v___x_1659_, sizeof(void*)*3 + 8, v___x_1656_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*3 + 16, v___x_1657_);
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1661_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v_a_1633_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
lean_inc(v_ref_1631_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v_ref_1631_);
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
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_env_1639_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_nextMacroScope_1640_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_ngen_1641_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_auxDeclNGen_1642_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1673_, 5, v_cache_1643_);
lean_ctor_set(v_reuseFailAlloc_1673_, 6, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1673_, 7, v_infoState_1645_);
lean_ctor_set(v_reuseFailAlloc_1673_, 8, v_snapshotTasks_1646_);
v___x_1667_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_st_ref_set(v___y_1629_, v___x_1667_);
v___x_1669_ = lean_box(0);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1669_);
v___x_1671_ = v___x_1635_;
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
lean_dec_ref_known(v_termMeasure_x3f_1714_, 1);
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
lean_dec_ref_known(v___x_1747_, 14);
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
lean_dec_ref_known(v___x_1799_, 1);
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
lean_dec_ref_known(v___x_2331_, 1);
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
lean_object* v_a_2311_; 
lean_del_object(v___x_2305_);
v_a_2311_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v_a_2303_, 1);
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
v___x_2509_ = lean_unsigned_to_nat(109u);
v___x_2510_ = lean_unsigned_to_nat(216u);
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
lean_dec_ref_known(v___x_2528_, 1);
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
lean_dec_ref_known(v___x_2550_, 1);
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
uint8_t v_a_9779__boxed_2599_; size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_a_9779__boxed_2599_ = lean_unbox(v_a_2594_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2598_);
lean_dec(v_stop_2598_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9779__boxed_2599_, v___x_2595_, v_as_2596_, v_i_boxed_2600_, v_stop_boxed_2601_);
lean_dec_ref(v_as_2596_);
lean_dec(v___x_2595_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2604_, lean_object* v___x_2605_, lean_object* v_ys_2606_, lean_object* v___x_2607_, lean_object* v_recArgInfo_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v_group_2611_, lean_object* v_as_2612_, size_t v_sz_2613_, size_t v_i_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_a_2622_; uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_lt(v_i_2614_, v_sz_2613_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_b_2615_);
return v___x_2627_;
}
else
{
lean_object* v_snd_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2786_; 
v_snd_2628_ = lean_ctor_get(v_b_2615_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_b_2615_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v_b_2615_, 0);
lean_dec(v_unused_2787_);
v___x_2630_ = v_b_2615_;
v_isShared_2631_ = v_isSharedCheck_2786_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snd_2628_);
lean_dec(v_b_2615_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2786_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_next_2632_; lean_object* v_upperBound_2633_; lean_object* v___x_2634_; 
v_next_2632_ = lean_ctor_get(v_snd_2628_, 0);
lean_inc(v_next_2632_);
v_upperBound_2633_ = lean_ctor_get(v_snd_2628_, 1);
v___x_2634_ = lean_box(0);
if (lean_obj_tag(v_next_2632_) == 0)
{
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
goto v___jp_2635_;
}
else
{
lean_object* v_val_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2785_; 
v_val_2640_ = lean_ctor_get(v_next_2632_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_next_2632_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2642_ = v_next_2632_;
v_isShared_2643_ = v_isSharedCheck_2785_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_val_2640_);
lean_dec(v_next_2632_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2785_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_nat_dec_lt(v_val_2640_, v_upperBound_2633_);
if (v___x_2644_ == 0)
{
lean_del_object(v___x_2642_);
lean_dec(v_val_2640_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
goto v___jp_2635_;
}
else
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_upperBound_2633_);
lean_del_object(v___x_2630_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_snd_2628_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; 
v_unused_2783_ = lean_ctor_get(v_snd_2628_, 1);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_snd_2628_, 0);
lean_dec(v_unused_2784_);
v___x_2646_ = v_snd_2628_;
v_isShared_2647_ = v_isSharedCheck_2782_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v_snd_2628_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2782_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; 
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc_ref(v___x_2604_);
v___x_2648_ = lean_infer_type(v___x_2604_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = l_Lean_Meta_whnfD(v_a_2649_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_a_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_a_2652_ = lean_array_uget_borrowed(v_as_2612_, v_i_2614_);
v___x_2653_ = 0;
lean_inc(v_a_2652_);
v___x_2654_ = l_Lean_Meta_forallMetaTelescope(v_a_2652_, v___x_2653_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_snd_2656_; lean_object* v_fst_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2757_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v_snd_2656_ = lean_ctor_get(v_a_2655_, 1);
v_fst_2657_ = lean_ctor_get(v_a_2655_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2659_ = v_a_2655_;
v_isShared_2660_ = v_isSharedCheck_2757_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2657_);
lean_dec(v_a_2655_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2757_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_snd_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2755_; 
v_snd_2661_ = lean_ctor_get(v_snd_2656_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_snd_2656_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_snd_2656_, 0);
lean_dec(v_unused_2756_);
v___x_2663_ = v_snd_2656_;
v_isShared_2664_ = v_isSharedCheck_2755_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_snd_2661_);
lean_dec(v_snd_2656_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2755_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2661_, v_a_2651_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_val_2640_, v___x_2667_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2668_);
v___x_2670_ = v___x_2642_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2670_);
v___x_2672_ = v___x_2646_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_upperBound_2633_);
v___x_2672_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_unbox(v_a_2666_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2675_; 
lean_dec(v_a_2666_);
lean_del_object(v___x_2659_);
lean_dec(v_fst_2657_);
lean_dec(v_val_2640_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2672_);
lean_ctor_set(v___x_2663_, 0, v___x_2634_);
v___x_2675_ = v___x_2663_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2672_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v_a_2622_ = v___x_2675_;
goto v___jp_2621_;
}
}
else
{
size_t v_sz_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v_sz_2677_ = lean_array_size(v_fst_2657_);
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2677_, v___x_2678_, v_fst_2657_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_nat_dec_eq(v___x_2605_, v___x_2685_);
v___x_2732_ = lean_array_get_size(v_a_2680_);
v___x_2733_ = lean_nat_dec_lt(v___x_2685_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v_a_2666_);
goto v___jp_2687_;
}
else
{
if (v___x_2733_ == 0)
{
lean_dec(v_a_2666_);
goto v___jp_2687_;
}
else
{
size_t v___x_2734_; uint8_t v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = lean_usize_of_nat(v___x_2732_);
v___x_2735_ = lean_unbox(v_a_2666_);
lean_dec(v_a_2666_);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2735_, v___x_2605_, v_a_2680_, v___x_2678_, v___x_2734_);
if (v___x_2736_ == 0)
{
goto v___jp_2687_;
}
else
{
if (v___x_2686_ == 0)
{
lean_dec(v_a_2680_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2640_);
goto v___jp_2681_;
}
else
{
goto v___jp_2687_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2683_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2672_);
lean_ctor_set(v___x_2663_, 0, v___x_2634_);
v___x_2683_ = v___x_2663_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2672_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
v_a_2622_ = v___x_2683_;
goto v___jp_2621_;
}
}
v___jp_2687_:
{
if (v___x_2686_ == 0)
{
uint8_t v___x_2688_; 
lean_del_object(v___x_2663_);
v___x_2688_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2680_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2690_; 
lean_dec(v_a_2680_);
lean_dec(v_val_2640_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2672_);
lean_ctor_set(v___x_2659_, 0, v___x_2634_);
v___x_2690_ = v___x_2659_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2672_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
v_a_2622_ = v___x_2690_;
goto v___jp_2621_;
}
}
else
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2606_, v_a_2680_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2723_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2723_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2723_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v___x_2698_; 
lean_dec_ref_known(v_a_2693_, 1);
lean_del_object(v___x_2695_);
lean_dec(v_a_2680_);
lean_dec(v_val_2640_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2672_);
lean_ctor_set(v___x_2659_, 0, v___x_2634_);
v___x_2698_ = v___x_2659_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2672_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
v_a_2622_ = v___x_2698_;
goto v___jp_2621_;
}
}
else
{
lean_object* v_fnName_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_a_2693_);
lean_dec_ref(v___x_2604_);
v_fnName_2700_ = lean_ctor_get(v_recArgInfo_2608_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_recArgInfo_2608_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; lean_object* v_unused_2719_; lean_object* v_unused_2720_; lean_object* v_unused_2721_; lean_object* v_unused_2722_; 
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2608_, 5);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_recArgInfo_2608_, 4);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_recArgInfo_2608_, 3);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_recArgInfo_2608_, 2);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_recArgInfo_2608_, 1);
lean_dec(v_unused_2722_);
v___x_2702_ = v_recArgInfo_2608_;
v_isShared_2703_ = v_isSharedCheck_2717_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_fnName_2700_);
lean_dec(v_recArgInfo_2608_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2717_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
size_t v_sz_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v_sz_2704_ = lean_array_size(v_a_2680_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2607_, v_sz_2704_, v___x_2678_, v_a_2680_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 5, v_val_2640_);
lean_ctor_set(v___x_2702_, 4, v_group_2611_);
lean_ctor_set(v___x_2702_, 3, v___x_2705_);
lean_ctor_set(v___x_2702_, 2, v___x_2610_);
lean_ctor_set(v___x_2702_, 1, v___x_2609_);
v___x_2707_ = v___x_2702_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_fnName_2700_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2716_, 4, v_group_2611_);
lean_ctor_set(v_reuseFailAlloc_2716_, 5, v_val_2640_);
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
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2672_);
lean_ctor_set(v___x_2659_, 0, v___x_2709_);
v___x_2711_ = v___x_2659_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2672_);
v___x_2711_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2711_);
v___x_2713_ = v___x_2695_;
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
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_a_2680_);
lean_dec_ref(v___x_2672_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2640_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2724_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2692_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2692_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_dec(v_a_2680_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2640_);
goto v___jp_2681_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___x_2672_);
lean_dec(v_a_2666_);
lean_del_object(v___x_2663_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2640_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2737_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2679_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2679_);
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
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_del_object(v___x_2663_);
lean_del_object(v___x_2659_);
lean_dec(v_fst_2657_);
lean_del_object(v___x_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_val_2640_);
lean_dec(v_upperBound_2633_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2747_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2665_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2665_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2651_);
lean_del_object(v___x_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_val_2640_);
lean_dec(v_upperBound_2633_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2758_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2654_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2654_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_del_object(v___x_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_val_2640_);
lean_dec(v_upperBound_2633_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2766_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2650_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2650_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_del_object(v___x_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_val_2640_);
lean_dec(v_upperBound_2633_);
lean_dec_ref(v_group_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_recArgInfo_2608_);
lean_dec_ref(v___x_2604_);
v_a_2774_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2648_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2648_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2637_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2634_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_snd_2628_);
v___x_2637_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
}
}
v___jp_2621_:
{
size_t v___x_2623_; size_t v___x_2624_; 
v___x_2623_ = ((size_t)1ULL);
v___x_2624_ = lean_usize_add(v_i_2614_, v___x_2623_);
v_i_2614_ = v___x_2624_;
v_b_2615_ = v_a_2622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2788_ = _args[0];
lean_object* v___x_2789_ = _args[1];
lean_object* v_ys_2790_ = _args[2];
lean_object* v___x_2791_ = _args[3];
lean_object* v_recArgInfo_2792_ = _args[4];
lean_object* v___x_2793_ = _args[5];
lean_object* v___x_2794_ = _args[6];
lean_object* v_group_2795_ = _args[7];
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
v_res_2807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2788_, v___x_2789_, v_ys_2790_, v___x_2791_, v_recArgInfo_2792_, v___x_2793_, v___x_2794_, v_group_2795_, v_as_2796_, v_sz_boxed_2805_, v_i_boxed_2806_, v_b_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v_as_2796_);
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_ys_2790_);
lean_dec(v___x_2789_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v_ys_2811_, lean_object* v_recArgInfo_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_group_2815_, lean_object* v_as_2816_, size_t v_sz_2817_, size_t v_i_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
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
lean_object* v_snd_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2990_; 
v_snd_2832_ = lean_ctor_get(v_b_2819_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_b_2819_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_b_2819_, 0);
lean_dec(v_unused_2991_);
v___x_2834_ = v_b_2819_;
v_isShared_2835_ = v_isSharedCheck_2990_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snd_2832_);
lean_dec(v_b_2819_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2990_;
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
lean_object* v_val_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2989_; 
v_val_2844_ = lean_ctor_get(v_next_2836_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_next_2836_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2846_ = v_next_2836_;
v_isShared_2847_ = v_isSharedCheck_2989_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_val_2844_);
lean_dec(v_next_2836_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2989_;
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
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2986_; 
lean_inc(v_upperBound_2837_);
lean_del_object(v___x_2834_);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_snd_2832_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; lean_object* v_unused_2988_; 
v_unused_2987_ = lean_ctor_get(v_snd_2832_, 1);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_snd_2832_, 0);
lean_dec(v_unused_2988_);
v___x_2850_ = v_snd_2832_;
v_isShared_2851_ = v_isSharedCheck_2986_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v_snd_2832_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2986_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; 
lean_inc(v___y_2823_);
lean_inc_ref(v___y_2822_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc_ref(v___x_2808_);
v___x_2852_ = lean_infer_type(v___x_2808_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_Meta_whnfD(v_a_2853_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_a_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v_a_2856_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
v___x_2857_ = 0;
lean_inc(v_a_2856_);
v___x_2858_ = l_Lean_Meta_forallMetaTelescope(v_a_2856_, v___x_2857_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_snd_2860_; lean_object* v_fst_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2961_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v_snd_2860_ = lean_ctor_get(v_a_2859_, 1);
v_fst_2861_ = lean_ctor_get(v_a_2859_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2863_ = v_a_2859_;
v_isShared_2864_ = v_isSharedCheck_2961_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_snd_2860_);
lean_inc(v_fst_2861_);
lean_dec(v_a_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2961_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v_snd_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2959_; 
v_snd_2865_ = lean_ctor_get(v_snd_2860_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_snd_2860_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_snd_2860_, 0);
lean_dec(v_unused_2960_);
v___x_2867_ = v_snd_2860_;
v_isShared_2868_ = v_isSharedCheck_2959_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_snd_2865_);
lean_dec(v_snd_2860_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2959_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2865_, v_a_2855_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_add(v_val_2844_, v___x_2871_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2872_);
v___x_2874_ = v___x_2846_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2874_);
v___x_2876_ = v___x_2850_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_upperBound_2837_);
v___x_2876_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_unbox(v_a_2870_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_a_2870_);
lean_del_object(v___x_2863_);
lean_dec(v_fst_2861_);
lean_dec(v_val_2844_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v___x_2876_);
lean_ctor_set(v___x_2867_, 0, v___x_2838_);
v___x_2879_ = v___x_2867_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2876_);
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
v_sz_2881_ = lean_array_size(v_fst_2861_);
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2881_, v___x_2882_, v_fst_2861_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2889_; uint8_t v___x_2890_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_nat_dec_eq(v___x_2809_, v___x_2889_);
v___x_2936_ = lean_array_get_size(v_a_2884_);
v___x_2937_ = lean_nat_dec_lt(v___x_2889_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_dec(v_a_2870_);
goto v___jp_2891_;
}
else
{
if (v___x_2937_ == 0)
{
lean_dec(v_a_2870_);
goto v___jp_2891_;
}
else
{
size_t v___x_2938_; uint8_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = lean_usize_of_nat(v___x_2936_);
v___x_2939_ = lean_unbox(v_a_2870_);
lean_dec(v_a_2870_);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2939_, v___x_2809_, v_a_2884_, v___x_2882_, v___x_2938_);
if (v___x_2940_ == 0)
{
goto v___jp_2891_;
}
else
{
if (v___x_2890_ == 0)
{
lean_dec(v_a_2884_);
lean_del_object(v___x_2863_);
lean_dec(v_val_2844_);
goto v___jp_2885_;
}
else
{
goto v___jp_2891_;
}
}
}
}
v___jp_2885_:
{
lean_object* v___x_2887_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v___x_2876_);
lean_ctor_set(v___x_2867_, 0, v___x_2838_);
v___x_2887_ = v___x_2867_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2876_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v_a_2826_ = v___x_2887_;
goto v___jp_2825_;
}
}
v___jp_2891_:
{
if (v___x_2890_ == 0)
{
uint8_t v___x_2892_; 
lean_del_object(v___x_2867_);
v___x_2892_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2884_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2894_; 
lean_dec(v_a_2884_);
lean_dec(v_val_2844_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2876_);
lean_ctor_set(v___x_2863_, 0, v___x_2838_);
v___x_2894_ = v___x_2863_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2876_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v_a_2826_ = v___x_2894_;
goto v___jp_2825_;
}
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2811_, v_a_2884_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2927_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
if (lean_obj_tag(v_a_2897_) == 1)
{
lean_object* v___x_2902_; 
lean_dec_ref_known(v_a_2897_, 1);
lean_del_object(v___x_2899_);
lean_dec(v_a_2884_);
lean_dec(v_val_2844_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2876_);
lean_ctor_set(v___x_2863_, 0, v___x_2838_);
v___x_2902_ = v___x_2863_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2876_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
v_a_2826_ = v___x_2902_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_fnName_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_a_2897_);
lean_dec_ref(v___x_2808_);
v_fnName_2904_ = lean_ctor_get(v_recArgInfo_2812_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_recArgInfo_2812_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; lean_object* v_unused_2926_; 
v_unused_2922_ = lean_ctor_get(v_recArgInfo_2812_, 5);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_recArgInfo_2812_, 4);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_recArgInfo_2812_, 3);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_recArgInfo_2812_, 2);
lean_dec(v_unused_2925_);
v_unused_2926_ = lean_ctor_get(v_recArgInfo_2812_, 1);
lean_dec(v_unused_2926_);
v___x_2906_ = v_recArgInfo_2812_;
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_fnName_2904_);
lean_dec(v_recArgInfo_2812_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
size_t v_sz_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v_sz_2908_ = lean_array_size(v_a_2884_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2810_, v_sz_2908_, v___x_2882_, v_a_2884_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 5, v_val_2844_);
lean_ctor_set(v___x_2906_, 4, v_group_2815_);
lean_ctor_set(v___x_2906_, 3, v___x_2909_);
lean_ctor_set(v___x_2906_, 2, v___x_2814_);
lean_ctor_set(v___x_2906_, 1, v___x_2813_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_fnName_2904_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_group_2815_);
lean_ctor_set(v_reuseFailAlloc_2920_, 5, v_val_2844_);
v___x_2911_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2876_);
lean_ctor_set(v___x_2863_, 0, v___x_2913_);
v___x_2915_ = v___x_2863_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2876_);
v___x_2915_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2917_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2915_);
v___x_2917_ = v___x_2899_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2884_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2863_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2928_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2896_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2896_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
lean_dec(v_a_2884_);
lean_del_object(v___x_2863_);
lean_dec(v_val_2844_);
goto v___jp_2885_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___x_2876_);
lean_dec(v_a_2870_);
lean_del_object(v___x_2867_);
lean_del_object(v___x_2863_);
lean_dec(v_val_2844_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2941_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2883_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2883_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_del_object(v___x_2867_);
lean_del_object(v___x_2863_);
lean_dec(v_fst_2861_);
lean_del_object(v___x_2850_);
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec(v_upperBound_2837_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2951_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2869_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2869_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_a_2855_);
lean_del_object(v___x_2850_);
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec(v_upperBound_2837_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2962_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2858_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2858_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2850_);
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec(v_upperBound_2837_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2970_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2854_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2854_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
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
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_del_object(v___x_2850_);
lean_del_object(v___x_2846_);
lean_dec(v_val_2844_);
lean_dec(v_upperBound_2837_);
lean_dec_ref(v_group_2815_);
lean_dec(v___x_2814_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_recArgInfo_2812_);
lean_dec_ref(v___x_2808_);
v_a_2978_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2852_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2852_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
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
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2808_, v___x_2809_, v_ys_2811_, v___x_2810_, v_recArgInfo_2812_, v___x_2813_, v___x_2814_, v_group_2815_, v_as_2816_, v_sz_2817_, v___x_2828_, v_a_2826_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2992_ = _args[0];
lean_object* v___x_2993_ = _args[1];
lean_object* v___x_2994_ = _args[2];
lean_object* v_ys_2995_ = _args[3];
lean_object* v_recArgInfo_2996_ = _args[4];
lean_object* v___x_2997_ = _args[5];
lean_object* v___x_2998_ = _args[6];
lean_object* v_group_2999_ = _args[7];
lean_object* v_as_3000_ = _args[8];
lean_object* v_sz_3001_ = _args[9];
lean_object* v_i_3002_ = _args[10];
lean_object* v_b_3003_ = _args[11];
lean_object* v___y_3004_ = _args[12];
lean_object* v___y_3005_ = _args[13];
lean_object* v___y_3006_ = _args[14];
lean_object* v___y_3007_ = _args[15];
lean_object* v___y_3008_ = _args[16];
_start:
{
size_t v_sz_boxed_3009_; size_t v_i_boxed_3010_; lean_object* v_res_3011_; 
v_sz_boxed_3009_ = lean_unbox_usize(v_sz_3001_);
lean_dec(v_sz_3001_);
v_i_boxed_3010_ = lean_unbox_usize(v_i_3002_);
lean_dec(v_i_3002_);
v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2992_, v___x_2993_, v___x_2994_, v_ys_2995_, v_recArgInfo_2996_, v___x_2997_, v___x_2998_, v_group_2999_, v_as_3000_, v_sz_boxed_3009_, v_i_boxed_3010_, v_b_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v_as_3000_);
lean_dec_ref(v_ys_2995_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2993_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3012_, lean_object* v_fixedParamPerm_3013_, lean_object* v_xs_3014_, lean_object* v_recArgPos_3015_, lean_object* v_a_3016_, lean_object* v___x_3017_, lean_object* v___x_3018_, lean_object* v_ys_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_toIndGroupInfo_3026_; lean_object* v_all_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3066_; 
v_toIndGroupInfo_3026_ = lean_ctor_get(v_group_3012_, 0);
lean_inc_ref(v_toIndGroupInfo_3026_);
v_all_3027_ = lean_ctor_get(v_toIndGroupInfo_3026_, 0);
lean_inc_ref(v_ys_3019_);
lean_inc_ref(v_fixedParamPerm_3013_);
v___x_3028_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3013_, v_xs_3014_, v_ys_3019_);
v___x_3029_ = l_Lean_instInhabitedExpr;
v___x_3030_ = lean_array_get(v___x_3029_, v___x_3028_, v_recArgPos_3015_);
v___x_3031_ = lean_array_get_size(v_all_3027_);
v___x_3032_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3026_);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_toIndGroupInfo_3026_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; lean_object* v_unused_3068_; 
v_unused_3067_ = lean_ctor_get(v_toIndGroupInfo_3026_, 1);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_toIndGroupInfo_3026_, 0);
lean_dec(v_unused_3068_);
v___x_3034_ = v_toIndGroupInfo_3026_;
v_isShared_3035_ = v_isSharedCheck_3066_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v_toIndGroupInfo_3026_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3066_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3031_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
lean_ctor_set(v___x_3034_, 0, v___x_3036_);
v___x_3038_ = v___x_3034_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3032_);
v___x_3038_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; size_t v_sz_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3038_);
v_sz_3041_ = lean_array_size(v_a_3016_);
v___x_3042_ = ((size_t)0ULL);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3030_, v___x_3017_, v___x_3028_, v_ys_3019_, v___x_3018_, v_fixedParamPerm_3013_, v_recArgPos_3015_, v_group_3012_, v_a_3016_, v_sz_3041_, v___x_3042_, v___x_3040_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec_ref(v_ys_3019_);
lean_dec_ref(v___x_3028_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3056_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3056_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3056_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v_fst_3048_; 
v_fst_3048_ = lean_ctor_get(v_a_3044_, 0);
lean_inc(v_fst_3048_);
lean_dec(v_a_3044_);
if (lean_obj_tag(v_fst_3048_) == 0)
{
lean_object* v___x_3050_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3039_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3039_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_object* v_val_3052_; lean_object* v___x_3054_; 
v_val_3052_ = lean_ctor_get(v_fst_3048_, 0);
lean_inc(v_val_3052_);
lean_dec_ref_known(v_fst_3048_, 1);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_val_3052_);
v___x_3054_ = v___x_3046_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_val_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3043_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3043_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3069_, lean_object* v_fixedParamPerm_3070_, lean_object* v_xs_3071_, lean_object* v_recArgPos_3072_, lean_object* v_a_3073_, lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v_ys_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3069_, v_fixedParamPerm_3070_, v_xs_3071_, v_recArgPos_3072_, v_a_3073_, v___x_3074_, v___x_3075_, v_ys_3076_, v_x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec_ref(v_x_3077_);
lean_dec(v___x_3074_);
lean_dec_ref(v_a_3073_);
lean_dec_ref(v_xs_3071_);
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
lean_object* v___x_3106_; lean_object* v_fixedParamPerm_3107_; lean_object* v_recArgPos_3108_; lean_object* v_indGroupInst_3109_; lean_object* v___x_3110_; 
v___x_3106_ = lean_array_uget_borrowed(v_as_3088_, v_i_3089_);
v_fixedParamPerm_3107_ = lean_ctor_get(v___x_3106_, 1);
v_recArgPos_3108_ = lean_ctor_get(v___x_3106_, 2);
v_indGroupInst_3109_ = lean_ctor_get(v___x_3106_, 4);
lean_inc_ref(v_indGroupInst_3109_);
lean_inc_ref(v_group_3084_);
v___x_3110_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3084_, v_indGroupInst_3109_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
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
v___x_3113_ = lean_array_get_size(v_a_3085_);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_nat_dec_eq(v___x_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___f_3116_; lean_object* v___x_3117_; 
lean_inc(v___x_3106_);
lean_inc_ref(v_a_3085_);
lean_inc(v_recArgPos_3108_);
lean_inc_ref(v_xs_3086_);
lean_inc_ref(v_fixedParamPerm_3107_);
lean_inc_ref(v_group_3084_);
v___f_3116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3116_, 0, v_group_3084_);
lean_closure_set(v___f_3116_, 1, v_fixedParamPerm_3107_);
lean_closure_set(v___f_3116_, 2, v_xs_3086_);
lean_closure_set(v___f_3116_, 3, v_recArgPos_3108_);
lean_closure_set(v___f_3116_, 4, v_a_3085_);
lean_closure_set(v___f_3116_, 5, v___x_3113_);
lean_closure_set(v___f_3116_, 6, v___x_3106_);
lean_inc_ref(v_value_3087_);
v___x_3117_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3087_, v___f_3116_, v___x_3115_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
if (lean_obj_tag(v_a_3118_) == 0)
{
v_a_3098_ = v_b_3091_;
goto v___jp_3097_;
}
else
{
lean_object* v_val_3119_; 
v_val_3119_ = lean_ctor_get(v_a_3118_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_a_3118_, 1);
v_val_3103_ = v_val_3119_;
goto v___jp_3102_;
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
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
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
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
lean_dec_ref(v_value_3087_);
lean_dec_ref(v_xs_3086_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_group_3084_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3091_);
return v___x_3136_;
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
uint8_t v___x_3239_; 
v___x_3239_ = lean_nat_dec_le(v___x_3237_, v___x_3237_);
if (v___x_3239_ == 0)
{
if (v___x_3238_ == 0)
{
lean_dec_ref(v_acc_3228_);
return v___x_3236_;
}
else
{
size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = lean_usize_of_nat(v___x_3237_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3227_, v_acc_3228_, v_xss_3226_, v___x_3234_, v___x_3240_, v___x_3241_, v___x_3236_);
return v___x_3242_;
}
}
else
{
size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = lean_usize_of_nat(v___x_3237_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3227_, v_acc_3228_, v_xss_3226_, v___x_3234_, v___x_3243_, v___x_3244_, v___x_3236_);
return v___x_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3246_, lean_object* v_acc_3247_, lean_object* v_xss_3248_, lean_object* v_as_3249_, size_t v_i_3250_, size_t v_stop_3251_, lean_object* v_b_3252_){
_start:
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_usize_dec_eq(v_i_3250_, v_stop_3251_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; size_t v___x_3260_; size_t v___x_3261_; 
v___x_3254_ = lean_array_uget_borrowed(v_as_3249_, v_i_3250_);
v___x_3255_ = lean_unsigned_to_nat(1u);
v___x_3256_ = lean_nat_add(v_i_3246_, v___x_3255_);
lean_inc(v___x_3254_);
lean_inc_ref(v_acc_3247_);
v___x_3257_ = lean_array_push(v_acc_3247_, v___x_3254_);
v___x_3258_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3248_, v___x_3256_, v___x_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = l_Array_append___redArg(v_b_3252_, v___x_3258_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = ((size_t)1ULL);
v___x_3261_ = lean_usize_add(v_i_3250_, v___x_3260_);
v_i_3250_ = v___x_3261_;
v_b_3252_ = v___x_3259_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3247_);
return v_b_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3263_, lean_object* v_acc_3264_, lean_object* v_xss_3265_, lean_object* v_as_3266_, lean_object* v_i_3267_, lean_object* v_stop_3268_, lean_object* v_b_3269_){
_start:
{
size_t v_i_boxed_3270_; size_t v_stop_boxed_3271_; lean_object* v_res_3272_; 
v_i_boxed_3270_ = lean_unbox_usize(v_i_3267_);
lean_dec(v_i_3267_);
v_stop_boxed_3271_ = lean_unbox_usize(v_stop_3268_);
lean_dec(v_stop_3268_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3263_, v_acc_3264_, v_xss_3265_, v_as_3266_, v_i_boxed_3270_, v_stop_boxed_3271_, v_b_3269_);
lean_dec_ref(v_as_3266_);
lean_dec_ref(v_xss_3265_);
lean_dec(v_i_3263_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3273_, lean_object* v_i_3274_, lean_object* v_acc_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3273_, v_i_3274_, v_acc_3275_);
lean_dec(v_i_3274_);
lean_dec_ref(v_xss_3273_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3277_, lean_object* v_xss_3278_, lean_object* v_i_3279_, lean_object* v_acc_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3278_, v_i_3279_, v_acc_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3282_, lean_object* v_xss_3283_, lean_object* v_i_3284_, lean_object* v_acc_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3282_, v_xss_3283_, v_i_3284_, v_acc_3285_);
lean_dec(v_i_3284_);
lean_dec_ref(v_xss_3283_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3287_, lean_object* v_i_3288_, lean_object* v_acc_3289_, lean_object* v_xss_3290_, lean_object* v_as_3291_, size_t v_i_3292_, size_t v_stop_3293_, lean_object* v_b_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3288_, v_acc_3289_, v_xss_3290_, v_as_3291_, v_i_3292_, v_stop_3293_, v_b_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3296_, lean_object* v_i_3297_, lean_object* v_acc_3298_, lean_object* v_xss_3299_, lean_object* v_as_3300_, lean_object* v_i_3301_, lean_object* v_stop_3302_, lean_object* v_b_3303_){
_start:
{
size_t v_i_boxed_3304_; size_t v_stop_boxed_3305_; lean_object* v_res_3306_; 
v_i_boxed_3304_ = lean_unbox_usize(v_i_3301_);
lean_dec(v_i_3301_);
v_stop_boxed_3305_ = lean_unbox_usize(v_stop_3302_);
lean_dec(v_stop_3302_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3296_, v_i_3297_, v_acc_3298_, v_xss_3299_, v_as_3300_, v_i_boxed_3304_, v_stop_boxed_3305_, v_b_3303_);
lean_dec_ref(v_as_3300_);
lean_dec_ref(v_xss_3299_);
lean_dec(v_i_3297_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3307_, size_t v_i_3308_, size_t v_stop_3309_, lean_object* v_b_3310_){
_start:
{
uint8_t v___x_3311_; 
v___x_3311_ = lean_usize_dec_eq(v_i_3308_, v_stop_3309_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; size_t v___x_3315_; size_t v___x_3316_; 
v___x_3312_ = lean_array_uget_borrowed(v_as_3307_, v_i_3308_);
v___x_3313_ = lean_array_get_size(v___x_3312_);
v___x_3314_ = lean_nat_mul(v_b_3310_, v___x_3313_);
lean_dec(v_b_3310_);
v___x_3315_ = ((size_t)1ULL);
v___x_3316_ = lean_usize_add(v_i_3308_, v___x_3315_);
v_i_3308_ = v___x_3316_;
v_b_3310_ = v___x_3314_;
goto _start;
}
else
{
return v_b_3310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3318_, lean_object* v_i_3319_, lean_object* v_stop_3320_, lean_object* v_b_3321_){
_start:
{
size_t v_i_boxed_3322_; size_t v_stop_boxed_3323_; lean_object* v_res_3324_; 
v_i_boxed_3322_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_stop_boxed_3323_ = lean_unbox_usize(v_stop_3320_);
lean_dec(v_stop_3320_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3318_, v_i_boxed_3322_, v_stop_boxed_3323_, v_b_3321_);
lean_dec_ref(v_as_3318_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___y_3330_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3326_ = lean_unsigned_to_nat(10u);
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3336_ = lean_array_get_size(v_xss_3325_);
v___x_3337_ = lean_nat_dec_lt(v___x_3328_, v___x_3336_);
if (v___x_3337_ == 0)
{
v___y_3330_ = v___x_3327_;
goto v___jp_3329_;
}
else
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_le(v___x_3336_, v___x_3336_);
if (v___x_3338_ == 0)
{
if (v___x_3337_ == 0)
{
v___y_3330_ = v___x_3327_;
goto v___jp_3329_;
}
else
{
size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((size_t)0ULL);
v___x_3340_ = lean_usize_of_nat(v___x_3336_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3325_, v___x_3339_, v___x_3340_, v___x_3327_);
v___y_3330_ = v___x_3341_;
goto v___jp_3329_;
}
}
else
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = lean_usize_of_nat(v___x_3336_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3325_, v___x_3342_, v___x_3343_, v___x_3327_);
v___y_3330_ = v___x_3344_;
goto v___jp_3329_;
}
}
v___jp_3329_:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_lt(v___x_3326_, v___y_3330_);
lean_dec(v___y_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3333_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3325_, v___x_3328_, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_box(0);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3345_);
lean_dec_ref(v_xss_3345_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3347_, lean_object* v_xss_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3350_, lean_object* v_xss_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3350_, v_xss_3351_);
lean_dec_ref(v_xss_3351_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3353_, lean_object* v_as_3354_, size_t v_i_3355_, size_t v_stop_3356_, lean_object* v_b_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3354_, v_i_3355_, v_stop_3356_, v_b_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3359_, lean_object* v_as_3360_, lean_object* v_i_3361_, lean_object* v_stop_3362_, lean_object* v_b_3363_){
_start:
{
size_t v_i_boxed_3364_; size_t v_stop_boxed_3365_; lean_object* v_res_3366_; 
v_i_boxed_3364_ = lean_unbox_usize(v_i_3361_);
lean_dec(v_i_3361_);
v_stop_boxed_3365_ = lean_unbox_usize(v_stop_3362_);
lean_dec(v_stop_3362_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3359_, v_as_3360_, v_i_boxed_3364_, v_stop_boxed_3365_, v_b_3363_);
lean_dec_ref(v_as_3360_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3367_, size_t v_i_3368_, size_t v_stop_3369_, lean_object* v_b_3370_){
_start:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_usize_dec_eq(v_i_3368_, v_stop_3369_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; size_t v___x_3374_; size_t v___x_3375_; 
v___x_3372_ = lean_array_uget_borrowed(v_as_3367_, v_i_3368_);
v___x_3373_ = l_Array_append___redArg(v_b_3370_, v___x_3372_);
v___x_3374_ = ((size_t)1ULL);
v___x_3375_ = lean_usize_add(v_i_3368_, v___x_3374_);
v_i_3368_ = v___x_3375_;
v_b_3370_ = v___x_3373_;
goto _start;
}
else
{
return v_b_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3377_, lean_object* v_i_3378_, lean_object* v_stop_3379_, lean_object* v_b_3380_){
_start:
{
size_t v_i_boxed_3381_; size_t v_stop_boxed_3382_; lean_object* v_res_3383_; 
v_i_boxed_3381_ = lean_unbox_usize(v_i_3378_);
lean_dec(v_i_3378_);
v_stop_boxed_3382_ = lean_unbox_usize(v_stop_3379_);
lean_dec(v_stop_3379_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3377_, v_i_boxed_3381_, v_stop_boxed_3382_, v_b_3380_);
lean_dec_ref(v_as_3377_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
if (lean_obj_tag(v_a_3384_) == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = l_List_reverse___redArg(v_a_3385_);
return v___x_3386_;
}
else
{
lean_object* v_head_3387_; lean_object* v_tail_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3398_; 
v_head_3387_ = lean_ctor_get(v_a_3384_, 0);
v_tail_3388_ = lean_ctor_get(v_a_3384_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_a_3384_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3390_ = v_a_3384_;
v_isShared_3391_ = v_isSharedCheck_3398_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_tail_3388_);
lean_inc(v_head_3387_);
lean_dec(v_a_3384_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3398_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3392_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3387_);
v___x_3393_ = l_Lean_MessageData_ofFormat(v___x_3392_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v_a_3385_);
lean_ctor_set(v___x_3390_, 0, v___x_3393_);
v___x_3395_ = v___x_3390_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3393_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_a_3385_);
v___x_3395_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
v_a_3384_ = v_tail_3388_;
v_a_3385_ = v___x_3395_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3399_, size_t v_i_3400_, lean_object* v_bs_3401_){
_start:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_usize_dec_lt(v_i_3400_, v_sz_3399_);
if (v___x_3402_ == 0)
{
return v_bs_3401_;
}
else
{
lean_object* v_v_3403_; lean_object* v___x_3404_; lean_object* v_bs_x27_3405_; lean_object* v___x_3406_; size_t v___x_3407_; size_t v___x_3408_; lean_object* v___x_3409_; 
v_v_3403_ = lean_array_uget(v_bs_3401_, v_i_3400_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v_bs_x27_3405_ = lean_array_uset(v_bs_3401_, v_i_3400_, v___x_3404_);
v___x_3406_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3403_);
lean_dec(v_v_3403_);
v___x_3407_ = ((size_t)1ULL);
v___x_3408_ = lean_usize_add(v_i_3400_, v___x_3407_);
v___x_3409_ = lean_array_uset(v_bs_x27_3405_, v_i_3400_, v___x_3406_);
v_i_3400_ = v___x_3408_;
v_bs_3401_ = v___x_3409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3411_, lean_object* v_i_3412_, lean_object* v_bs_3413_){
_start:
{
size_t v_sz_boxed_3414_; size_t v_i_boxed_3415_; lean_object* v_res_3416_; 
v_sz_boxed_3414_ = lean_unbox_usize(v_sz_3411_);
lean_dec(v_sz_3411_);
v_i_boxed_3415_ = lean_unbox_usize(v_i_3412_);
lean_dec(v_i_3412_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3414_, v_i_boxed_3415_, v_bs_3413_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3417_, lean_object* v_as_3418_, size_t v_sz_3419_, size_t v_i_3420_, lean_object* v_b_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec_ref(v_xs_3417_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_b_3421_);
return v___x_3428_;
}
else
{
lean_object* v_snd_3429_; lean_object* v_snd_3430_; lean_object* v_snd_3431_; lean_object* v_snd_3432_; lean_object* v_fst_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3577_; 
v_snd_3429_ = lean_ctor_get(v_b_3421_, 1);
lean_inc(v_snd_3429_);
v_snd_3430_ = lean_ctor_get(v_snd_3429_, 1);
lean_inc(v_snd_3430_);
v_snd_3431_ = lean_ctor_get(v_snd_3430_, 1);
lean_inc(v_snd_3431_);
v_snd_3432_ = lean_ctor_get(v_snd_3431_, 1);
lean_inc(v_snd_3432_);
v_fst_3433_ = lean_ctor_get(v_b_3421_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_b_3421_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_b_3421_, 1);
lean_dec(v_unused_3578_);
v___x_3435_ = v_b_3421_;
v_isShared_3436_ = v_isSharedCheck_3577_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_fst_3433_);
lean_dec(v_b_3421_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3577_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_fst_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3575_; 
v_fst_3437_ = lean_ctor_get(v_snd_3429_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v_snd_3429_, 1);
lean_dec(v_unused_3576_);
v___x_3439_ = v_snd_3429_;
v_isShared_3440_ = v_isSharedCheck_3575_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_fst_3437_);
lean_dec(v_snd_3429_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3575_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_fst_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3573_; 
v_fst_3441_ = lean_ctor_get(v_snd_3430_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_snd_3430_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v_snd_3430_, 1);
lean_dec(v_unused_3574_);
v___x_3443_ = v_snd_3430_;
v_isShared_3444_ = v_isSharedCheck_3573_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_fst_3441_);
lean_dec(v_snd_3430_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3573_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_fst_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3571_; 
v_fst_3445_ = lean_ctor_get(v_snd_3431_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_snd_3431_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_snd_3431_, 1);
lean_dec(v_unused_3572_);
v___x_3447_ = v_snd_3431_;
v_isShared_3448_ = v_isSharedCheck_3571_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_fst_3445_);
lean_dec(v_snd_3431_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3571_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_array_3449_; lean_object* v_start_3450_; lean_object* v_stop_3451_; uint8_t v___x_3452_; 
v_array_3449_ = lean_ctor_get(v_snd_3432_, 0);
v_start_3450_ = lean_ctor_get(v_snd_3432_, 1);
v_stop_3451_ = lean_ctor_get(v_snd_3432_, 2);
v___x_3452_ = lean_nat_dec_lt(v_start_3450_, v_stop_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3454_; 
lean_dec_ref(v_xs_3417_);
if (v_isShared_3448_ == 0)
{
v___x_3454_ = v___x_3447_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_fst_3445_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_snd_3432_);
v___x_3454_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3454_);
v___x_3456_ = v___x_3443_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3441_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3456_);
v___x_3458_ = v___x_3439_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3458_);
v___x_3460_ = v___x_3435_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
}
}
}
}
else
{
lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3567_; 
lean_inc(v_stop_3451_);
lean_inc(v_start_3450_);
lean_inc_ref(v_array_3449_);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_snd_3432_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3568_ = lean_ctor_get(v_snd_3432_, 2);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_snd_3432_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_snd_3432_, 0);
lean_dec(v_unused_3570_);
v___x_3467_ = v_snd_3432_;
v_isShared_3468_ = v_isSharedCheck_3567_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v_snd_3432_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3567_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_array_3469_; lean_object* v_start_3470_; lean_object* v_stop_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v_array_3469_ = lean_ctor_get(v_fst_3445_, 0);
v_start_3470_ = lean_ctor_get(v_fst_3445_, 1);
v_stop_3471_ = lean_ctor_get(v_fst_3445_, 2);
v___x_3472_ = lean_array_fget(v_array_3449_, v_start_3450_);
v___x_3473_ = lean_unsigned_to_nat(1u);
v___x_3474_ = lean_nat_add(v_start_3450_, v___x_3473_);
lean_dec(v_start_3450_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3474_);
v___x_3476_ = v___x_3467_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_array_3449_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_stop_3451_);
v___x_3476_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_nat_dec_lt(v_start_3470_, v_stop_3471_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3479_; 
lean_dec(v___x_3472_);
lean_dec_ref(v_xs_3417_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3476_);
v___x_3479_ = v___x_3447_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fst_3445_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3476_);
v___x_3479_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3479_);
v___x_3481_ = v___x_3443_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3441_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3483_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3481_);
v___x_3483_ = v___x_3439_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3485_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3483_);
v___x_3485_ = v___x_3435_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
}
}
}
else
{
lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3562_; 
lean_inc(v_stop_3471_);
lean_inc(v_start_3470_);
lean_inc_ref(v_array_3469_);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_fst_3445_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; 
v_unused_3563_ = lean_ctor_get(v_fst_3445_, 2);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_fst_3445_, 1);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_fst_3445_, 0);
lean_dec(v_unused_3565_);
v___x_3492_ = v_fst_3445_;
v_isShared_3493_ = v_isSharedCheck_3562_;
goto v_resetjp_3491_;
}
else
{
lean_dec(v_fst_3445_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3562_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_array_3494_; lean_object* v_start_3495_; lean_object* v_stop_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v_array_3494_ = lean_ctor_get(v_fst_3441_, 0);
v_start_3495_ = lean_ctor_get(v_fst_3441_, 1);
v_stop_3496_ = lean_ctor_get(v_fst_3441_, 2);
v___x_3497_ = lean_array_fget(v_array_3469_, v_start_3470_);
v___x_3498_ = lean_nat_add(v_start_3470_, v___x_3473_);
lean_dec(v_start_3470_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3498_);
v___x_3500_ = v___x_3492_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_array_3469_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_stop_3471_);
v___x_3500_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
uint8_t v___x_3501_; 
v___x_3501_ = lean_nat_dec_lt(v_start_3495_, v_stop_3496_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v___x_3497_);
lean_dec(v___x_3472_);
lean_dec_ref(v_xs_3417_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3476_);
lean_ctor_set(v___x_3447_, 0, v___x_3500_);
v___x_3503_ = v___x_3447_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___x_3476_);
v___x_3503_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3505_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3503_);
v___x_3505_ = v___x_3443_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_fst_3441_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3505_);
v___x_3507_ = v___x_3439_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3507_);
v___x_3509_ = v___x_3435_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
lean_object* v___x_3510_; 
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
return v___x_3510_;
}
}
}
}
}
else
{
lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3557_; 
lean_inc(v_stop_3496_);
lean_inc(v_start_3495_);
lean_inc_ref(v_array_3494_);
lean_del_object(v___x_3435_);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_fst_3441_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3558_ = lean_ctor_get(v_fst_3441_, 2);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_fst_3441_, 1);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_fst_3441_, 0);
lean_dec(v_unused_3560_);
v___x_3516_ = v_fst_3441_;
v_isShared_3517_ = v_isSharedCheck_3557_;
goto v_resetjp_3515_;
}
else
{
lean_dec(v_fst_3441_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3557_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3518_ = lean_array_uget_borrowed(v_as_3418_, v_i_3420_);
v___x_3519_ = lean_array_fget_borrowed(v_array_3494_, v_start_3495_);
lean_inc(v___x_3519_);
lean_inc_ref(v_xs_3417_);
lean_inc(v_a_3518_);
v___x_3520_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3518_, v___x_3472_, v_xs_3417_, v___x_3519_, v___x_3497_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3548_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
v_snd_3523_ = lean_ctor_get(v_a_3521_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3525_ = v_a_3521_;
v_isShared_3526_ = v_isSharedCheck_3548_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_snd_3523_);
lean_inc(v_fst_3522_);
lean_dec(v_a_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3548_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = lean_nat_add(v_start_3495_, v___x_3473_);
lean_dec(v_start_3495_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3527_);
v___x_3529_ = v___x_3516_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_array_3494_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_stop_3496_);
v___x_3529_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_fst_3433_);
lean_ctor_set(v___x_3530_, 1, v_snd_3523_);
v___x_3531_ = lean_array_push(v_fst_3437_, v_fst_3522_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 1, v___x_3476_);
lean_ctor_set(v___x_3525_, 0, v___x_3500_);
v___x_3533_ = v___x_3525_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3476_);
v___x_3533_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3535_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3533_);
lean_ctor_set(v___x_3447_, 0, v___x_3529_);
v___x_3535_ = v___x_3447_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3537_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3535_);
lean_ctor_set(v___x_3443_, 0, v___x_3531_);
v___x_3537_ = v___x_3443_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3539_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3537_);
lean_ctor_set(v___x_3439_, 0, v___x_3530_);
v___x_3539_ = v___x_3439_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
size_t v___x_3540_; size_t v___x_3541_; 
v___x_3540_ = ((size_t)1ULL);
v___x_3541_ = lean_usize_add(v_i_3420_, v___x_3540_);
v_i_3420_ = v___x_3541_;
v_b_3421_ = v___x_3539_;
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
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_del_object(v___x_3516_);
lean_dec_ref(v___x_3500_);
lean_dec(v_stop_3496_);
lean_dec(v_start_3495_);
lean_dec_ref(v_array_3494_);
lean_dec_ref(v___x_3476_);
lean_del_object(v___x_3447_);
lean_del_object(v___x_3443_);
lean_del_object(v___x_3439_);
lean_dec(v_fst_3437_);
lean_dec(v_fst_3433_);
lean_dec_ref(v_xs_3417_);
v_a_3549_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3520_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3520_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3579_, lean_object* v_as_3580_, lean_object* v_sz_3581_, lean_object* v_i_3582_, lean_object* v_b_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
size_t v_sz_boxed_3589_; size_t v_i_boxed_3590_; lean_object* v_res_3591_; 
v_sz_boxed_3589_ = lean_unbox_usize(v_sz_3581_);
lean_dec(v_sz_3581_);
v_i_boxed_3590_ = lean_unbox_usize(v_i_3582_);
lean_dec(v_i_3582_);
v_res_3591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3579_, v_as_3580_, v_sz_boxed_3589_, v_i_boxed_3590_, v_b_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v_as_3580_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
if (lean_obj_tag(v_a_3592_) == 0)
{
lean_object* v___x_3594_; 
v___x_3594_ = l_List_reverse___redArg(v_a_3593_);
return v___x_3594_;
}
else
{
lean_object* v_head_3595_; lean_object* v_tail_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3605_; 
v_head_3595_ = lean_ctor_get(v_a_3592_, 0);
v_tail_3596_ = lean_ctor_get(v_a_3592_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_a_3592_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3598_ = v_a_3592_;
v_isShared_3599_ = v_isSharedCheck_3605_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_tail_3596_);
lean_inc(v_head_3595_);
lean_dec(v_a_3592_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3605_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3595_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_a_3593_);
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_a_3593_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v_a_3592_ = v_tail_3596_;
v_a_3593_ = v___x_3602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3606_, lean_object* v_j_3607_){
_start:
{
lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = lean_array_get_size(v_as_3606_);
v___x_3609_ = lean_nat_dec_lt(v_j_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v_j_3607_);
v___x_3610_ = lean_box(0);
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3611_ = lean_array_fget_borrowed(v_as_3606_, v_j_3607_);
v___x_3612_ = lean_array_get_size(v___x_3611_);
v___x_3613_ = lean_unsigned_to_nat(0u);
v___x_3614_ = lean_nat_dec_eq(v___x_3612_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_nat_add(v_j_3607_, v___x_3615_);
lean_dec(v_j_3607_);
v_j_3607_ = v___x_3616_;
goto _start;
}
else
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3618_, 0, v_j_3607_);
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3619_, lean_object* v_j_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3619_, v_j_3620_);
lean_dec_ref(v_as_3619_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3622_, lean_object* v_as_3623_, size_t v_sz_3624_, size_t v_i_3625_, lean_object* v_b_3626_){
_start:
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_usize_dec_lt(v_i_3625_, v_sz_3624_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
lean_dec_ref(v_a_3622_);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v_b_3626_);
return v___x_3629_;
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; size_t v___x_3633_; size_t v___x_3634_; 
v_a_3630_ = lean_array_uget_borrowed(v_as_3623_, v_i_3625_);
lean_inc(v_a_3630_);
lean_inc_ref(v_a_3622_);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_a_3622_);
lean_ctor_set(v___x_3631_, 1, v_a_3630_);
v___x_3632_ = lean_array_push(v_b_3626_, v___x_3631_);
v___x_3633_ = ((size_t)1ULL);
v___x_3634_ = lean_usize_add(v_i_3625_, v___x_3633_);
v_i_3625_ = v___x_3634_;
v_b_3626_ = v___x_3632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3636_, lean_object* v_as_3637_, lean_object* v_sz_3638_, lean_object* v_i_3639_, lean_object* v_b_3640_, lean_object* v___y_3641_){
_start:
{
size_t v_sz_boxed_3642_; size_t v_i_boxed_3643_; lean_object* v_res_3644_; 
v_sz_boxed_3642_ = lean_unbox_usize(v_sz_3638_);
lean_dec(v_sz_3638_);
v_i_boxed_3643_ = lean_unbox_usize(v_i_3639_);
lean_dec(v_i_3639_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3636_, v_as_3637_, v_sz_boxed_3642_, v_i_boxed_3643_, v_b_3640_);
lean_dec_ref(v_as_3637_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3645_, lean_object* v_xs_3646_, lean_object* v_as_3647_, size_t v_sz_3648_, size_t v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_usize_dec_lt(v_i_3649_, v_sz_3648_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_dec_ref(v_xs_3646_);
lean_dec_ref(v_a_3645_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_b_3650_);
return v___x_3657_;
}
else
{
lean_object* v_snd_3658_; lean_object* v_fst_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3702_; 
v_snd_3658_ = lean_ctor_get(v_b_3650_, 1);
v_fst_3659_ = lean_ctor_get(v_b_3650_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_b_3650_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3661_ = v_b_3650_;
v_isShared_3662_ = v_isSharedCheck_3702_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_snd_3658_);
lean_inc(v_fst_3659_);
lean_dec(v_b_3650_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3702_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v_array_3663_; lean_object* v_start_3664_; lean_object* v_stop_3665_; uint8_t v___x_3666_; 
v_array_3663_ = lean_ctor_get(v_snd_3658_, 0);
v_start_3664_ = lean_ctor_get(v_snd_3658_, 1);
v_stop_3665_ = lean_ctor_get(v_snd_3658_, 2);
v___x_3666_ = lean_nat_dec_lt(v_start_3664_, v_stop_3665_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3668_; 
lean_dec_ref(v_xs_3646_);
lean_dec_ref(v_a_3645_);
if (v_isShared_3662_ == 0)
{
v___x_3668_ = v___x_3661_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_fst_3659_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_snd_3658_);
v___x_3668_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
}
else
{
lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3698_; 
lean_inc(v_stop_3665_);
lean_inc(v_start_3664_);
lean_inc_ref(v_array_3663_);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_snd_3658_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; lean_object* v_unused_3700_; lean_object* v_unused_3701_; 
v_unused_3699_ = lean_ctor_get(v_snd_3658_, 2);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_snd_3658_, 1);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_snd_3658_, 0);
lean_dec(v_unused_3701_);
v___x_3672_ = v_snd_3658_;
v_isShared_3673_ = v_isSharedCheck_3698_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v_snd_3658_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3698_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_a_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3674_ = lean_array_uget_borrowed(v_as_3647_, v_i_3649_);
v___x_3675_ = lean_array_fget_borrowed(v_array_3663_, v_start_3664_);
lean_inc(v_a_3674_);
lean_inc_ref(v_xs_3646_);
lean_inc_ref(v_a_3645_);
v___x_3676_ = l_Lean_Elab_Structural_argsInGroup(v_a_3645_, v_xs_3646_, v_a_3674_, v___x_3675_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3678_ = lean_unsigned_to_nat(1u);
v___x_3679_ = lean_nat_add(v_start_3664_, v___x_3678_);
lean_dec(v_start_3664_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 1, v___x_3679_);
v___x_3681_ = v___x_3672_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_array_3663_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_stop_3665_);
v___x_3681_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_array_push(v_fst_3659_, v_a_3677_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 1, v___x_3681_);
lean_ctor_set(v___x_3661_, 0, v___x_3682_);
v___x_3684_ = v___x_3661_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3681_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
size_t v___x_3685_; size_t v___x_3686_; 
v___x_3685_ = ((size_t)1ULL);
v___x_3686_ = lean_usize_add(v_i_3649_, v___x_3685_);
v_i_3649_ = v___x_3686_;
v_b_3650_ = v___x_3684_;
goto _start;
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_del_object(v___x_3672_);
lean_dec(v_stop_3665_);
lean_dec(v_start_3664_);
lean_dec_ref(v_array_3663_);
lean_del_object(v___x_3661_);
lean_dec(v_fst_3659_);
lean_dec_ref(v_xs_3646_);
lean_dec_ref(v_a_3645_);
v_a_3690_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3676_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3676_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3703_, lean_object* v_xs_3704_, lean_object* v_as_3705_, lean_object* v_sz_3706_, lean_object* v_i_3707_, lean_object* v_b_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3706_);
lean_dec(v_sz_3706_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3707_);
lean_dec(v_i_3707_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3703_, v_xs_3704_, v_as_3705_, v_sz_boxed_3714_, v_i_boxed_3715_, v_b_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_as_3705_);
return v_res_3716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3724_ = l_Lean_stringToMessageData(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
return v___x_3727_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
return v___x_3730_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3733_ = l_Lean_stringToMessageData(v___x_3732_);
return v___x_3733_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3736_ = l_Lean_stringToMessageData(v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3737_, lean_object* v_values_3738_, lean_object* v_xs_3739_, lean_object* v_fnNames_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_a_3751_; uint8_t v___x_3755_; 
v___x_3755_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec_ref(v_xs_3739_);
lean_dec_ref(v___x_3737_);
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_b_3744_);
return v___x_3756_;
}
else
{
lean_object* v___x_3757_; lean_object* v_recArgInfoss_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; size_t v_sz_3763_; size_t v___x_3764_; lean_object* v___x_3765_; 
v___x_3757_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3759_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
v___x_3760_ = lean_array_get_size(v___x_3737_);
lean_inc_ref(v___x_3737_);
v___x_3761_ = l_Array_toSubarray___redArg(v___x_3737_, v___x_3757_, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v_recArgInfoss_3758_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v_sz_3763_ = lean_array_size(v_values_3738_);
v___x_3764_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3739_);
lean_inc(v_a_3759_);
v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3759_, v_xs_3739_, v_values_3738_, v_sz_3763_, v___x_3764_, v___x_3762_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3826_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3765_, 1);
v_fst_3767_ = lean_ctor_get(v_b_3744_, 0);
v_snd_3768_ = lean_ctor_get(v_b_3744_, 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_b_3744_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3770_ = v_b_3744_;
v_isShared_3771_ = v_isSharedCheck_3826_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_snd_3768_);
lean_inc(v_fst_3767_);
lean_dec(v_b_3744_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3826_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_fst_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3824_; 
v_fst_3772_ = lean_ctor_get(v_a_3766_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; 
v_unused_3825_ = lean_ctor_get(v_a_3766_, 1);
lean_dec(v_unused_3825_);
v___x_3774_ = v_a_3766_;
v_isShared_3775_ = v_isSharedCheck_3824_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_fst_3772_);
lean_dec(v_a_3766_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3824_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3772_, v___x_3757_);
if (lean_obj_tag(v___x_3776_) == 1)
{
lean_object* v_val_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v_fst_3772_);
v_val_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3759_);
v___x_3780_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3759_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 7);
lean_ctor_set(v___x_3770_, 1, v___x_3780_);
lean_ctor_set(v___x_3770_, 0, v___x_3779_);
v___x_3782_ = v___x_3770_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_array_get_borrowed(v___x_3778_, v_fnNames_3740_, v_val_3777_);
lean_dec(v_val_3777_);
lean_inc(v___x_3785_);
v___x_3786_ = l_Lean_MessageData_ofName(v___x_3785_);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3784_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_fst_3767_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_snd_3768_);
lean_ctor_set(v___x_3774_, 0, v___x_3790_);
v___x_3792_ = v___x_3774_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_snd_3768_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
v_a_3751_ = v___x_3792_;
goto v___jp_3750_;
}
}
}
else
{
lean_object* v___x_3795_; 
lean_dec(v___x_3776_);
v___x_3795_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3772_);
lean_dec(v_fst_3772_);
if (lean_obj_tag(v___x_3795_) == 1)
{
lean_object* v_val_3796_; size_t v_sz_3797_; lean_object* v___x_3798_; 
lean_del_object(v___x_3770_);
v_val_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v_sz_3797_ = lean_array_size(v_val_3796_);
lean_inc(v_a_3759_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3759_, v_val_3796_, v_sz_3797_, v___x_3764_, v_snd_3768_);
lean_dec(v_val_3796_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_a_3799_);
lean_ctor_set(v___x_3774_, 0, v_fst_3767_);
v___x_3801_ = v___x_3774_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_fst_3767_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_a_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
v_a_3751_ = v___x_3801_;
goto v___jp_3750_;
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_del_object(v___x_3774_);
lean_dec(v_fst_3767_);
lean_dec_ref(v_xs_3739_);
lean_dec_ref(v___x_3737_);
v_a_3803_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3798_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3798_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
lean_dec(v___x_3795_);
v___x_3811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3759_);
v___x_3812_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3759_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 7);
lean_ctor_set(v___x_3770_, 1, v___x_3812_);
lean_ctor_set(v___x_3770_, 0, v___x_3811_);
v___x_3814_ = v___x_3770_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3815_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v_fst_3767_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_snd_3768_);
lean_ctor_set(v___x_3774_, 0, v___x_3819_);
v___x_3821_ = v___x_3774_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_snd_3768_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
v_a_3751_ = v___x_3821_;
goto v___jp_3750_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v_b_3744_);
lean_dec_ref(v_xs_3739_);
lean_dec_ref(v___x_3737_);
v_a_3827_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3765_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3765_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
v___jp_3750_:
{
size_t v___x_3752_; size_t v___x_3753_; 
v___x_3752_ = ((size_t)1ULL);
v___x_3753_ = lean_usize_add(v_i_3743_, v___x_3752_);
v_i_3743_ = v___x_3753_;
v_b_3744_ = v_a_3751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3835_, lean_object* v_values_3836_, lean_object* v_xs_3837_, lean_object* v_fnNames_3838_, lean_object* v_as_3839_, lean_object* v_sz_3840_, lean_object* v_i_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
size_t v_sz_boxed_3848_; size_t v_i_boxed_3849_; lean_object* v_res_3850_; 
v_sz_boxed_3848_ = lean_unbox_usize(v_sz_3840_);
lean_dec(v_sz_3840_);
v_i_boxed_3849_ = lean_unbox_usize(v_i_3841_);
lean_dec(v_i_3841_);
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3835_, v_values_3836_, v_xs_3837_, v_fnNames_3838_, v_as_3839_, v_sz_boxed_3848_, v_i_boxed_3849_, v_b_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v_as_3839_);
lean_dec_ref(v_fnNames_3838_);
lean_dec_ref(v_values_3836_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3851_, lean_object* v___x_3852_, lean_object* v_values_3853_, lean_object* v_fnNames_3854_, lean_object* v_as_3855_, size_t v_sz_3856_, size_t v_i_3857_, lean_object* v_b_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_a_3865_; uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_lt(v_i_3857_, v_sz_3856_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; 
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_xs_3851_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_b_3858_);
return v___x_3870_;
}
else
{
lean_object* v___x_3871_; lean_object* v_recArgInfoss_3872_; lean_object* v_a_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; size_t v_sz_3877_; size_t v___x_3878_; lean_object* v___x_3879_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3873_ = lean_array_uget_borrowed(v_as_3855_, v_i_3857_);
v___x_3874_ = lean_array_get_size(v___x_3852_);
lean_inc_ref(v___x_3852_);
v___x_3875_ = l_Array_toSubarray___redArg(v___x_3852_, v___x_3871_, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_recArgInfoss_3872_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v_sz_3877_ = lean_array_size(v_values_3853_);
v___x_3878_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3851_);
lean_inc(v_a_3873_);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3873_, v_xs_3851_, v_values_3853_, v_sz_3877_, v___x_3878_, v___x_3876_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_fst_3881_; lean_object* v_snd_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3940_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v_fst_3881_ = lean_ctor_get(v_b_3858_, 0);
v_snd_3882_ = lean_ctor_get(v_b_3858_, 1);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_b_3858_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3884_ = v_b_3858_;
v_isShared_3885_ = v_isSharedCheck_3940_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_snd_3882_);
lean_inc(v_fst_3881_);
lean_dec(v_b_3858_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3940_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_fst_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3938_; 
v_fst_3886_ = lean_ctor_get(v_a_3880_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3880_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v_a_3880_, 1);
lean_dec(v_unused_3939_);
v___x_3888_ = v_a_3880_;
v_isShared_3889_ = v_isSharedCheck_3938_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_fst_3886_);
lean_dec(v_a_3880_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3938_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3886_, v___x_3871_);
if (lean_obj_tag(v___x_3890_) == 1)
{
lean_object* v_val_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_dec(v_fst_3886_);
v_val_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_box(0);
v___x_3893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3873_);
v___x_3894_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3873_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 7);
lean_ctor_set(v___x_3884_, 1, v___x_3894_);
lean_ctor_set(v___x_3884_, 0, v___x_3893_);
v___x_3896_ = v___x_3884_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = lean_array_get_borrowed(v___x_3892_, v_fnNames_3854_, v_val_3891_);
lean_dec(v_val_3891_);
lean_inc(v___x_3899_);
v___x_3900_ = l_Lean_MessageData_ofName(v___x_3899_);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3898_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3901_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v_fst_3881_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 1, v_snd_3882_);
lean_ctor_set(v___x_3888_, 0, v___x_3904_);
v___x_3906_ = v___x_3888_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_snd_3882_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
v_a_3865_ = v___x_3906_;
goto v___jp_3864_;
}
}
}
else
{
lean_object* v___x_3909_; 
lean_dec(v___x_3890_);
v___x_3909_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3886_);
lean_dec(v_fst_3886_);
if (lean_obj_tag(v___x_3909_) == 1)
{
lean_object* v_val_3910_; size_t v_sz_3911_; lean_object* v___x_3912_; 
lean_del_object(v___x_3884_);
v_val_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_val_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v_sz_3911_ = lean_array_size(v_val_3910_);
lean_inc(v_a_3873_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3873_, v_val_3910_, v_sz_3911_, v___x_3878_, v_snd_3882_);
lean_dec(v_val_3910_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 1, v_a_3913_);
lean_ctor_set(v___x_3888_, 0, v_fst_3881_);
v___x_3915_ = v___x_3888_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_fst_3881_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_a_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
v_a_3865_ = v___x_3915_;
goto v___jp_3864_;
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_del_object(v___x_3888_);
lean_dec(v_fst_3881_);
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_xs_3851_);
v_a_3917_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3912_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3912_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_dec(v___x_3909_);
v___x_3925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3873_);
v___x_3926_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3873_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 7);
lean_ctor_set(v___x_3884_, 1, v___x_3926_);
lean_ctor_set(v___x_3884_, 0, v___x_3925_);
v___x_3928_ = v___x_3884_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3929_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v_fst_3881_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3931_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 1, v_snd_3882_);
lean_ctor_set(v___x_3888_, 0, v___x_3933_);
v___x_3935_ = v___x_3888_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_snd_3882_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
v_a_3865_ = v___x_3935_;
goto v___jp_3864_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref(v_b_3858_);
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_xs_3851_);
v_a_3941_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3879_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3879_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
v___jp_3864_:
{
size_t v___x_3866_; size_t v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = ((size_t)1ULL);
v___x_3867_ = lean_usize_add(v_i_3857_, v___x_3866_);
v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3852_, v_values_3853_, v_xs_3851_, v_fnNames_3854_, v_as_3855_, v_sz_3856_, v___x_3867_, v_a_3865_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3949_, lean_object* v___x_3950_, lean_object* v_values_3951_, lean_object* v_fnNames_3952_, lean_object* v_as_3953_, lean_object* v_sz_3954_, lean_object* v_i_3955_, lean_object* v_b_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
size_t v_sz_boxed_3962_; size_t v_i_boxed_3963_; lean_object* v_res_3964_; 
v_sz_boxed_3962_ = lean_unbox_usize(v_sz_3954_);
lean_dec(v_sz_3954_);
v_i_boxed_3963_ = lean_unbox_usize(v_i_3955_);
lean_dec(v_i_3955_);
v_res_3964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3949_, v___x_3950_, v_values_3951_, v_fnNames_3952_, v_as_3953_, v_sz_boxed_3962_, v_i_boxed_3963_, v_b_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec_ref(v_as_3953_);
lean_dec_ref(v_fnNames_3952_);
lean_dec_ref(v_values_3951_);
return v_res_3964_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3969_ = l_Lean_MessageData_ofFormat(v___x_3968_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3972_ = l_Lean_stringToMessageData(v___x_3971_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3977_ = l_Lean_stringToMessageData(v___x_3976_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = lean_box(1);
v___x_3979_ = l_Lean_MessageData_ofFormat(v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3980_, lean_object* v_fixedParamPerms_3981_, lean_object* v_xs_3982_, lean_object* v_values_3983_, lean_object* v_termMeasure_x3fs_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v___x_3990_; lean_object* v_recArgInfoss_3991_; lean_object* v___x_3992_; lean_object* v_perms_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_report_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; size_t v_sz_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_3990_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3992_ = lean_array_get_size(v_values_3983_);
v_perms_3993_ = lean_ctor_get(v_fixedParamPerms_3981_, 1);
lean_inc_ref(v_perms_3993_);
lean_dec_ref(v_fixedParamPerms_3981_);
lean_inc_ref(v_values_3983_);
v___x_3994_ = l_Array_toSubarray___redArg(v_values_3983_, v___x_3990_, v___x_3992_);
v___x_3995_ = lean_array_get_size(v_termMeasure_x3fs_3984_);
v_report_3996_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3997_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3984_, v___x_3990_, v___x_3995_);
v___x_3998_ = lean_array_get_size(v_perms_3993_);
v___x_3999_ = l_Array_toSubarray___redArg(v_perms_3993_, v___x_3990_, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3997_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3994_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v_recArgInfoss_3991_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v_report_3996_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v_sz_4004_ = lean_array_size(v_fnNames_3980_);
v___x_4005_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3982_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3982_, v_fnNames_3980_, v_sz_4004_, v___x_4005_, v___x_4003_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v_snd_4008_; lean_object* v_options_4009_; lean_object* v_fst_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4153_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v_snd_4008_ = lean_ctor_get(v_a_4007_, 1);
lean_inc(v_snd_4008_);
v_options_4009_ = lean_ctor_get(v_a_3987_, 2);
v_fst_4010_ = lean_ctor_get(v_a_4007_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_a_4007_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v_a_4007_, 1);
lean_dec(v_unused_4154_);
v___x_4012_ = v_a_4007_;
v_isShared_4013_ = v_isSharedCheck_4153_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_fst_4010_);
lean_dec(v_a_4007_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4153_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_fst_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4151_; 
v_fst_4014_ = lean_ctor_get(v_snd_4008_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_snd_4008_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v_snd_4008_, 1);
lean_dec(v_unused_4152_);
v___x_4016_ = v_snd_4008_;
v_isShared_4017_ = v_isSharedCheck_4151_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_fst_4014_);
lean_dec(v_snd_4008_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4151_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_inheritedTraceOptions_4018_; uint8_t v_hasTrace_4019_; size_t v_sz_4020_; lean_object* v___x_4021_; lean_object* v___y_4023_; lean_object* v_report_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___x_4071_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; 
v_inheritedTraceOptions_4018_ = lean_ctor_get(v_a_3987_, 13);
v_hasTrace_4019_ = lean_ctor_get_uint8(v_options_4009_, sizeof(void*)*1);
v_sz_4020_ = lean_array_size(v_fst_4014_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4020_, v___x_4005_, v_fst_4014_);
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4019_ == 0)
{
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
v___y_4113_ = v_a_3988_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4122_; uint8_t v___x_4123_; 
v___x_4122_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4123_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4018_, v_options_4009_, v___x_4122_);
if (v___x_4123_ == 0)
{
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
v___y_4113_ = v_a_3988_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4124_; lean_object* v___y_4126_; lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v___x_4124_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4144_ = lean_array_get_size(v___x_4021_);
v___x_4145_ = lean_nat_dec_lt(v___x_3990_, v___x_4144_);
if (v___x_4145_ == 0)
{
v___y_4126_ = v___x_4143_;
goto v___jp_4125_;
}
else
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_nat_dec_le(v___x_4144_, v___x_4144_);
if (v___x_4146_ == 0)
{
if (v___x_4145_ == 0)
{
v___y_4126_ = v___x_4143_;
goto v___jp_4125_;
}
else
{
size_t v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_usize_of_nat(v___x_4144_);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4021_, v___x_4005_, v___x_4147_, v___x_4143_);
v___y_4126_ = v___x_4148_;
goto v___jp_4125_;
}
}
else
{
size_t v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_usize_of_nat(v___x_4144_);
v___x_4150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4021_, v___x_4005_, v___x_4149_, v___x_4143_);
v___y_4126_ = v___x_4150_;
goto v___jp_4125_;
}
}
v___jp_4125_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4127_ = lean_array_to_list(v___y_4126_);
v___x_4128_ = lean_box(0);
v___x_4129_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4127_, v___x_4128_);
v___x_4130_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4131_ = l_Lean_MessageData_joinSep(v___x_4129_, v___x_4130_);
v___x_4132_ = l_Lean_indentD(v___x_4131_);
v___x_4133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4124_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4071_, v___x_4133_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
v___y_4113_ = v_a_3988_;
goto v___jp_4109_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_4016_);
lean_del_object(v___x_4012_);
lean_dec(v_fst_4010_);
lean_dec_ref(v_values_3983_);
lean_dec_ref(v_xs_3982_);
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
v___jp_4022_:
{
lean_object* v___x_4030_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 1, v_recArgInfoss_3991_);
lean_ctor_set(v___x_4016_, 0, v_report_4024_);
v___x_4030_ = v___x_4016_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_report_4024_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_recArgInfoss_3991_);
v___x_4030_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
size_t v_sz_4031_; lean_object* v___x_4032_; 
v_sz_4031_ = lean_array_size(v___y_4023_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3982_, v___x_4021_, v_values_3983_, v_fnNames_3980_, v___y_4023_, v_sz_4031_, v___x_4005_, v___x_4030_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec_ref(v___y_4023_);
lean_dec_ref(v_values_3983_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4049_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4049_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4049_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4048_; 
v_fst_4037_ = lean_ctor_get(v_a_4033_, 0);
v_snd_4038_ = lean_ctor_get(v_a_4033_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_a_4033_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4040_ = v_a_4033_;
v_isShared_4041_ = v_isSharedCheck_4048_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snd_4038_);
lean_inc(v_fst_4037_);
lean_dec(v_a_4033_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4048_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v_fst_4037_);
lean_ctor_set(v___x_4040_, 0, v_snd_4038_);
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_snd_4038_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v_fst_4037_);
v___x_4043_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4045_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4043_);
v___x_4045_ = v___x_4035_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
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
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4032_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4032_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
v___jp_4059_:
{
lean_object* v___x_4065_; uint8_t v___x_4066_; 
v___x_4065_ = lean_array_get_size(v___y_4060_);
v___x_4066_ = lean_nat_dec_eq(v___x_4065_, v___x_3990_);
if (v___x_4066_ == 0)
{
lean_del_object(v___x_4012_);
v___y_4023_ = v___y_4060_;
v_report_4024_ = v_fst_4010_;
v___y_4025_ = v___y_4061_;
v___y_4026_ = v___y_4062_;
v___y_4027_ = v___y_4063_;
v___y_4028_ = v___y_4064_;
goto v___jp_4022_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 7);
lean_ctor_set(v___x_4012_, 1, v___x_4067_);
v___x_4069_ = v___x_4012_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_4010_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
v___y_4023_ = v___y_4060_;
v_report_4024_ = v___x_4069_;
v___y_4025_ = v___y_4061_;
v___y_4026_ = v___y_4062_;
v___y_4027_ = v___y_4063_;
v___y_4028_ = v___y_4064_;
goto v___jp_4022_;
}
}
}
v___jp_4072_:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4077_, v___y_4073_, v___y_4076_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_options_4079_; uint8_t v_hasTrace_4080_; 
v_options_4079_ = lean_ctor_get(v___y_4074_, 2);
v_hasTrace_4080_ = lean_ctor_get_uint8(v_options_4079_, sizeof(void*)*1);
if (v_hasTrace_4080_ == 0)
{
lean_object* v_a_4081_; 
v_a_4081_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4078_, 1);
v___y_4060_ = v_a_4081_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v___y_4074_;
v___y_4064_ = v___y_4075_;
goto v___jp_4059_;
}
else
{
lean_object* v_a_4082_; lean_object* v_inheritedTraceOptions_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v_a_4082_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4078_, 1);
v_inheritedTraceOptions_4083_ = lean_ctor_get(v___y_4074_, 13);
v___x_4084_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4083_, v_options_4079_, v___x_4084_);
if (v___x_4085_ == 0)
{
v___y_4060_ = v_a_4082_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v___y_4074_;
v___y_4064_ = v___y_4075_;
goto v___jp_4059_;
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4086_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4082_);
v___x_4087_ = lean_array_to_list(v_a_4082_);
v___x_4088_ = lean_box(0);
v___x_4089_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4087_, v___x_4088_);
v___x_4090_ = l_Lean_MessageData_ofList(v___x_4089_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4086_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4071_, v___x_4091_, v___y_4073_, v___y_4076_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_dec_ref_known(v___x_4092_, 1);
v___y_4060_ = v_a_4082_;
v___y_4061_ = v___y_4073_;
v___y_4062_ = v___y_4076_;
v___y_4063_ = v___y_4074_;
v___y_4064_ = v___y_4075_;
goto v___jp_4059_;
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_a_4082_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_4016_);
lean_del_object(v___x_4012_);
lean_dec(v_fst_4010_);
lean_dec_ref(v_values_3983_);
lean_dec_ref(v_xs_3982_);
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
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
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_4016_);
lean_del_object(v___x_4012_);
lean_dec(v_fst_4010_);
lean_dec_ref(v_values_3983_);
lean_dec_ref(v_xs_3982_);
v_a_4101_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4078_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4078_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
v___jp_4109_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4115_ = lean_array_get_size(v___x_4021_);
v___x_4116_ = lean_nat_dec_lt(v___x_3990_, v___x_4115_);
if (v___x_4116_ == 0)
{
v___y_4073_ = v___y_4110_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4113_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___x_4114_;
goto v___jp_4072_;
}
else
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_nat_dec_le(v___x_4115_, v___x_4115_);
if (v___x_4117_ == 0)
{
if (v___x_4116_ == 0)
{
v___y_4073_ = v___y_4110_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4113_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___x_4114_;
goto v___jp_4072_;
}
else
{
size_t v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_usize_of_nat(v___x_4115_);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4021_, v___x_4005_, v___x_4118_, v___x_4114_);
v___y_4073_ = v___y_4110_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4113_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___x_4119_;
goto v___jp_4072_;
}
}
else
{
size_t v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = lean_usize_of_nat(v___x_4115_);
v___x_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4021_, v___x_4005_, v___x_4120_, v___x_4114_);
v___y_4073_ = v___y_4110_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4113_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___x_4121_;
goto v___jp_4072_;
}
}
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_values_3983_);
lean_dec_ref(v_xs_3982_);
v_a_4155_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4006_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4006_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4163_, lean_object* v_fixedParamPerms_4164_, lean_object* v_xs_4165_, lean_object* v_values_4166_, lean_object* v_termMeasure_x3fs_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4163_, v_fixedParamPerms_4164_, v_xs_4165_, v_values_4166_, v_termMeasure_x3fs_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec_ref(v_fnNames_4163_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4174_, lean_object* v_as_4175_, size_t v_sz_4176_, size_t v_i_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4174_, v_as_4175_, v_sz_4176_, v_i_4177_, v_b_4178_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4185_, lean_object* v_as_4186_, lean_object* v_sz_4187_, lean_object* v_i_4188_, lean_object* v_b_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
size_t v_sz_boxed_4195_; size_t v_i_boxed_4196_; lean_object* v_res_4197_; 
v_sz_boxed_4195_ = lean_unbox_usize(v_sz_4187_);
lean_dec(v_sz_4187_);
v_i_boxed_4196_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_res_4197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4185_, v_as_4186_, v_sz_boxed_4195_, v_i_boxed_4196_, v_b_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec_ref(v_as_4186_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4198_, uint8_t v_skipRealize_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v___x_4202_; lean_object* v_env_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4202_ = lean_st_ref_get(v___y_4200_);
v_env_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc_ref(v_env_4203_);
lean_dec(v___x_4202_);
v___x_4204_ = l_Lean_Environment_contains(v_env_4203_, v_constName_4198_, v_skipRealize_4199_);
v___x_4205_ = lean_box(v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4207_, lean_object* v_skipRealize_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
uint8_t v_skipRealize_boxed_4211_; lean_object* v_res_4212_; 
v_skipRealize_boxed_4211_ = lean_unbox(v_skipRealize_4208_);
v_res_4212_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4207_, v_skipRealize_boxed_4211_, v___y_4209_);
lean_dec(v___y_4209_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4213_, uint8_t v_skipRealize_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4213_, v_skipRealize_4214_, v___y_4218_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4221_, lean_object* v_skipRealize_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
uint8_t v_skipRealize_boxed_4228_; lean_object* v_res_4229_; 
v_skipRealize_boxed_4228_ = lean_unbox(v_skipRealize_4222_);
v_res_4229_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4221_, v_skipRealize_boxed_4228_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_Meta_saveState___redArg(v___y_4232_, v___y_4234_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
lean_inc(v___y_4234_);
lean_inc_ref(v___y_4233_);
lean_inc(v___y_4232_);
lean_inc_ref(v___y_4231_);
v___x_4238_ = lean_apply_5(v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, lean_box(0));
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_dec(v_a_4237_);
return v___x_4238_;
}
else
{
lean_object* v_a_4239_; uint8_t v___y_4241_; uint8_t v___x_4259_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
v___x_4259_ = l_Lean_Exception_isInterrupt(v_a_4239_);
if (v___x_4259_ == 0)
{
uint8_t v___x_4260_; 
lean_inc(v_a_4239_);
v___x_4260_ = l_Lean_Exception_isRuntime(v_a_4239_);
v___y_4241_ = v___x_4260_;
goto v___jp_4240_;
}
else
{
v___y_4241_ = v___x_4259_;
goto v___jp_4240_;
}
v___jp_4240_:
{
if (v___y_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec_ref_known(v___x_4238_, 1);
v___x_4242_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4237_, v___y_4232_, v___y_4234_);
lean_dec(v_a_4237_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v___x_4242_, 0);
lean_dec(v_unused_4250_);
v___x_4244_ = v___x_4242_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_dec(v___x_4242_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 1);
lean_ctor_set(v___x_4244_, 0, v_a_4239_);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4239_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_a_4239_);
v_a_4251_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4242_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4242_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
lean_dec(v_a_4239_);
lean_dec(v_a_4237_);
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_x_4230_);
v_a_4261_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4236_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4236_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4284_, lean_object* v_x_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4284_, v_x_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
return v_res_4291_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4294_ = l_Lean_stringToMessageData(v___x_4293_);
return v___x_4294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4297_ = l_Lean_stringToMessageData(v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4298_, uint8_t v___x_4299_, lean_object* v_group_4300_, lean_object* v_k_4301_, lean_object* v_comb_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4298_, v___x_4299_, v___y_4306_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; uint8_t v___x_4310_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v___x_4310_ = lean_unbox(v_a_4309_);
lean_dec(v_a_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4312_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4300_);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4313_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
v___x_4316_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4315_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v___x_4317_; 
lean_dec_ref_known(v___x_4316_, 1);
v___x_4317_ = lean_apply_6(v_k_4301_, v_comb_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, lean_box(0));
return v___x_4317_;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_comb_4302_);
lean_dec_ref(v_k_4301_);
v_a_4318_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4316_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4316_);
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
else
{
lean_object* v___x_4326_; 
lean_dec_ref(v_group_4300_);
v___x_4326_ = lean_apply_6(v_k_4301_, v_comb_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, lean_box(0));
return v___x_4326_;
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_comb_4302_);
lean_dec_ref(v_k_4301_);
lean_dec_ref(v_group_4300_);
v_a_4327_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4308_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4308_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4335_, lean_object* v___x_4336_, lean_object* v_group_4337_, lean_object* v_k_4338_, lean_object* v_comb_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
uint8_t v___x_4418__boxed_4345_; lean_object* v_res_4346_; 
v___x_4418__boxed_4345_ = lean_unbox(v___x_4336_);
v_res_4346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4335_, v___x_4418__boxed_4345_, v_group_4337_, v_k_4338_, v_comb_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
return v_res_4346_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
return v___x_4349_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4351_ = l_Lean_stringToMessageData(v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4352_, lean_object* v_fnNames_4353_, lean_object* v_xs_4354_, lean_object* v_values_4355_, lean_object* v_as_4356_, size_t v_sz_4357_, size_t v_i_4358_, lean_object* v_b_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
uint8_t v___x_4365_; 
v___x_4365_ = lean_usize_dec_lt(v_i_4358_, v_sz_4357_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_dec_ref(v_values_4355_);
lean_dec_ref(v_xs_4354_);
lean_dec_ref(v_k_4352_);
v___x_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4366_, 0, v_b_4359_);
return v___x_4366_;
}
else
{
lean_object* v_snd_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4437_; 
v_snd_4367_ = lean_ctor_get(v_b_4359_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_b_4359_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; 
v_unused_4438_ = lean_ctor_get(v_b_4359_, 0);
lean_dec(v_unused_4438_);
v___x_4369_ = v_b_4359_;
v_isShared_4370_ = v_isSharedCheck_4437_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_snd_4367_);
lean_dec(v_b_4359_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4437_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_a_4371_; lean_object* v_group_4372_; lean_object* v_comb_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4436_; 
v_a_4371_ = lean_array_uget(v_as_4356_, v_i_4358_);
v_group_4372_ = lean_ctor_get(v_a_4371_, 0);
v_comb_4373_ = lean_ctor_get(v_a_4371_, 1);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_a_4371_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4375_ = v_a_4371_;
v_isShared_4376_ = v_isSharedCheck_4436_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_comb_4373_);
lean_inc(v_group_4372_);
lean_dec(v_a_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4436_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v_toIndGroupInfo_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; 
v_toIndGroupInfo_4377_ = lean_ctor_get(v_group_4372_, 0);
v___x_4378_ = lean_unsigned_to_nat(0u);
v___x_4379_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4377_, v___x_4378_);
v___x_4380_ = lean_box(v___x_4365_);
lean_inc_ref(v_comb_4373_);
lean_inc_ref(v_k_4352_);
v___f_4381_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4381_, 0, v___x_4379_);
lean_closure_set(v___f_4381_, 1, v___x_4380_);
lean_closure_set(v___f_4381_, 2, v_group_4372_);
lean_closure_set(v___f_4381_, 3, v_k_4352_);
lean_closure_set(v___f_4381_, 4, v_comb_4373_);
v___x_4382_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4381_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4394_; 
lean_del_object(v___x_4375_);
lean_dec_ref(v_comb_4373_);
lean_dec_ref(v_values_4355_);
lean_dec_ref(v_xs_4354_);
lean_dec_ref(v_k_4352_);
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4394_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4394_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v_a_4383_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4387_);
v___x_4389_ = v___x_4369_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_snd_4367_);
v___x_4389_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4391_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4389_);
v___x_4391_ = v___x_4385_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4389_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4435_; 
v_a_4395_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4397_ = v___x_4382_;
v_isShared_4398_ = v_isSharedCheck_4435_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4382_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4435_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; uint8_t v___y_4401_; uint8_t v___x_4433_; 
v___x_4399_ = lean_box(0);
v___x_4433_ = l_Lean_Exception_isInterrupt(v_a_4395_);
if (v___x_4433_ == 0)
{
uint8_t v___x_4434_; 
lean_inc(v_a_4395_);
v___x_4434_ = l_Lean_Exception_isRuntime(v_a_4395_);
v___y_4401_ = v___x_4434_;
goto v___jp_4400_;
}
else
{
v___y_4401_ = v___x_4433_;
goto v___jp_4400_;
}
v___jp_4400_:
{
if (v___y_4401_ == 0)
{
lean_object* v___x_4402_; 
lean_del_object(v___x_4397_);
lean_inc_ref(v_values_4355_);
lean_inc_ref(v_xs_4354_);
v___x_4402_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4353_, v_xs_4354_, v_values_4355_, v_comb_4373_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 7);
lean_ctor_set(v___x_4375_, 1, v_a_4403_);
lean_ctor_set(v___x_4375_, 0, v___x_4404_);
v___x_4406_ = v___x_4375_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_a_4403_);
v___x_4406_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4407_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Lean_Exception_toMessageData(v_a_4395_);
v___x_4410_ = l_Lean_indentD(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4408_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4411_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v_snd_4367_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v___x_4414_);
lean_ctor_set(v___x_4369_, 0, v___x_4399_);
v___x_4416_ = v___x_4369_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4399_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
size_t v___x_4417_; size_t v___x_4418_; 
v___x_4417_ = ((size_t)1ULL);
v___x_4418_ = lean_usize_add(v_i_4358_, v___x_4417_);
v_i_4358_ = v___x_4418_;
v_b_4359_ = v___x_4416_;
goto _start;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_a_4395_);
lean_del_object(v___x_4375_);
lean_del_object(v___x_4369_);
lean_dec(v_snd_4367_);
lean_dec_ref(v_values_4355_);
lean_dec_ref(v_xs_4354_);
lean_dec_ref(v_k_4352_);
v_a_4422_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4402_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4402_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_object* v___x_4431_; 
lean_del_object(v___x_4375_);
lean_dec_ref(v_comb_4373_);
lean_del_object(v___x_4369_);
lean_dec(v_snd_4367_);
lean_dec_ref(v_values_4355_);
lean_dec_ref(v_xs_4354_);
lean_dec_ref(v_k_4352_);
if (v_isShared_4398_ == 0)
{
v___x_4431_ = v___x_4397_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4395_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4439_, lean_object* v_fnNames_4440_, lean_object* v_xs_4441_, lean_object* v_values_4442_, lean_object* v_as_4443_, lean_object* v_sz_4444_, lean_object* v_i_4445_, lean_object* v_b_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
size_t v_sz_boxed_4452_; size_t v_i_boxed_4453_; lean_object* v_res_4454_; 
v_sz_boxed_4452_ = lean_unbox_usize(v_sz_4444_);
lean_dec(v_sz_4444_);
v_i_boxed_4453_ = lean_unbox_usize(v_i_4445_);
lean_dec(v_i_4445_);
v_res_4454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4439_, v_fnNames_4440_, v_xs_4441_, v_values_4442_, v_as_4443_, v_sz_boxed_4452_, v_i_boxed_4453_, v_b_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v_as_4443_);
lean_dec_ref(v_fnNames_4440_);
return v_res_4454_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
return v___x_4457_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4460_ = l_Lean_stringToMessageData(v___x_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4461_, lean_object* v_xs_4462_, lean_object* v_values_4463_, lean_object* v_candidates_4464_, lean_object* v_k_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_candidates_4471_; lean_object* v_report_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4531_; 
v_candidates_4471_ = lean_ctor_get(v_candidates_4464_, 0);
v_report_4472_ = lean_ctor_get(v_candidates_4464_, 1);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_candidates_4464_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4474_ = v_candidates_4464_;
v_isShared_4475_ = v_isSharedCheck_4531_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_report_4472_);
lean_inc(v_candidates_4471_);
lean_dec(v_candidates_4464_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4531_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; lean_object* v___x_4478_; 
v___x_4476_ = lean_box(0);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4476_);
v___x_4478_ = v___x_4474_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4476_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v_report_4472_);
v___x_4478_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
size_t v_sz_4479_; size_t v___x_4480_; lean_object* v___x_4481_; 
v_sz_4479_ = lean_array_size(v_candidates_4471_);
v___x_4480_ = ((size_t)0ULL);
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4465_, v_fnNames_4461_, v_xs_4462_, v_values_4463_, v_candidates_4471_, v_sz_4479_, v___x_4480_, v___x_4478_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec_ref(v_candidates_4471_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4521_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4521_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4521_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_fst_4486_; 
v_fst_4486_ = lean_ctor_get(v_a_4482_, 0);
if (lean_obj_tag(v_fst_4486_) == 0)
{
lean_object* v_options_4487_; lean_object* v_snd_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4515_; 
lean_del_object(v___x_4484_);
v_options_4487_ = lean_ctor_get(v_a_4468_, 2);
v_snd_4488_ = lean_ctor_get(v_a_4482_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_a_4482_, 0);
lean_dec(v_unused_4516_);
v___x_4490_ = v_a_4482_;
v_isShared_4491_ = v_isSharedCheck_4515_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_snd_4488_);
lean_dec(v_a_4482_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4515_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_inheritedTraceOptions_4492_; uint8_t v_hasTrace_4493_; lean_object* v___x_4494_; lean_object* v___x_4496_; 
v_inheritedTraceOptions_4492_ = lean_ctor_get(v_a_4468_, 13);
v_hasTrace_4493_ = lean_ctor_get_uint8(v_options_4487_, sizeof(void*)*1);
v___x_4494_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 7);
lean_ctor_set(v___x_4490_, 0, v___x_4494_);
v___x_4496_ = v___x_4490_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_snd_4488_);
v___x_4496_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
if (v_hasTrace_4493_ == 0)
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4496_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4497_;
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4498_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4499_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4492_, v_options_4487_, v___x_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4496_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4501_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4496_);
v___x_4503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
lean_ctor_set(v___x_4503_, 1, v___x_4496_);
v___x_4504_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4498_, v___x_4503_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v___x_4505_; 
lean_dec_ref_known(v___x_4504_, 1);
v___x_4505_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4496_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4505_;
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v___x_4496_);
v_a_4506_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4504_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4504_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
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
}
}
}
}
else
{
lean_object* v_val_4517_; lean_object* v___x_4519_; 
lean_inc_ref(v_fst_4486_);
lean_dec(v_a_4482_);
v_val_4517_ = lean_ctor_get(v_fst_4486_, 0);
lean_inc(v_val_4517_);
lean_dec_ref_known(v_fst_4486_, 1);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v_val_4517_);
v___x_4519_ = v___x_4484_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_val_4517_);
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
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_a_4522_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4481_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4481_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4532_, lean_object* v_xs_4533_, lean_object* v_values_4534_, lean_object* v_candidates_4535_, lean_object* v_k_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4532_, v_xs_4533_, v_values_4534_, v_candidates_4535_, v_k_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec_ref(v_fnNames_4532_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4543_, lean_object* v_fnNames_4544_, lean_object* v_xs_4545_, lean_object* v_values_4546_, lean_object* v_candidates_4547_, lean_object* v_k_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4544_, v_xs_4545_, v_values_4546_, v_candidates_4547_, v_k_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4555_, lean_object* v_fnNames_4556_, lean_object* v_xs_4557_, lean_object* v_values_4558_, lean_object* v_candidates_4559_, lean_object* v_k_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4555_, v_fnNames_4556_, v_xs_4557_, v_values_4558_, v_candidates_4559_, v_k_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec_ref(v_fnNames_4556_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4567_, lean_object* v_k_4568_, lean_object* v_fnNames_4569_, lean_object* v_xs_4570_, lean_object* v_values_4571_, lean_object* v_as_4572_, size_t v_sz_4573_, size_t v_i_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4568_, v_fnNames_4569_, v_xs_4570_, v_values_4571_, v_as_4572_, v_sz_4573_, v_i_4574_, v_b_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4582_, lean_object* v_k_4583_, lean_object* v_fnNames_4584_, lean_object* v_xs_4585_, lean_object* v_values_4586_, lean_object* v_as_4587_, lean_object* v_sz_4588_, lean_object* v_i_4589_, lean_object* v_b_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
size_t v_sz_boxed_4596_; size_t v_i_boxed_4597_; lean_object* v_res_4598_; 
v_sz_boxed_4596_ = lean_unbox_usize(v_sz_4588_);
lean_dec(v_sz_4588_);
v_i_boxed_4597_ = lean_unbox_usize(v_i_4589_);
lean_dec(v_i_4589_);
v_res_4598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4582_, v_k_4583_, v_fnNames_4584_, v_xs_4585_, v_values_4586_, v_as_4587_, v_sz_boxed_4596_, v_i_boxed_4597_, v_b_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_as_4587_);
lean_dec_ref(v_fnNames_4584_);
return v_res_4598_;
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
