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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not considering parameter "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "getRecArgInfos report: "};
static const lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Structural_nonIndicesFirst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_nonIndicesFirst___closed__2;
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
lean_inc_ref(v_mctx_503_);
lean_dec(v___x_477_);
v___f_504_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_505_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_505_, 0, v_fvarId_474_);
v___x_506_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_503_);
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
v___x_961_ = lean_panic_fn(v___x_960_, v_msg_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_6886__overap_970_; lean_object* v___x_971_; 
v___f_969_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6886__overap_970_ = lean_panic_fn(v___f_969_, v_msg_963_);
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
v_name_1221_ = lean_ctor_get(v___y_1211_, 0);
lean_inc(v_name_1221_);
lean_dec_ref(v___y_1211_);
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
v___x_1229_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1228_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1193_, v_xs_1194_);
v___x_1231_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1230_, v___y_1216_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1230_, v___y_1215_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
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
v_name_1238_ = lean_ctor_get(v___y_1211_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___y_1211_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v___y_1211_, 2);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v___y_1211_, 1);
lean_dec(v_unused_1260_);
v___x_1240_ = v___y_1211_;
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_name_1238_);
lean_dec(v___y_1211_);
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
v___x_1257_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1256_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
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
lean_dec_ref(v___y_1211_);
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
v___x_1281_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1280_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
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
lean_dec_ref(v___y_1211_);
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
v_name_1299_ = lean_ctor_get(v___y_1211_, 0);
lean_inc(v_name_1299_);
lean_dec_ref(v___y_1211_);
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
v___x_1316_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1315_, v___y_1213_, v___y_1219_, v___y_1212_, v___y_1214_);
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
lean_dec_ref(v___y_1211_);
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
v___x_1342_ = l_Array_toSubarray___redArg(v___y_1332_, v_lower_1340_, v_upper_1341_);
v___x_1343_ = l_Subarray_copy___redArg(v___x_1342_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_nat_dec_lt(v___y_1330_, v___x_1344_);
lean_dec(v___y_1330_);
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1333_;
v___y_1211_ = v___y_1329_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1337_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1338_;
v___y_1218_ = v___y_1331_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1333_;
v___y_1211_ = v___y_1329_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1337_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1338_;
v___y_1218_ = v___y_1331_;
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
v___y_1210_ = v___y_1333_;
v___y_1211_ = v___y_1329_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1337_;
v___y_1216_ = v___x_1343_;
v___y_1217_ = v___y_1338_;
v___y_1218_ = v___y_1331_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
lean_object* v_name_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1349_ = lean_ctor_get(v___y_1329_, 0);
lean_inc(v_name_1349_);
lean_dec_ref(v___y_1329_);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1351_ = l_Lean_MessageData_ofName(v_name_1349_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_indentExpr(v___y_1333_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1356_, v___y_1335_, v___y_1339_, v___y_1334_, v___y_1336_);
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
v___y_1329_ = v_toConstantVal_1376_;
v___y_1330_ = v___x_1385_;
v___y_1331_ = v_all_1378_;
v___y_1332_ = v___x_1384_;
v___y_1333_ = v_a_1366_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1360_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___x_1387_;
v___y_1338_ = v_val_1375_;
v___y_1339_ = v___y_1361_;
v_lower_1340_ = v_numParams_1377_;
v_upper_1341_ = v___x_1388_;
goto v___jp_1327_;
}
else
{
v___y_1328_ = v_us_1369_;
v___y_1329_ = v_toConstantVal_1376_;
v___y_1330_ = v___x_1385_;
v___y_1331_ = v_all_1378_;
v___y_1332_ = v___x_1384_;
v___y_1333_ = v_a_1366_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1360_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___x_1387_;
v___y_1338_ = v_val_1375_;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(lean_object* v_cls_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_options_1502_; uint8_t v_hasTrace_1503_; 
v_options_1502_ = lean_ctor_get(v___y_1500_, 2);
v_hasTrace_1503_ = lean_ctor_get_uint8(v_options_1502_, sizeof(void*)*1);
if (v_hasTrace_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_cls_1499_);
v___x_1504_ = lean_box(v_hasTrace_1503_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
else
{
lean_object* v_inheritedTraceOptions_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_inheritedTraceOptions_1506_ = lean_ctor_get(v___y_1500_, 13);
v___x_1507_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__1));
v___x_1508_ = l_Lean_Name_append(v___x_1507_, v_cls_1499_);
v___x_1509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1506_, v_options_1502_, v___x_1508_);
lean_dec(v___x_1508_);
v___x_1510_ = lean_box(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___boxed(lean_object* v_cls_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v_cls_1512_, v___y_1513_);
lean_dec_ref(v___y_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v_cls_1516_, v___y_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1530_, lean_object* v_e_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = l_Lean_indentD(v_e_1531_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1530_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1534_, lean_object* v_fnName_1535_, lean_object* v_fixedParamPerm_1536_, lean_object* v_args_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1534_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1535_, v_fixedParamPerm_1536_, v_args_1537_, v_a_1544_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1545_;
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v_fixedParamPerm_1536_);
lean_dec(v_fnName_1535_);
v_a_1546_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1543_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1543_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1554_, lean_object* v_fnName_1555_, lean_object* v_fixedParamPerm_1556_, lean_object* v_args_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1554_, v_fnName_1555_, v_fixedParamPerm_1556_, v_args_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v_args_1557_);
return v_res_1563_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__0));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__2));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__5));
v___x_1574_ = l_Lean_MessageData_ofFormat(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(lean_object* v_upperBound_1575_, lean_object* v_fnName_1576_, lean_object* v_fixedParamPerm_1577_, lean_object* v_args_1578_, lean_object* v_a_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_fst_1587_; lean_object* v_snd_1588_; uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_lt(v_a_1579_, v_upperBound_1575_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec(v_a_1579_);
lean_dec_ref(v_fixedParamPerm_1577_);
lean_dec(v_fnName_1576_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_b_1580_);
return v___x_1594_;
}
else
{
lean_object* v_fst_1595_; lean_object* v_snd_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1641_; 
v_fst_1595_ = lean_ctor_get(v_b_1580_, 0);
v_snd_1596_ = lean_ctor_get(v_b_1580_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_b_1580_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1598_ = v_b_1580_;
v_isShared_1599_ = v_isSharedCheck_1641_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_snd_1596_);
lean_inc(v_fst_1595_);
lean_dec(v_b_1580_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1641_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; 
lean_inc(v_a_1579_);
lean_inc_ref(v_fixedParamPerm_1577_);
lean_inc(v_fnName_1576_);
v___x_1600_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1576_, v_fixedParamPerm_1577_, v_args_1578_, v_a_1579_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1598_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_array_push(v_fst_1595_, v_a_1601_);
v_fst_1587_ = v___x_1602_;
v_snd_1588_ = v_snd_1596_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1640_; 
v_a_1603_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1605_ = v___x_1600_;
v_isShared_1606_ = v_isSharedCheck_1640_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1600_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1640_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
uint8_t v___y_1608_; uint8_t v___x_1638_; 
v___x_1638_ = l_Lean_Exception_isInterrupt(v_a_1603_);
if (v___x_1638_ == 0)
{
uint8_t v___x_1639_; 
lean_inc(v_a_1603_);
v___x_1639_ = l_Lean_Exception_isRuntime(v_a_1603_);
v___y_1608_ = v___x_1639_;
goto v___jp_1607_;
}
else
{
v___y_1608_ = v___x_1638_;
goto v___jp_1607_;
}
v___jp_1607_:
{
if (v___y_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_del_object(v___x_1605_);
v___x_1609_ = l_Lean_Elab_Structural_prettyParam(v_args_1578_, v_a_1579_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 7);
lean_ctor_set(v___x_1598_, 1, v_a_1610_);
lean_ctor_set(v___x_1598_, 0, v___x_1611_);
v___x_1613_ = v___x_1598_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_a_1610_);
v___x_1613_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
lean_inc(v_fnName_1576_);
v___x_1616_ = l_Lean_MessageData_ofName(v_fnName_1576_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_Exception_toMessageData(v_a_1603_);
v___x_1621_ = l_Lean_indentD(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_snd_1596_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__6);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v_fst_1587_ = v_fst_1595_;
v_snd_1588_ = v___x_1625_;
goto v___jp_1586_;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1603_);
lean_del_object(v___x_1598_);
lean_dec(v_snd_1596_);
lean_dec(v_fst_1595_);
lean_dec(v_a_1579_);
lean_dec_ref(v_fixedParamPerm_1577_);
lean_dec(v_fnName_1576_);
v_a_1627_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1609_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1609_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v___x_1636_; 
lean_del_object(v___x_1598_);
lean_dec(v_snd_1596_);
lean_dec(v_fst_1595_);
lean_dec(v_a_1579_);
lean_dec_ref(v_fixedParamPerm_1577_);
lean_dec(v_fnName_1576_);
if (v_isShared_1606_ == 0)
{
v___x_1636_ = v___x_1605_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1603_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
}
v___jp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_fst_1587_);
lean_ctor_set(v___x_1589_, 1, v_snd_1588_);
v___x_1590_ = lean_unsigned_to_nat(1u);
v___x_1591_ = lean_nat_add(v_a_1579_, v___x_1590_);
lean_dec(v_a_1579_);
v_a_1579_ = v___x_1591_;
v_b_1580_ = v___x_1589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___boxed(lean_object* v_upperBound_1642_, lean_object* v_fnName_1643_, lean_object* v_fixedParamPerm_1644_, lean_object* v_args_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(v_upperBound_1642_, v_fnName_1643_, v_fixedParamPerm_1644_, v_args_1645_, v_a_1646_, v_b_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_args_1645_);
lean_dec(v_upperBound_1642_);
return v_res_1653_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1654_; double v___x_1655_; 
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = lean_float_of_nat(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_cls_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_ref_1664_; lean_object* v___x_1665_; lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1710_; 
v_ref_1664_ = lean_ctor_get(v___y_1661_, 5);
v___x_1665_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1710_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1710_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v_traceState_1671_; lean_object* v_env_1672_; lean_object* v_nextMacroScope_1673_; lean_object* v_ngen_1674_; lean_object* v_auxDeclNGen_1675_; lean_object* v_cache_1676_; lean_object* v_messages_1677_; lean_object* v_infoState_1678_; lean_object* v_snapshotTasks_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1709_; 
v___x_1670_ = lean_st_ref_take(v___y_1662_);
v_traceState_1671_ = lean_ctor_get(v___x_1670_, 4);
v_env_1672_ = lean_ctor_get(v___x_1670_, 0);
v_nextMacroScope_1673_ = lean_ctor_get(v___x_1670_, 1);
v_ngen_1674_ = lean_ctor_get(v___x_1670_, 2);
v_auxDeclNGen_1675_ = lean_ctor_get(v___x_1670_, 3);
v_cache_1676_ = lean_ctor_get(v___x_1670_, 5);
v_messages_1677_ = lean_ctor_get(v___x_1670_, 6);
v_infoState_1678_ = lean_ctor_get(v___x_1670_, 7);
v_snapshotTasks_1679_ = lean_ctor_get(v___x_1670_, 8);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1681_ = v___x_1670_;
v_isShared_1682_ = v_isSharedCheck_1709_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snapshotTasks_1679_);
lean_inc(v_infoState_1678_);
lean_inc(v_messages_1677_);
lean_inc(v_cache_1676_);
lean_inc(v_traceState_1671_);
lean_inc(v_auxDeclNGen_1675_);
lean_inc(v_ngen_1674_);
lean_inc(v_nextMacroScope_1673_);
lean_inc(v_env_1672_);
lean_dec(v___x_1670_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1709_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
uint64_t v_tid_1683_; lean_object* v_traces_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1708_; 
v_tid_1683_ = lean_ctor_get_uint64(v_traceState_1671_, sizeof(void*)*1);
v_traces_1684_ = lean_ctor_get(v_traceState_1671_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_traceState_1671_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1686_ = v_traceState_1671_;
v_isShared_1687_ = v_isSharedCheck_1708_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_traces_1684_);
lean_dec(v_traceState_1671_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1708_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; double v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0);
v___x_1690_ = 0;
v___x_1691_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1));
v___x_1692_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1692_, 0, v_cls_1657_);
lean_ctor_set(v___x_1692_, 1, v___x_1688_);
lean_ctor_set(v___x_1692_, 2, v___x_1691_);
lean_ctor_set_float(v___x_1692_, sizeof(void*)*3, v___x_1689_);
lean_ctor_set_float(v___x_1692_, sizeof(void*)*3 + 8, v___x_1689_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*3 + 16, v___x_1690_);
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1694_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v_a_1666_);
lean_ctor_set(v___x_1694_, 2, v___x_1693_);
lean_inc(v_ref_1664_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_ref_1664_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_PersistentArray_push___redArg(v_traces_1684_, v___x_1695_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1696_);
v___x_1698_ = v___x_1686_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1696_);
lean_ctor_set_uint64(v_reuseFailAlloc_1707_, sizeof(void*)*1, v_tid_1683_);
v___x_1698_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 4, v___x_1698_);
v___x_1700_ = v___x_1681_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_env_1672_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_nextMacroScope_1673_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_ngen_1674_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_auxDeclNGen_1675_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1706_, 5, v_cache_1676_);
lean_ctor_set(v_reuseFailAlloc_1706_, 6, v_messages_1677_);
lean_ctor_set(v_reuseFailAlloc_1706_, 7, v_infoState_1678_);
lean_ctor_set(v_reuseFailAlloc_1706_, 8, v_snapshotTasks_1679_);
v___x_1700_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1701_ = lean_st_ref_set(v___y_1662_, v___x_1700_);
v___x_1702_ = lean_box(0);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1702_);
v___x_1704_ = v___x_1668_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_cls_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_cls_1711_, v_msg_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1718_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___f_1723_; 
v___x_1722_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1723_, 0, v___x_1722_);
return v___f_1723_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1728_; lean_object* v_recArgInfos_1729_; lean_object* v___x_1730_; 
v_report_1728_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1729_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_recArgInfos_1729_);
lean_ctor_set(v___x_1730_, 1, v_report_1728_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1741_, lean_object* v_fixedParamPerm_1742_, lean_object* v_xs_1743_, lean_object* v_fnName_1744_, lean_object* v_ys_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1741_) == 1)
{
lean_object* v_val_1752_; lean_object* v_ref_1753_; lean_object* v_fileName_1754_; lean_object* v_fileMap_1755_; lean_object* v_options_1756_; lean_object* v_currRecDepth_1757_; lean_object* v_maxRecDepth_1758_; lean_object* v_ref_1759_; lean_object* v_currNamespace_1760_; lean_object* v_openDecls_1761_; lean_object* v_initHeartbeats_1762_; lean_object* v_maxHeartbeats_1763_; lean_object* v_quotContext_1764_; lean_object* v_currMacroScope_1765_; uint8_t v_diag_1766_; lean_object* v_cancelTk_x3f_1767_; uint8_t v_suppressElabErrors_1768_; lean_object* v_inheritedTraceOptions_1769_; lean_object* v___f_1770_; lean_object* v_args_1771_; lean_object* v___f_1772_; lean_object* v_ref_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_val_1752_ = lean_ctor_get(v_termMeasure_x3f_1741_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v_termMeasure_x3f_1741_);
v_ref_1753_ = lean_ctor_get(v_val_1752_, 0);
lean_inc(v_ref_1753_);
v_fileName_1754_ = lean_ctor_get(v___y_1749_, 0);
v_fileMap_1755_ = lean_ctor_get(v___y_1749_, 1);
v_options_1756_ = lean_ctor_get(v___y_1749_, 2);
v_currRecDepth_1757_ = lean_ctor_get(v___y_1749_, 3);
v_maxRecDepth_1758_ = lean_ctor_get(v___y_1749_, 4);
v_ref_1759_ = lean_ctor_get(v___y_1749_, 5);
v_currNamespace_1760_ = lean_ctor_get(v___y_1749_, 6);
v_openDecls_1761_ = lean_ctor_get(v___y_1749_, 7);
v_initHeartbeats_1762_ = lean_ctor_get(v___y_1749_, 8);
v_maxHeartbeats_1763_ = lean_ctor_get(v___y_1749_, 9);
v_quotContext_1764_ = lean_ctor_get(v___y_1749_, 10);
v_currMacroScope_1765_ = lean_ctor_get(v___y_1749_, 11);
v_diag_1766_ = lean_ctor_get_uint8(v___y_1749_, sizeof(void*)*14);
v_cancelTk_x3f_1767_ = lean_ctor_get(v___y_1749_, 12);
v_suppressElabErrors_1768_ = lean_ctor_get_uint8(v___y_1749_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1769_ = lean_ctor_get(v___y_1749_, 13);
v___f_1770_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1742_);
v_args_1771_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1742_, v_xs_1743_, v_ys_1745_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1772_, 0, v_val_1752_);
lean_closure_set(v___f_1772_, 1, v_fnName_1744_);
lean_closure_set(v___f_1772_, 2, v_fixedParamPerm_1742_);
lean_closure_set(v___f_1772_, 3, v_args_1771_);
v_ref_1773_ = l_Lean_replaceRef(v_ref_1753_, v_ref_1759_);
lean_dec(v_ref_1753_);
lean_inc_ref(v_inheritedTraceOptions_1769_);
lean_inc(v_cancelTk_x3f_1767_);
lean_inc(v_currMacroScope_1765_);
lean_inc(v_quotContext_1764_);
lean_inc(v_maxHeartbeats_1763_);
lean_inc(v_initHeartbeats_1762_);
lean_inc(v_openDecls_1761_);
lean_inc(v_currNamespace_1760_);
lean_inc(v_maxRecDepth_1758_);
lean_inc(v_currRecDepth_1757_);
lean_inc_ref(v_options_1756_);
lean_inc_ref(v_fileMap_1755_);
lean_inc_ref(v_fileName_1754_);
v___x_1774_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1774_, 0, v_fileName_1754_);
lean_ctor_set(v___x_1774_, 1, v_fileMap_1755_);
lean_ctor_set(v___x_1774_, 2, v_options_1756_);
lean_ctor_set(v___x_1774_, 3, v_currRecDepth_1757_);
lean_ctor_set(v___x_1774_, 4, v_maxRecDepth_1758_);
lean_ctor_set(v___x_1774_, 5, v_ref_1773_);
lean_ctor_set(v___x_1774_, 6, v_currNamespace_1760_);
lean_ctor_set(v___x_1774_, 7, v_openDecls_1761_);
lean_ctor_set(v___x_1774_, 8, v_initHeartbeats_1762_);
lean_ctor_set(v___x_1774_, 9, v_maxHeartbeats_1763_);
lean_ctor_set(v___x_1774_, 10, v_quotContext_1764_);
lean_ctor_set(v___x_1774_, 11, v_currMacroScope_1765_);
lean_ctor_set(v___x_1774_, 12, v_cancelTk_x3f_1767_);
lean_ctor_set(v___x_1774_, 13, v_inheritedTraceOptions_1769_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*14, v_diag_1766_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*14 + 1, v_suppressElabErrors_1768_);
v___x_1775_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1772_, v___f_1770_, v___y_1747_, v___y_1748_, v___x_1774_, v___y_1750_);
lean_dec_ref(v___x_1774_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1788_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1780_);
v___x_1782_ = lean_array_push(v___x_1781_, v_a_1776_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1784_);
v___x_1786_ = v___x_1778_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1775_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1775_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v_args_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_termMeasure_x3f_1741_);
lean_inc_ref(v_fixedParamPerm_1742_);
v_args_1797_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1742_, v_xs_1743_, v_ys_1745_);
v___x_1798_ = lean_array_get_size(v_args_1797_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(v___x_1798_, v_fnName_1744_, v_fixedParamPerm_1742_, v_args_1797_, v___x_1799_, v___x_1800_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v_args_1797_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1834_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1804_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v___x_1803_, v___y_1749_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1834_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1834_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_fst_1809_; lean_object* v_snd_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1833_; 
v_fst_1809_ = lean_ctor_get(v_a_1802_, 0);
v_snd_1810_ = lean_ctor_get(v_a_1802_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1812_ = v_a_1802_;
v_isShared_1813_ = v_isSharedCheck_1833_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_snd_1810_);
lean_inc(v_fst_1809_);
lean_dec(v_a_1802_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1833_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_unbox(v_a_1805_);
lean_dec(v_a_1805_);
if (v___x_1821_ == 0)
{
goto v___jp_1814_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11);
lean_inc(v_snd_1810_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_snd_1810_);
v___x_1824_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v___x_1803_, v___x_1823_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_dec_ref(v___x_1824_);
goto v___jp_1814_;
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_del_object(v___x_1812_);
lean_dec(v_snd_1810_);
lean_dec(v_fst_1809_);
lean_del_object(v___x_1807_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
v___jp_1814_:
{
lean_object* v___x_1816_; 
if (v_isShared_1813_ == 0)
{
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_fst_1809_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1810_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1816_);
v___x_1818_ = v___x_1807_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
else
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1835_, lean_object* v_fixedParamPerm_1836_, lean_object* v_xs_1837_, lean_object* v_fnName_1838_, lean_object* v_ys_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1835_, v_fixedParamPerm_1836_, v_xs_1837_, v_fnName_1838_, v_ys_1839_, v_x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_x_1840_);
lean_dec_ref(v_xs_1837_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1847_, lean_object* v_fixedParamPerm_1848_, lean_object* v_xs_1849_, lean_object* v_value_1850_, lean_object* v_termMeasure_x3f_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___f_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1857_, 0, v_termMeasure_x3f_1851_);
lean_closure_set(v___f_1857_, 1, v_fixedParamPerm_1848_);
lean_closure_set(v___f_1857_, 2, v_xs_1849_);
lean_closure_set(v___f_1857_, 3, v_fnName_1847_);
v___x_1858_ = 0;
v___x_1859_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1850_, v___f_1857_, v___x_1858_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1860_, lean_object* v_fixedParamPerm_1861_, lean_object* v_xs_1862_, lean_object* v_value_1863_, lean_object* v_termMeasure_x3f_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1860_, v_fixedParamPerm_1861_, v_xs_1862_, v_value_1863_, v_termMeasure_x3f_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2(lean_object* v_upperBound_1871_, lean_object* v_fnName_1872_, lean_object* v_fixedParamPerm_1873_, lean_object* v_args_1874_, lean_object* v_inst_1875_, lean_object* v_R_1876_, lean_object* v_a_1877_, lean_object* v_b_1878_, lean_object* v_c_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(v_upperBound_1871_, v_fnName_1872_, v_fixedParamPerm_1873_, v_args_1874_, v_a_1877_, v_b_1878_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___boxed(lean_object* v_upperBound_1886_, lean_object* v_fnName_1887_, lean_object* v_fixedParamPerm_1888_, lean_object* v_args_1889_, lean_object* v_inst_1890_, lean_object* v_R_1891_, lean_object* v_a_1892_, lean_object* v_b_1893_, lean_object* v_c_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2(v_upperBound_1886_, v_fnName_1887_, v_fixedParamPerm_1888_, v_args_1889_, v_inst_1890_, v_R_1891_, v_a_1892_, v_b_1893_, v_c_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v_args_1889_);
lean_dec(v_upperBound_1886_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
return v_x_1901_;
}
else
{
lean_object* v_key_1903_; lean_object* v_value_1904_; lean_object* v_tail_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1928_; 
v_key_1903_ = lean_ctor_get(v_x_1902_, 0);
v_value_1904_ = lean_ctor_get(v_x_1902_, 1);
v_tail_1905_ = lean_ctor_get(v_x_1902_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1907_ = v_x_1902_;
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_tail_1905_);
lean_inc(v_value_1904_);
lean_inc(v_key_1903_);
lean_dec(v_x_1902_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; uint64_t v___x_1910_; uint64_t v___x_1911_; uint64_t v___x_1912_; uint64_t v_fold_1913_; uint64_t v___x_1914_; uint64_t v___x_1915_; uint64_t v___x_1916_; size_t v___x_1917_; size_t v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1909_ = lean_array_get_size(v_x_1901_);
v___x_1910_ = lean_uint64_of_nat(v_key_1903_);
v___x_1911_ = 32ULL;
v___x_1912_ = lean_uint64_shift_right(v___x_1910_, v___x_1911_);
v_fold_1913_ = lean_uint64_xor(v___x_1910_, v___x_1912_);
v___x_1914_ = 16ULL;
v___x_1915_ = lean_uint64_shift_right(v_fold_1913_, v___x_1914_);
v___x_1916_ = lean_uint64_xor(v_fold_1913_, v___x_1915_);
v___x_1917_ = lean_uint64_to_usize(v___x_1916_);
v___x_1918_ = lean_usize_of_nat(v___x_1909_);
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_sub(v___x_1918_, v___x_1919_);
v___x_1921_ = lean_usize_land(v___x_1917_, v___x_1920_);
v___x_1922_ = lean_array_uget_borrowed(v_x_1901_, v___x_1921_);
lean_inc(v___x_1922_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 2, v___x_1922_);
v___x_1924_ = v___x_1907_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_key_1903_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_value_1904_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_array_uset(v_x_1901_, v___x_1921_, v___x_1924_);
v_x_1901_ = v___x_1925_;
v_x_1902_ = v_tail_1905_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1929_, lean_object* v_source_1930_, lean_object* v_target_1931_){
_start:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_array_get_size(v_source_1930_);
v___x_1933_ = lean_nat_dec_lt(v_i_1929_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec_ref(v_source_1930_);
lean_dec(v_i_1929_);
return v_target_1931_;
}
else
{
lean_object* v_es_1934_; lean_object* v___x_1935_; lean_object* v_source_1936_; lean_object* v_target_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_es_1934_ = lean_array_fget(v_source_1930_, v_i_1929_);
v___x_1935_ = lean_box(0);
v_source_1936_ = lean_array_fset(v_source_1930_, v_i_1929_, v___x_1935_);
v_target_1937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1931_, v_es_1934_);
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_add(v_i_1929_, v___x_1938_);
lean_dec(v_i_1929_);
v_i_1929_ = v___x_1939_;
v_source_1930_ = v_source_1936_;
v_target_1931_ = v_target_1937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_nbuckets_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1942_ = lean_array_get_size(v_data_1941_);
v___x_1943_ = lean_unsigned_to_nat(2u);
v_nbuckets_1944_ = lean_nat_mul(v___x_1942_, v___x_1943_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_mk_array(v_nbuckets_1944_, v___x_1946_);
v___x_1948_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1945_, v_data_1941_, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1950_) == 0)
{
uint8_t v___x_1951_; 
v___x_1951_ = 0;
return v___x_1951_;
}
else
{
lean_object* v_key_1952_; lean_object* v_tail_1953_; uint8_t v___x_1954_; 
v_key_1952_ = lean_ctor_get(v_x_1950_, 0);
v_tail_1953_ = lean_ctor_get(v_x_1950_, 2);
v___x_1954_ = lean_nat_dec_eq(v_key_1952_, v_a_1949_);
if (v___x_1954_ == 0)
{
v_x_1950_ = v_tail_1953_;
goto _start;
}
else
{
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1956_, lean_object* v_x_1957_){
_start:
{
uint8_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1956_, v_x_1957_);
lean_dec(v_x_1957_);
lean_dec(v_a_1956_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1960_, lean_object* v_a_1961_, lean_object* v_b_1962_){
_start:
{
lean_object* v_size_1963_; lean_object* v_buckets_1964_; lean_object* v___x_1965_; uint64_t v___x_1966_; uint64_t v___x_1967_; uint64_t v___x_1968_; uint64_t v_fold_1969_; uint64_t v___x_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; lean_object* v_bkt_1978_; uint8_t v___x_1979_; 
v_size_1963_ = lean_ctor_get(v_m_1960_, 0);
v_buckets_1964_ = lean_ctor_get(v_m_1960_, 1);
v___x_1965_ = lean_array_get_size(v_buckets_1964_);
v___x_1966_ = lean_uint64_of_nat(v_a_1961_);
v___x_1967_ = 32ULL;
v___x_1968_ = lean_uint64_shift_right(v___x_1966_, v___x_1967_);
v_fold_1969_ = lean_uint64_xor(v___x_1966_, v___x_1968_);
v___x_1970_ = 16ULL;
v___x_1971_ = lean_uint64_shift_right(v_fold_1969_, v___x_1970_);
v___x_1972_ = lean_uint64_xor(v_fold_1969_, v___x_1971_);
v___x_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = lean_usize_of_nat(v___x_1965_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_sub(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_usize_land(v___x_1973_, v___x_1976_);
v_bkt_1978_ = lean_array_uget_borrowed(v_buckets_1964_, v___x_1977_);
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1961_, v_bkt_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2000_; 
lean_inc_ref(v_buckets_1964_);
lean_inc(v_size_1963_);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_m_1960_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; lean_object* v_unused_2002_; 
v_unused_2001_ = lean_ctor_get(v_m_1960_, 1);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_m_1960_, 0);
lean_dec(v_unused_2002_);
v___x_1981_ = v_m_1960_;
v_isShared_1982_ = v_isSharedCheck_2000_;
goto v_resetjp_1980_;
}
else
{
lean_dec(v_m_1960_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2000_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v_size_x27_1984_; lean_object* v___x_1985_; lean_object* v_buckets_x27_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1983_ = lean_unsigned_to_nat(1u);
v_size_x27_1984_ = lean_nat_add(v_size_1963_, v___x_1983_);
lean_dec(v_size_1963_);
lean_inc(v_bkt_1978_);
v___x_1985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1985_, 0, v_a_1961_);
lean_ctor_set(v___x_1985_, 1, v_b_1962_);
lean_ctor_set(v___x_1985_, 2, v_bkt_1978_);
v_buckets_x27_1986_ = lean_array_uset(v_buckets_1964_, v___x_1977_, v___x_1985_);
v___x_1987_ = lean_unsigned_to_nat(4u);
v___x_1988_ = lean_nat_mul(v_size_x27_1984_, v___x_1987_);
v___x_1989_ = lean_unsigned_to_nat(3u);
v___x_1990_ = lean_nat_div(v___x_1988_, v___x_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_array_get_size(v_buckets_x27_1986_);
v___x_1992_ = lean_nat_dec_le(v___x_1990_, v___x_1991_);
lean_dec(v___x_1990_);
if (v___x_1992_ == 0)
{
lean_object* v_val_1993_; lean_object* v___x_1995_; 
v_val_1993_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1986_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v_val_1993_);
lean_ctor_set(v___x_1981_, 0, v_size_x27_1984_);
v___x_1995_ = v___x_1981_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_size_x27_1984_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_val_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
else
{
lean_object* v___x_1998_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v_buckets_x27_1986_);
lean_ctor_set(v___x_1981_, 0, v_size_x27_1984_);
v___x_1998_ = v___x_1981_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_size_x27_1984_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_buckets_x27_1986_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_dec(v_b_1962_);
lean_dec(v_a_1961_);
return v_m_1960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_2003_, size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_b_2006_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2007_ == 0)
{
return v_b_2006_;
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; 
v_a_2008_ = lean_array_uget_borrowed(v_as_2003_, v_i_2005_);
v___x_2009_ = lean_box(0);
lean_inc(v_a_2008_);
v___x_2010_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_2006_, v_a_2008_, v___x_2009_);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2005_, v___x_2011_);
v_i_2005_ = v___x_2012_;
v_b_2006_ = v___x_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_2014_, lean_object* v_sz_2015_, lean_object* v_i_2016_, lean_object* v_b_2017_){
_start:
{
size_t v_sz_boxed_2018_; size_t v_i_boxed_2019_; lean_object* v_res_2020_; 
v_sz_boxed_2018_ = lean_unbox_usize(v_sz_2015_);
lean_dec(v_sz_2015_);
v_i_boxed_2019_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_2014_, v_sz_boxed_2018_, v_i_boxed_2019_, v_b_2017_);
lean_dec_ref(v_as_2014_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2021_, size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_b_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2025_ == 0)
{
return v_b_2024_;
}
else
{
lean_object* v_a_2026_; lean_object* v_indicesPos_2027_; size_t v_sz_2028_; size_t v___x_2029_; lean_object* v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_2021_, v_i_2023_);
v_indicesPos_2027_ = lean_ctor_get(v_a_2026_, 3);
v_sz_2028_ = lean_array_size(v_indicesPos_2027_);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2027_, v_sz_2028_, v___x_2029_, v_b_2024_);
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2023_, v___x_2031_);
v_i_2023_ = v___x_2032_;
v_b_2024_ = v___x_2030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2034_, lean_object* v_sz_2035_, lean_object* v_i_2036_, lean_object* v_b_2037_){
_start:
{
size_t v_sz_boxed_2038_; size_t v_i_boxed_2039_; lean_object* v_res_2040_; 
v_sz_boxed_2038_ = lean_unbox_usize(v_sz_2035_);
lean_dec(v_sz_2035_);
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2034_, v_sz_boxed_2038_, v_i_boxed_2039_, v_b_2037_);
lean_dec_ref(v_as_2034_);
return v_res_2040_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_buckets_2043_; lean_object* v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; uint64_t v___x_2047_; uint64_t v_fold_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_buckets_2043_ = lean_ctor_get(v_m_2041_, 1);
v___x_2044_ = lean_array_get_size(v_buckets_2043_);
v___x_2045_ = lean_uint64_of_nat(v_a_2042_);
v___x_2046_ = 32ULL;
v___x_2047_ = lean_uint64_shift_right(v___x_2045_, v___x_2046_);
v_fold_2048_ = lean_uint64_xor(v___x_2045_, v___x_2047_);
v___x_2049_ = 16ULL;
v___x_2050_ = lean_uint64_shift_right(v_fold_2048_, v___x_2049_);
v___x_2051_ = lean_uint64_xor(v_fold_2048_, v___x_2050_);
v___x_2052_ = lean_uint64_to_usize(v___x_2051_);
v___x_2053_ = lean_usize_of_nat(v___x_2044_);
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_sub(v___x_2053_, v___x_2054_);
v___x_2056_ = lean_usize_land(v___x_2052_, v___x_2055_);
v___x_2057_ = lean_array_uget_borrowed(v_buckets_2043_, v___x_2056_);
v___x_2058_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2042_, v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2059_, lean_object* v_a_2060_){
_start:
{
uint8_t v_res_2061_; lean_object* v_r_2062_; 
v_res_2061_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_m_2059_);
v_r_2062_ = lean_box(v_res_2061_);
return v_r_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2063_, lean_object* v_as_2064_, size_t v_sz_2065_, size_t v_i_2066_, lean_object* v_b_2067_){
_start:
{
lean_object* v_a_2069_; uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_lt(v_i_2066_, v_sz_2065_);
if (v___x_2073_ == 0)
{
return v_b_2067_;
}
else
{
lean_object* v_fst_2074_; lean_object* v_snd_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2090_; 
v_fst_2074_ = lean_ctor_get(v_b_2067_, 0);
v_snd_2075_ = lean_ctor_get(v_b_2067_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_b_2067_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2077_ = v_b_2067_;
v_isShared_2078_ = v_isSharedCheck_2090_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snd_2075_);
lean_inc(v_fst_2074_);
lean_dec(v_b_2067_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2090_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_a_2079_; lean_object* v_recArgPos_2080_; uint8_t v___x_2081_; 
v_a_2079_ = lean_array_uget_borrowed(v_as_2064_, v_i_2066_);
v_recArgPos_2080_ = lean_ctor_get(v_a_2079_, 2);
v___x_2081_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2063_, v_recArgPos_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
lean_inc(v_a_2079_);
v___x_2082_ = lean_array_push(v_snd_2075_, v_a_2079_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v___x_2082_);
v___x_2084_ = v___x_2077_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fst_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_a_2069_ = v___x_2084_;
goto v___jp_2068_;
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_inc(v_a_2079_);
v___x_2086_ = lean_array_push(v_fst_2074_, v_a_2079_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2086_);
v___x_2088_ = v___x_2077_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_snd_2075_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v_a_2069_ = v___x_2088_;
goto v___jp_2068_;
}
}
}
}
v___jp_2068_:
{
size_t v___x_2070_; size_t v___x_2071_; 
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2066_, v___x_2070_);
v_i_2066_ = v___x_2071_;
v_b_2067_ = v_a_2069_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2091_, lean_object* v_as_2092_, lean_object* v_sz_2093_, lean_object* v_i_2094_, lean_object* v_b_2095_){
_start:
{
size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2093_);
lean_dec(v_sz_2093_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2091_, v_as_2092_, v_sz_boxed_2096_, v_i_boxed_2097_, v_b_2095_);
lean_dec_ref(v_as_2092_);
lean_dec_ref(v___x_2091_);
return v_res_2098_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_unsigned_to_nat(16u);
v___x_2101_ = lean_mk_array(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_indicesPos_2104_; 
v___x_2102_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2103_ = lean_unsigned_to_nat(0u);
v_indicesPos_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2104_, 0, v___x_2103_);
lean_ctor_set(v_indicesPos_2104_, 1, v___x_2102_);
return v_indicesPos_2104_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__2(void){
_start:
{
lean_object* v_bs_2105_; lean_object* v___x_2106_; 
v_bs_2105_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_bs_2105_);
lean_ctor_set(v___x_2106_, 1, v_bs_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2107_){
_start:
{
lean_object* v_indicesPos_2108_; size_t v_sz_2109_; size_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; 
v_indicesPos_2108_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2109_ = lean_array_size(v_recArgInfos_2107_);
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2107_, v_sz_2109_, v___x_2110_, v_indicesPos_2108_);
v___x_2112_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__2, &l_Lean_Elab_Structural_nonIndicesFirst___closed__2_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__2);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2111_, v_recArgInfos_2107_, v_sz_2109_, v___x_2110_, v___x_2112_);
lean_dec_ref(v___x_2111_);
v_fst_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_fst_2114_);
v_snd_2115_ = lean_ctor_get(v___x_2113_, 1);
lean_inc(v_snd_2115_);
lean_dec_ref(v___x_2113_);
v___x_2116_ = l_Array_append___redArg(v_snd_2115_, v_fst_2114_);
lean_dec(v_fst_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2117_);
lean_dec_ref(v_recArgInfos_2117_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2119_, lean_object* v_m_2120_, lean_object* v_a_2121_, lean_object* v_b_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2120_, v_a_2121_, v_b_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2124_, lean_object* v_m_2125_, lean_object* v_a_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2125_, v_a_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2128_, lean_object* v_m_2129_, lean_object* v_a_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2128_, v_m_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_m_2129_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2133_, lean_object* v_a_2134_, lean_object* v_x_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2134_, v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2137_, lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_res_2140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2137_, v_a_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec(v_a_2138_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2142_, lean_object* v_data_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2145_, lean_object* v_i_2146_, lean_object* v_source_2147_, lean_object* v_target_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2146_, v_source_2147_, v_target_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2154_, lean_object* v_a_2155_, lean_object* v_toPure_2156_, uint8_t v_____do__lift_2157_){
_start:
{
if (v_____do__lift_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_array_push(v___y_2154_, v_a_2155_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
v___x_2160_ = lean_apply_2(v_toPure_2156_, lean_box(0), v___x_2159_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec(v_a_2155_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___y_2154_);
v___x_2162_ = lean_apply_2(v_toPure_2156_, lean_box(0), v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2163_, lean_object* v_a_2164_, lean_object* v_toPure_2165_, lean_object* v_____do__lift_2166_){
_start:
{
uint8_t v_____do__lift_192__boxed_2167_; lean_object* v_res_2168_; 
v_____do__lift_192__boxed_2167_ = lean_unbox(v_____do__lift_2166_);
v_res_2168_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2163_, v_a_2164_, v_toPure_2165_, v_____do__lift_192__boxed_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2169_, lean_object* v_a_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_apply_2(v_eq_2169_, v_x_2171_, v_a_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2173_, lean_object* v___x_2174_, lean_object* v_toBind_2175_, lean_object* v_eq_2176_, lean_object* v_inst_2177_, lean_object* v_a_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___f_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
lean_inc(v_toPure_2173_);
lean_inc(v_a_2178_);
lean_inc_ref(v___y_2180_);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2181_, 0, v___y_2180_);
lean_closure_set(v___f_2181_, 1, v_a_2178_);
lean_closure_set(v___f_2181_, 2, v_toPure_2173_);
v___x_2182_ = lean_array_get_size(v___y_2180_);
v___x_2183_ = lean_nat_dec_lt(v___x_2174_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec_ref(v___y_2180_);
lean_dec(v_a_2178_);
lean_dec_ref(v_inst_2177_);
lean_dec(v_eq_2176_);
v___x_2184_ = lean_box(v___x_2183_);
v___x_2185_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2184_);
v___x_2186_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2185_, v___f_2181_);
return v___x_2186_;
}
else
{
if (v___x_2183_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec_ref(v___y_2180_);
lean_dec(v_a_2178_);
lean_dec_ref(v_inst_2177_);
lean_dec(v_eq_2176_);
v___x_2187_ = lean_box(v___x_2183_);
v___x_2188_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2187_);
v___x_2189_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2188_, v___f_2181_);
return v___x_2189_;
}
else
{
lean_object* v___f_2190_; size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec(v_toPure_2173_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2190_, 0, v_eq_2176_);
lean_closure_set(v___f_2190_, 1, v_a_2178_);
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = lean_usize_of_nat(v___x_2182_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2177_, v___f_2190_, v___y_2180_, v___x_2191_, v___x_2192_);
v___x_2194_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2193_, v___f_2181_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2195_, lean_object* v___x_2196_, lean_object* v_toBind_2197_, lean_object* v_eq_2198_, lean_object* v_inst_2199_, lean_object* v_a_2200_, lean_object* v_x_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2195_, v___x_2196_, v_toBind_2197_, v_eq_2198_, v_inst_2199_, v_a_2200_, v_x_2201_, v___y_2202_);
lean_dec(v___x_2196_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2204_, lean_object* v_____s_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_apply_2(v_toPure_2204_, lean_box(0), v_____s_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2209_, lean_object* v_eq_2210_, lean_object* v_xs_2211_){
_start:
{
lean_object* v_toApplicative_2212_; lean_object* v_toBind_2213_; lean_object* v_toPure_2214_; lean_object* v___x_2215_; lean_object* v_ret_2216_; lean_object* v___f_2217_; lean_object* v___f_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_toApplicative_2212_ = lean_ctor_get(v_inst_2209_, 0);
v_toBind_2213_ = lean_ctor_get(v_inst_2209_, 1);
lean_inc(v_toBind_2213_);
v_toPure_2214_ = lean_ctor_get(v_toApplicative_2212_, 1);
v___x_2215_ = lean_unsigned_to_nat(0u);
v_ret_2216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2209_);
lean_inc(v_toBind_2213_);
lean_inc(v_toPure_2214_);
v___f_2217_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2217_, 0, v_toPure_2214_);
lean_closure_set(v___f_2217_, 1, v___x_2215_);
lean_closure_set(v___f_2217_, 2, v_toBind_2213_);
lean_closure_set(v___f_2217_, 3, v_eq_2210_);
lean_closure_set(v___f_2217_, 4, v_inst_2209_);
lean_inc(v_toPure_2214_);
v___f_2218_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2218_, 0, v_toPure_2214_);
v_sz_2219_ = lean_array_size(v_xs_2211_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2209_, v_xs_2211_, v___f_2217_, v_sz_2219_, v___x_2220_, v_ret_2216_);
v___x_2222_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v___x_2221_, v___f_2218_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2223_, lean_object* v_00_u03b1_2224_, lean_object* v_inst_2225_, lean_object* v_eq_2226_, lean_object* v_xs_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2225_, v_eq_2226_, v_xs_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2229_, size_t v_i_2230_, lean_object* v_bs_2231_){
_start:
{
uint8_t v___x_2232_; 
v___x_2232_ = lean_usize_dec_lt(v_i_2230_, v_sz_2229_);
if (v___x_2232_ == 0)
{
return v_bs_2231_;
}
else
{
lean_object* v_v_2233_; lean_object* v_indGroupInst_2234_; lean_object* v___x_2235_; lean_object* v_bs_x27_2236_; size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
v_v_2233_ = lean_array_uget_borrowed(v_bs_2231_, v_i_2230_);
v_indGroupInst_2234_ = lean_ctor_get(v_v_2233_, 4);
lean_inc_ref(v_indGroupInst_2234_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v_bs_x27_2236_ = lean_array_uset(v_bs_2231_, v_i_2230_, v___x_2235_);
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2230_, v___x_2237_);
v___x_2239_ = lean_array_uset(v_bs_x27_2236_, v_i_2230_, v_indGroupInst_2234_);
v_i_2230_ = v___x_2238_;
v_bs_2231_ = v___x_2239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2241_, lean_object* v_i_2242_, lean_object* v_bs_2243_){
_start:
{
size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2241_);
lean_dec(v_sz_2241_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2244_, v_i_boxed_2245_, v_bs_2243_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2247_, lean_object* v_a_2248_, lean_object* v_as_2249_, size_t v_i_2250_, size_t v_stop_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_eq(v_i_2250_, v_stop_2251_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_array_uget_borrowed(v_as_2249_, v_i_2250_);
lean_inc_ref(v_eq_2247_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v_a_2248_);
lean_inc(v___x_2258_);
v___x_2259_ = lean_apply_7(v_eq_2247_, v___x_2258_, v_a_2248_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2271_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_unbox(v_a_2260_);
if (v___x_2264_ == 0)
{
size_t v___x_2265_; size_t v___x_2266_; 
lean_del_object(v___x_2262_);
lean_dec(v_a_2260_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2250_, v___x_2265_);
v_i_2250_ = v___x_2266_;
goto _start;
}
else
{
lean_object* v___x_2269_; 
lean_dec(v_a_2248_);
lean_dec_ref(v_eq_2247_);
if (v_isShared_2263_ == 0)
{
v___x_2269_ = v___x_2262_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2260_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_dec(v_a_2248_);
lean_dec_ref(v_eq_2247_);
return v___x_2259_;
}
}
else
{
uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec(v_a_2248_);
lean_dec_ref(v_eq_2247_);
v___x_2272_ = 0;
v___x_2273_ = lean_box(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2275_, lean_object* v_a_2276_, lean_object* v_as_2277_, lean_object* v_i_2278_, lean_object* v_stop_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
size_t v_i_boxed_2285_; size_t v_stop_boxed_2286_; lean_object* v_res_2287_; 
v_i_boxed_2285_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_stop_boxed_2286_ = lean_unbox_usize(v_stop_2279_);
lean_dec(v_stop_2279_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2275_, v_a_2276_, v_as_2277_, v_i_boxed_2285_, v_stop_boxed_2286_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_as_2277_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2288_, lean_object* v_a_2289_, uint8_t v_____do__lift_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
if (v_____do__lift_2290_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_array_push(v_b_2288_, v_a_2289_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec(v_a_2289_);
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_b_2288_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2301_, lean_object* v_a_2302_, lean_object* v_____do__lift_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v_____do__lift_1292__boxed_2309_; lean_object* v_res_2310_; 
v_____do__lift_1292__boxed_2309_ = lean_unbox(v_____do__lift_2303_);
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2301_, v_a_2302_, v_____do__lift_1292__boxed_2309_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2311_, lean_object* v_as_2312_, size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_a_2322_; lean_object* v___y_2327_; uint8_t v___x_2346_; 
v___x_2346_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; 
lean_dec_ref(v_eq_2311_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_b_2315_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v_a_2349_ = lean_array_uget_borrowed(v_as_2312_, v_i_2314_);
v___x_2350_ = lean_array_get_size(v_b_2315_);
v___x_2351_ = lean_nat_dec_lt(v___x_2348_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_inc(v_a_2349_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2315_, v_a_2349_, v___x_2351_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2352_;
goto v___jp_2326_;
}
else
{
if (v___x_2351_ == 0)
{
lean_object* v___x_2353_; 
lean_inc(v_a_2349_);
v___x_2353_ = lean_array_push(v_b_2315_, v_a_2349_);
v_a_2322_ = v___x_2353_;
goto v___jp_2321_;
}
else
{
size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = lean_usize_of_nat(v___x_2350_);
lean_inc(v_a_2349_);
lean_inc_ref(v_eq_2311_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2311_, v_a_2349_, v_b_2315_, v___x_2354_, v___x_2355_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
lean_inc(v_a_2349_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2315_, v_a_2349_, v___x_2358_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2327_ = v___x_2359_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_b_2315_);
lean_dec_ref(v_eq_2311_);
v_a_2360_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2356_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2356_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
}
v___jp_2321_:
{
size_t v___x_2323_; size_t v___x_2324_; 
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2314_, v___x_2323_);
v_i_2314_ = v___x_2324_;
v_b_2315_ = v_a_2322_;
goto _start;
}
v___jp_2326_:
{
if (lean_obj_tag(v___y_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
v_a_2328_ = lean_ctor_get(v___y_2327_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2330_ = v___y_2327_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___y_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
if (lean_obj_tag(v_a_2328_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; 
lean_dec_ref(v_eq_2311_);
v_a_2332_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v_a_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v_a_2332_);
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v_a_2336_; 
lean_del_object(v___x_2330_);
v_a_2336_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v_a_2328_);
v_a_2322_ = v_a_2336_;
goto v___jp_2321_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_eq_2311_);
v_a_2338_ = lean_ctor_get(v___y_2327_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___y_2327_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___y_2327_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2368_, lean_object* v_as_2369_, lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_b_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
size_t v_sz_boxed_2378_; size_t v_i_boxed_2379_; lean_object* v_res_2380_; 
v_sz_boxed_2378_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2379_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2368_, v_as_2369_, v_sz_boxed_2378_, v_i_boxed_2379_, v_b_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_as_2369_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2381_, lean_object* v_xs_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_ret_2388_; size_t v_sz_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v_ret_2388_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2389_ = lean_array_size(v_xs_2382_);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2381_, v_xs_2382_, v_sz_2389_, v___x_2390_, v_ret_2388_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2392_, lean_object* v_xs_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2392_, v_xs_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec_ref(v_xs_2393_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; size_t v_sz_2408_; size_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2407_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2408_ = lean_array_size(v_recArgInfos_2401_);
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2408_, v___x_2409_, v_recArgInfos_2401_);
v___x_2411_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2407_, v___x_2410_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec_ref(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2419_, lean_object* v_eq_2420_, lean_object* v_xs_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2420_, v_xs_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_eq_2429_, lean_object* v_xs_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2428_, v_eq_2429_, v_xs_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_xs_2430_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2437_, lean_object* v_eq_2438_, lean_object* v_a_2439_, lean_object* v_as_2440_, size_t v_i_2441_, size_t v_stop_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2438_, v_a_2439_, v_as_2440_, v_i_2441_, v_stop_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2449_, lean_object* v_eq_2450_, lean_object* v_a_2451_, lean_object* v_as_2452_, lean_object* v_i_2453_, lean_object* v_stop_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
size_t v_i_boxed_2460_; size_t v_stop_boxed_2461_; lean_object* v_res_2462_; 
v_i_boxed_2460_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_stop_boxed_2461_ = lean_unbox_usize(v_stop_2454_);
lean_dec(v_stop_2454_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2449_, v_eq_2450_, v_a_2451_, v_as_2452_, v_i_boxed_2460_, v_stop_boxed_2461_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec_ref(v_as_2452_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2463_, lean_object* v_eq_2464_, lean_object* v_as_2465_, size_t v_sz_2466_, size_t v_i_2467_, lean_object* v_b_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2464_, v_as_2465_, v_sz_2466_, v_i_2467_, v_b_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_eq_2476_, lean_object* v_as_2477_, lean_object* v_sz_2478_, lean_object* v_i_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2478_);
lean_dec(v_sz_2478_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2475_, v_eq_2476_, v_as_2477_, v_sz_boxed_2486_, v_i_boxed_2487_, v_b_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v_as_2477_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v___x_2492_; 
v___x_2492_ = l_Lean_Expr_hasMVar(v_e_2489_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_e_2489_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v_mctx_2495_; lean_object* v___x_2496_; lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v___x_2499_; lean_object* v_cache_2500_; lean_object* v_zetaDeltaFVarIds_2501_; lean_object* v_postponed_2502_; lean_object* v_diag_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2512_; 
v___x_2494_ = lean_st_ref_get(v___y_2490_);
v_mctx_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc_ref(v_mctx_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = l_Lean_instantiateMVarsCore(v_mctx_2495_, v_e_2489_);
v_fst_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_fst_2497_);
v_snd_2498_ = lean_ctor_get(v___x_2496_, 1);
lean_inc(v_snd_2498_);
lean_dec_ref(v___x_2496_);
v___x_2499_ = lean_st_ref_take(v___y_2490_);
v_cache_2500_ = lean_ctor_get(v___x_2499_, 1);
v_zetaDeltaFVarIds_2501_ = lean_ctor_get(v___x_2499_, 2);
v_postponed_2502_ = lean_ctor_get(v___x_2499_, 3);
v_diag_2503_ = lean_ctor_get(v___x_2499_, 4);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2499_, 0);
lean_dec(v_unused_2513_);
v___x_2505_ = v___x_2499_;
v_isShared_2506_ = v_isSharedCheck_2512_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_diag_2503_);
lean_inc(v_postponed_2502_);
lean_inc(v_zetaDeltaFVarIds_2501_);
lean_inc(v_cache_2500_);
lean_dec(v___x_2499_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2512_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v_snd_2498_);
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_snd_2498_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_cache_2500_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_zetaDeltaFVarIds_2501_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_postponed_2502_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_diag_2503_);
v___x_2508_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_st_ref_set(v___y_2490_, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_fst_2497_);
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2514_, v___y_2515_);
lean_dec(v___y_2515_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2518_, v___y_2520_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2531_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2534_ = lean_unsigned_to_nat(113u);
v___x_2535_ = lean_unsigned_to_nat(214u);
v___x_2536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2538_ = l_mkPanicMessageWithDecl(v___x_2537_, v___x_2536_, v___x_2535_, v___x_2534_, v___x_2533_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2539_, size_t v_sz_2540_, size_t v_i_2541_, lean_object* v_bs_2542_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_lt(v_i_2541_, v_sz_2540_);
if (v___x_2543_ == 0)
{
return v_bs_2542_;
}
else
{
lean_object* v_v_2544_; lean_object* v___x_2545_; lean_object* v_bs_x27_2546_; lean_object* v___y_2548_; lean_object* v___x_2553_; 
v_v_2544_ = lean_array_uget(v_bs_2542_, v_i_2541_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v_bs_x27_2546_ = lean_array_uset(v_bs_2542_, v_i_2541_, v___x_2545_);
v___x_2553_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2539_, v_v_2544_);
lean_dec(v_v_2544_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2555_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2554_);
v___y_2548_ = v___x_2555_;
goto v___jp_2547_;
}
else
{
lean_object* v_val_2556_; 
v_val_2556_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_val_2556_);
lean_dec_ref(v___x_2553_);
v___y_2548_ = v_val_2556_;
goto v___jp_2547_;
}
v___jp_2547_:
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_add(v_i_2541_, v___x_2549_);
v___x_2551_ = lean_array_uset(v_bs_x27_2546_, v_i_2541_, v___y_2548_);
v_i_2541_ = v___x_2550_;
v_bs_2542_ = v___x_2551_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_bs_2560_){
_start:
{
size_t v_sz_boxed_2561_; size_t v_i_boxed_2562_; lean_object* v_res_2563_; 
v_sz_boxed_2561_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2557_, v_sz_boxed_2561_, v_i_boxed_2562_, v_bs_2560_);
lean_dec_ref(v___x_2557_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2564_, size_t v_i_2565_, lean_object* v_bs_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_usize_dec_lt(v_i_2565_, v_sz_2564_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_bs_2566_);
return v___x_2573_;
}
else
{
lean_object* v_v_2574_; lean_object* v___x_2575_; 
v_v_2574_ = lean_array_uget_borrowed(v_bs_2566_, v_i_2565_);
lean_inc(v_v_2574_);
v___x_2575_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2574_, v___y_2568_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v_bs_x27_2578_; size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v_bs_x27_2578_ = lean_array_uset(v_bs_2566_, v_i_2565_, v___x_2577_);
v___x_2579_ = ((size_t)1ULL);
v___x_2580_ = lean_usize_add(v_i_2565_, v___x_2579_);
v___x_2581_ = lean_array_uset(v_bs_x27_2578_, v_i_2565_, v_a_2576_);
v_i_2565_ = v___x_2580_;
v_bs_2566_ = v___x_2581_;
goto _start;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v_bs_2566_);
v_a_2583_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2575_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2575_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_bs_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2599_, v_i_boxed_2600_, v_bs_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2601_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2602_, lean_object* v___x_2603_, lean_object* v_as_2604_, size_t v_i_2605_, size_t v_stop_2606_){
_start:
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_usize_dec_eq(v_i_2605_, v_stop_2606_);
if (v___x_2607_ == 0)
{
uint8_t v___x_2608_; uint8_t v___y_2610_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2608_ = 1;
v___x_2614_ = lean_array_uget_borrowed(v_as_2604_, v_i_2605_);
v___x_2615_ = l_Lean_Expr_isFVar(v___x_2614_);
if (v___x_2615_ == 0)
{
v___y_2610_ = v_a_2602_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_nat_dec_eq(v___x_2603_, v___x_2616_);
v___y_2610_ = v___x_2617_;
goto v___jp_2609_;
}
v___jp_2609_:
{
if (v___y_2610_ == 0)
{
size_t v___x_2611_; size_t v___x_2612_; 
v___x_2611_ = ((size_t)1ULL);
v___x_2612_ = lean_usize_add(v_i_2605_, v___x_2611_);
v_i_2605_ = v___x_2612_;
goto _start;
}
else
{
return v___x_2608_;
}
}
}
else
{
uint8_t v___x_2618_; 
v___x_2618_ = 0;
return v___x_2618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2619_, lean_object* v___x_2620_, lean_object* v_as_2621_, lean_object* v_i_2622_, lean_object* v_stop_2623_){
_start:
{
uint8_t v_a_9872__boxed_2624_; size_t v_i_boxed_2625_; size_t v_stop_boxed_2626_; uint8_t v_res_2627_; lean_object* v_r_2628_; 
v_a_9872__boxed_2624_ = lean_unbox(v_a_2619_);
v_i_boxed_2625_ = lean_unbox_usize(v_i_2622_);
lean_dec(v_i_2622_);
v_stop_boxed_2626_ = lean_unbox_usize(v_stop_2623_);
lean_dec(v_stop_2623_);
v_res_2627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9872__boxed_2624_, v___x_2620_, v_as_2621_, v_i_boxed_2625_, v_stop_boxed_2626_);
lean_dec_ref(v_as_2621_);
lean_dec(v___x_2620_);
v_r_2628_ = lean_box(v_res_2627_);
return v_r_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_ys_2631_, lean_object* v___x_2632_, lean_object* v_recArgInfo_2633_, lean_object* v___x_2634_, lean_object* v_group_2635_, lean_object* v_as_2636_, size_t v_sz_2637_, size_t v_i_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_a_2646_; uint8_t v___x_2650_; 
v___x_2650_ = lean_usize_dec_lt(v_i_2638_, v_sz_2637_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_b_2639_);
return v___x_2651_;
}
else
{
lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2810_; 
v_snd_2652_ = lean_ctor_get(v_b_2639_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_b_2639_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v_b_2639_, 0);
lean_dec(v_unused_2811_);
v___x_2654_ = v_b_2639_;
v_isShared_2655_ = v_isSharedCheck_2810_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_dec(v_b_2639_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2810_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_next_2656_; lean_object* v_upperBound_2657_; lean_object* v___x_2658_; 
v_next_2656_ = lean_ctor_get(v_snd_2652_, 0);
lean_inc(v_next_2656_);
v_upperBound_2657_ = lean_ctor_get(v_snd_2652_, 1);
v___x_2658_ = lean_box(0);
if (lean_obj_tag(v_next_2656_) == 0)
{
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
goto v___jp_2659_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2809_; 
v_val_2664_ = lean_ctor_get(v_next_2656_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_next_2656_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2666_ = v_next_2656_;
v_isShared_2667_ = v_isSharedCheck_2809_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_val_2664_);
lean_dec(v_next_2656_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2809_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_lt(v_val_2664_, v_upperBound_2657_);
if (v___x_2668_ == 0)
{
lean_del_object(v___x_2666_);
lean_dec(v_val_2664_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2806_; 
lean_inc(v_upperBound_2657_);
lean_del_object(v___x_2654_);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_snd_2652_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2807_ = lean_ctor_get(v_snd_2652_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_snd_2652_, 0);
lean_dec(v_unused_2808_);
v___x_2670_ = v_snd_2652_;
v_isShared_2671_ = v_isSharedCheck_2806_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v_snd_2652_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2806_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; 
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc_ref(v___x_2629_);
v___x_2672_ = lean_infer_type(v___x_2629_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = l_Lean_Meta_whnfD(v_a_2673_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v_a_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref(v___x_2674_);
v_a_2676_ = lean_array_uget_borrowed(v_as_2636_, v_i_2638_);
v___x_2677_ = 0;
lean_inc(v_a_2676_);
v___x_2678_ = l_Lean_Meta_forallMetaTelescope(v_a_2676_, v___x_2677_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_snd_2680_; lean_object* v_fst_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2781_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v_snd_2680_ = lean_ctor_get(v_a_2679_, 1);
v_fst_2681_ = lean_ctor_get(v_a_2679_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2683_ = v_a_2679_;
v_isShared_2684_ = v_isSharedCheck_2781_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2680_);
lean_inc(v_fst_2681_);
lean_dec(v_a_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2781_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_snd_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2779_; 
v_snd_2685_ = lean_ctor_get(v_snd_2680_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_snd_2680_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_snd_2680_, 0);
lean_dec(v_unused_2780_);
v___x_2687_ = v_snd_2680_;
v_isShared_2688_ = v_isSharedCheck_2779_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2685_);
lean_dec(v_snd_2680_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2779_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2685_, v_a_2675_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_nat_add(v_val_2664_, v___x_2691_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2692_);
v___x_2694_ = v___x_2666_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2694_);
v___x_2696_ = v___x_2670_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_upperBound_2657_);
v___x_2696_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_unbox(v_a_2690_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2699_; 
lean_dec(v_a_2690_);
lean_del_object(v___x_2683_);
lean_dec(v_fst_2681_);
lean_dec(v_val_2664_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2696_);
lean_ctor_set(v___x_2687_, 0, v___x_2658_);
v___x_2699_ = v___x_2687_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2696_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
v_a_2646_ = v___x_2699_;
goto v___jp_2645_;
}
}
else
{
size_t v_sz_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v_sz_2701_ = lean_array_size(v_fst_2681_);
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2701_, v___x_2702_, v_fst_2681_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref(v___x_2703_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_nat_dec_eq(v___x_2630_, v___x_2709_);
v___x_2756_ = lean_array_get_size(v_a_2704_);
v___x_2757_ = lean_nat_dec_lt(v___x_2709_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_dec(v_a_2690_);
goto v___jp_2711_;
}
else
{
if (v___x_2757_ == 0)
{
lean_dec(v_a_2690_);
goto v___jp_2711_;
}
else
{
size_t v___x_2758_; uint8_t v___x_2759_; uint8_t v___x_2760_; 
v___x_2758_ = lean_usize_of_nat(v___x_2756_);
v___x_2759_ = lean_unbox(v_a_2690_);
lean_dec(v_a_2690_);
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2759_, v___x_2630_, v_a_2704_, v___x_2702_, v___x_2758_);
if (v___x_2760_ == 0)
{
goto v___jp_2711_;
}
else
{
if (v___x_2710_ == 0)
{
lean_dec(v_a_2704_);
lean_del_object(v___x_2683_);
lean_dec(v_val_2664_);
goto v___jp_2705_;
}
else
{
goto v___jp_2711_;
}
}
}
}
v___jp_2705_:
{
lean_object* v___x_2707_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2696_);
lean_ctor_set(v___x_2687_, 0, v___x_2658_);
v___x_2707_ = v___x_2687_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2696_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
v_a_2646_ = v___x_2707_;
goto v___jp_2645_;
}
}
v___jp_2711_:
{
if (v___x_2710_ == 0)
{
uint8_t v___x_2712_; 
lean_del_object(v___x_2687_);
v___x_2712_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2704_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2714_; 
lean_dec(v_a_2704_);
lean_dec(v_val_2664_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2696_);
lean_ctor_set(v___x_2683_, 0, v___x_2658_);
v___x_2714_ = v___x_2683_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2696_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
v_a_2646_ = v___x_2714_;
goto v___jp_2645_;
}
}
else
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2631_, v_a_2704_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2747_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2747_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2747_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
if (lean_obj_tag(v_a_2717_) == 1)
{
lean_object* v___x_2722_; 
lean_dec_ref(v_a_2717_);
lean_del_object(v___x_2719_);
lean_dec(v_a_2704_);
lean_dec(v_val_2664_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2696_);
lean_ctor_set(v___x_2683_, 0, v___x_2658_);
v___x_2722_ = v___x_2683_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2696_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
v_a_2646_ = v___x_2722_;
goto v___jp_2645_;
}
}
else
{
lean_object* v_fnName_2724_; lean_object* v_fixedParamPerm_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2717_);
lean_dec_ref(v___x_2629_);
v_fnName_2724_ = lean_ctor_get(v_recArgInfo_2633_, 0);
v_fixedParamPerm_2725_ = lean_ctor_get(v_recArgInfo_2633_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_recArgInfo_2633_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; lean_object* v_unused_2744_; lean_object* v_unused_2745_; lean_object* v_unused_2746_; 
v_unused_2743_ = lean_ctor_get(v_recArgInfo_2633_, 5);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_recArgInfo_2633_, 4);
lean_dec(v_unused_2744_);
v_unused_2745_ = lean_ctor_get(v_recArgInfo_2633_, 3);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_recArgInfo_2633_, 2);
lean_dec(v_unused_2746_);
v___x_2727_ = v_recArgInfo_2633_;
v_isShared_2728_ = v_isSharedCheck_2742_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_fixedParamPerm_2725_);
lean_inc(v_fnName_2724_);
lean_dec(v_recArgInfo_2633_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2742_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
size_t v_sz_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v_sz_2729_ = lean_array_size(v_a_2704_);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2632_, v_sz_2729_, v___x_2702_, v_a_2704_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 5, v_val_2664_);
lean_ctor_set(v___x_2727_, 4, v_group_2635_);
lean_ctor_set(v___x_2727_, 3, v___x_2730_);
lean_ctor_set(v___x_2727_, 2, v___x_2634_);
v___x_2732_ = v___x_2727_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_fnName_2724_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_fixedParamPerm_2725_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v_group_2635_);
lean_ctor_set(v_reuseFailAlloc_2741_, 5, v_val_2664_);
v___x_2732_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2696_);
lean_ctor_set(v___x_2683_, 0, v___x_2734_);
v___x_2736_ = v___x_2683_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2696_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2736_);
v___x_2738_ = v___x_2719_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
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
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___x_2696_);
lean_del_object(v___x_2683_);
lean_dec(v_val_2664_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2748_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2716_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2716_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
else
{
lean_dec(v_a_2704_);
lean_del_object(v___x_2683_);
lean_dec(v_val_2664_);
goto v___jp_2705_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v___x_2696_);
lean_dec(v_a_2690_);
lean_del_object(v___x_2687_);
lean_del_object(v___x_2683_);
lean_dec(v_val_2664_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2761_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2703_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2703_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_del_object(v___x_2687_);
lean_del_object(v___x_2683_);
lean_dec(v_fst_2681_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec(v_val_2664_);
lean_dec(v_upperBound_2657_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2771_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2689_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2689_);
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
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2675_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec(v_val_2664_);
lean_dec(v_upperBound_2657_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2782_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2678_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2678_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec(v_val_2664_);
lean_dec(v_upperBound_2657_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2790_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2674_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2674_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
lean_dec(v_val_2664_);
lean_dec(v_upperBound_2657_);
lean_dec_ref(v_group_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_recArgInfo_2633_);
lean_dec_ref(v___x_2629_);
v_a_2798_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2672_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2672_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2661_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2658_);
v___x_2661_ = v___x_2654_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_snd_2652_);
v___x_2661_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
}
}
v___jp_2645_:
{
size_t v___x_2647_; size_t v___x_2648_; 
v___x_2647_ = ((size_t)1ULL);
v___x_2648_ = lean_usize_add(v_i_2638_, v___x_2647_);
v_i_2638_ = v___x_2648_;
v_b_2639_ = v_a_2646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v_ys_2814_, lean_object* v___x_2815_, lean_object* v_recArgInfo_2816_, lean_object* v___x_2817_, lean_object* v_group_2818_, lean_object* v_as_2819_, lean_object* v_sz_2820_, lean_object* v_i_2821_, lean_object* v_b_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
size_t v_sz_boxed_2828_; size_t v_i_boxed_2829_; lean_object* v_res_2830_; 
v_sz_boxed_2828_ = lean_unbox_usize(v_sz_2820_);
lean_dec(v_sz_2820_);
v_i_boxed_2829_ = lean_unbox_usize(v_i_2821_);
lean_dec(v_i_2821_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2812_, v___x_2813_, v_ys_2814_, v___x_2815_, v_recArgInfo_2816_, v___x_2817_, v_group_2818_, v_as_2819_, v_sz_boxed_2828_, v_i_boxed_2829_, v_b_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_as_2819_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_ys_2814_);
lean_dec(v___x_2813_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v_ys_2834_, lean_object* v_recArgInfo_2835_, lean_object* v___x_2836_, lean_object* v_group_2837_, lean_object* v_as_2838_, size_t v_sz_2839_, size_t v_i_2840_, lean_object* v_b_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_a_2848_; uint8_t v___x_2852_; 
v___x_2852_ = lean_usize_dec_lt(v_i_2840_, v_sz_2839_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_b_2841_);
return v___x_2853_;
}
else
{
lean_object* v_snd_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3012_; 
v_snd_2854_ = lean_ctor_get(v_b_2841_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_b_2841_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v_b_2841_, 0);
lean_dec(v_unused_3013_);
v___x_2856_ = v_b_2841_;
v_isShared_2857_ = v_isSharedCheck_3012_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_snd_2854_);
lean_dec(v_b_2841_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3012_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_next_2858_; lean_object* v_upperBound_2859_; lean_object* v___x_2860_; 
v_next_2858_ = lean_ctor_get(v_snd_2854_, 0);
lean_inc(v_next_2858_);
v_upperBound_2859_ = lean_ctor_get(v_snd_2854_, 1);
v___x_2860_ = lean_box(0);
if (lean_obj_tag(v_next_2858_) == 0)
{
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
goto v___jp_2861_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_3011_; 
v_val_2866_ = lean_ctor_get(v_next_2858_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_next_2858_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2868_ = v_next_2858_;
v_isShared_2869_ = v_isSharedCheck_3011_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_val_2866_);
lean_dec(v_next_2858_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_3011_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
uint8_t v___x_2870_; 
v___x_2870_ = lean_nat_dec_lt(v_val_2866_, v_upperBound_2859_);
if (v___x_2870_ == 0)
{
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
goto v___jp_2861_;
}
else
{
lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_3008_; 
lean_inc(v_upperBound_2859_);
lean_del_object(v___x_2856_);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_snd_2854_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; lean_object* v_unused_3010_; 
v_unused_3009_ = lean_ctor_get(v_snd_2854_, 1);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_snd_2854_, 0);
lean_dec(v_unused_3010_);
v___x_2872_ = v_snd_2854_;
v_isShared_2873_ = v_isSharedCheck_3008_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v_snd_2854_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_3008_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; 
lean_inc(v___y_2845_);
lean_inc_ref(v___y_2844_);
lean_inc(v___y_2843_);
lean_inc_ref(v___y_2842_);
lean_inc_ref(v___x_2831_);
v___x_2874_ = lean_infer_type(v___x_2831_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = l_Lean_Meta_whnfD(v_a_2875_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v_a_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
v_a_2878_ = lean_array_uget_borrowed(v_as_2838_, v_i_2840_);
v___x_2879_ = 0;
lean_inc(v_a_2878_);
v___x_2880_ = l_Lean_Meta_forallMetaTelescope(v_a_2878_, v___x_2879_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v_snd_2882_; lean_object* v_fst_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2983_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v_snd_2882_ = lean_ctor_get(v_a_2881_, 1);
v_fst_2883_ = lean_ctor_get(v_a_2881_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2885_ = v_a_2881_;
v_isShared_2886_ = v_isSharedCheck_2983_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_snd_2882_);
lean_inc(v_fst_2883_);
lean_dec(v_a_2881_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2983_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v_snd_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2981_; 
v_snd_2887_ = lean_ctor_get(v_snd_2882_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_snd_2882_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_snd_2882_, 0);
lean_dec(v_unused_2982_);
v___x_2889_ = v_snd_2882_;
v_isShared_2890_ = v_isSharedCheck_2981_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snd_2887_);
lean_dec(v_snd_2882_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2981_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2887_, v_a_2877_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_add(v_val_2866_, v___x_2893_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2894_);
v___x_2896_ = v___x_2868_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2896_);
v___x_2898_ = v___x_2872_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_upperBound_2859_);
v___x_2898_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_unbox(v_a_2892_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2901_; 
lean_dec(v_a_2892_);
lean_del_object(v___x_2885_);
lean_dec(v_fst_2883_);
lean_dec(v_val_2866_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2898_);
lean_ctor_set(v___x_2889_, 0, v___x_2860_);
v___x_2901_ = v___x_2889_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2898_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_a_2848_ = v___x_2901_;
goto v___jp_2847_;
}
}
else
{
size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v_sz_2903_ = lean_array_size(v_fst_2883_);
v___x_2904_ = ((size_t)0ULL);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2903_, v___x_2904_, v_fst_2883_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2911_; uint8_t v___x_2912_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2911_ = lean_unsigned_to_nat(0u);
v___x_2912_ = lean_nat_dec_eq(v___x_2832_, v___x_2911_);
v___x_2958_ = lean_array_get_size(v_a_2906_);
v___x_2959_ = lean_nat_dec_lt(v___x_2911_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec(v_a_2892_);
goto v___jp_2913_;
}
else
{
if (v___x_2959_ == 0)
{
lean_dec(v_a_2892_);
goto v___jp_2913_;
}
else
{
size_t v___x_2960_; uint8_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = lean_usize_of_nat(v___x_2958_);
v___x_2961_ = lean_unbox(v_a_2892_);
lean_dec(v_a_2892_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2961_, v___x_2832_, v_a_2906_, v___x_2904_, v___x_2960_);
if (v___x_2962_ == 0)
{
goto v___jp_2913_;
}
else
{
if (v___x_2912_ == 0)
{
lean_dec(v_a_2906_);
lean_del_object(v___x_2885_);
lean_dec(v_val_2866_);
goto v___jp_2907_;
}
else
{
goto v___jp_2913_;
}
}
}
}
v___jp_2907_:
{
lean_object* v___x_2909_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2898_);
lean_ctor_set(v___x_2889_, 0, v___x_2860_);
v___x_2909_ = v___x_2889_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2898_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
v_a_2848_ = v___x_2909_;
goto v___jp_2847_;
}
}
v___jp_2913_:
{
if (v___x_2912_ == 0)
{
uint8_t v___x_2914_; 
lean_del_object(v___x_2889_);
v___x_2914_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2906_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2916_; 
lean_dec(v_a_2906_);
lean_dec(v_val_2866_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2898_);
lean_ctor_set(v___x_2885_, 0, v___x_2860_);
v___x_2916_ = v___x_2885_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2898_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v_a_2848_ = v___x_2916_;
goto v___jp_2847_;
}
}
else
{
lean_object* v___x_2918_; 
v___x_2918_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2834_, v_a_2906_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2949_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_2949_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2949_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
if (lean_obj_tag(v_a_2919_) == 1)
{
lean_object* v___x_2924_; 
lean_dec_ref(v_a_2919_);
lean_del_object(v___x_2921_);
lean_dec(v_a_2906_);
lean_dec(v_val_2866_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2898_);
lean_ctor_set(v___x_2885_, 0, v___x_2860_);
v___x_2924_ = v___x_2885_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2898_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
v_a_2848_ = v___x_2924_;
goto v___jp_2847_;
}
}
else
{
lean_object* v_fnName_2926_; lean_object* v_fixedParamPerm_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2831_);
v_fnName_2926_ = lean_ctor_get(v_recArgInfo_2835_, 0);
v_fixedParamPerm_2927_ = lean_ctor_get(v_recArgInfo_2835_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_recArgInfo_2835_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; lean_object* v_unused_2946_; lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2945_ = lean_ctor_get(v_recArgInfo_2835_, 5);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_recArgInfo_2835_, 4);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_recArgInfo_2835_, 3);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_recArgInfo_2835_, 2);
lean_dec(v_unused_2948_);
v___x_2929_ = v_recArgInfo_2835_;
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_fixedParamPerm_2927_);
lean_inc(v_fnName_2926_);
lean_dec(v_recArgInfo_2835_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
size_t v_sz_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v_sz_2931_ = lean_array_size(v_a_2906_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2833_, v_sz_2931_, v___x_2904_, v_a_2906_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 5, v_val_2866_);
lean_ctor_set(v___x_2929_, 4, v_group_2837_);
lean_ctor_set(v___x_2929_, 3, v___x_2932_);
lean_ctor_set(v___x_2929_, 2, v___x_2836_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_fnName_2926_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_fixedParamPerm_2927_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_group_2837_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_val_2866_);
v___x_2934_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2898_);
lean_ctor_set(v___x_2885_, 0, v___x_2936_);
v___x_2938_ = v___x_2885_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___x_2898_);
v___x_2938_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2940_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2938_);
v___x_2940_ = v___x_2921_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_a_2906_);
lean_dec_ref(v___x_2898_);
lean_del_object(v___x_2885_);
lean_dec(v_val_2866_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_2950_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2918_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2918_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
else
{
lean_dec(v_a_2906_);
lean_del_object(v___x_2885_);
lean_dec(v_val_2866_);
goto v___jp_2907_;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v___x_2898_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2889_);
lean_del_object(v___x_2885_);
lean_dec(v_val_2866_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_2963_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2905_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2905_);
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
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_del_object(v___x_2889_);
lean_del_object(v___x_2885_);
lean_dec(v_fst_2883_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v_upperBound_2859_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_2973_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2891_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2891_);
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
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2877_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v_upperBound_2859_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_2984_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2880_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2880_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v_upperBound_2859_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_2992_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2876_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2876_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v_upperBound_2859_);
lean_dec_ref(v_group_2837_);
lean_dec(v___x_2836_);
lean_dec_ref(v_recArgInfo_2835_);
lean_dec_ref(v___x_2831_);
v_a_3000_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2874_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2874_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
}
v___jp_2861_:
{
lean_object* v___x_2863_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2860_);
v___x_2863_ = v___x_2856_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_snd_2854_);
v___x_2863_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
}
}
v___jp_2847_:
{
size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_add(v_i_2840_, v___x_2849_);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2831_, v___x_2832_, v_ys_2834_, v___x_2833_, v_recArgInfo_2835_, v___x_2836_, v_group_2837_, v_as_2838_, v_sz_2839_, v___x_2850_, v_a_2848_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
return v___x_2851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object* v___x_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v_ys_3017_, lean_object* v_recArgInfo_3018_, lean_object* v___x_3019_, lean_object* v_group_3020_, lean_object* v_as_3021_, lean_object* v_sz_3022_, lean_object* v_i_3023_, lean_object* v_b_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
size_t v_sz_boxed_3030_; size_t v_i_boxed_3031_; lean_object* v_res_3032_; 
v_sz_boxed_3030_ = lean_unbox_usize(v_sz_3022_);
lean_dec(v_sz_3022_);
v_i_boxed_3031_ = lean_unbox_usize(v_i_3023_);
lean_dec(v_i_3023_);
v_res_3032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3014_, v___x_3015_, v___x_3016_, v_ys_3017_, v_recArgInfo_3018_, v___x_3019_, v_group_3020_, v_as_3021_, v_sz_boxed_3030_, v_i_boxed_3031_, v_b_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_as_3021_);
lean_dec_ref(v_ys_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3033_, lean_object* v_xs_3034_, lean_object* v_recArgPos_3035_, lean_object* v_a_3036_, lean_object* v___x_3037_, lean_object* v___x_3038_, lean_object* v_ys_3039_, lean_object* v_x_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_toIndGroupInfo_3046_; lean_object* v_all_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3086_; 
v_toIndGroupInfo_3046_ = lean_ctor_get(v_group_3033_, 0);
lean_inc_ref(v_toIndGroupInfo_3046_);
v_all_3047_ = lean_ctor_get(v_toIndGroupInfo_3046_, 0);
v___x_3048_ = l_Lean_instInhabitedExpr;
v___x_3049_ = l_Array_append___redArg(v_xs_3034_, v_ys_3039_);
v___x_3050_ = lean_array_get(v___x_3048_, v___x_3049_, v_recArgPos_3035_);
v___x_3051_ = lean_array_get_size(v_all_3047_);
v___x_3052_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3046_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_toIndGroupInfo_3046_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3087_ = lean_ctor_get(v_toIndGroupInfo_3046_, 1);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_toIndGroupInfo_3046_, 0);
lean_dec(v_unused_3088_);
v___x_3054_ = v_toIndGroupInfo_3046_;
v_isShared_3055_ = v_isSharedCheck_3086_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v_toIndGroupInfo_3046_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3086_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3051_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 1, v___x_3052_);
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3052_);
v___x_3058_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; size_t v_sz_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set(v___x_3060_, 1, v___x_3058_);
v_sz_3061_ = lean_array_size(v_a_3036_);
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3050_, v___x_3037_, v___x_3049_, v_ys_3039_, v___x_3038_, v_recArgPos_3035_, v_group_3033_, v_a_3036_, v_sz_3061_, v___x_3062_, v___x_3060_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec_ref(v___x_3049_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3076_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3076_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3076_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v_fst_3068_; 
v_fst_3068_ = lean_ctor_get(v_a_3064_, 0);
lean_inc(v_fst_3068_);
lean_dec(v_a_3064_);
if (lean_obj_tag(v_fst_3068_) == 0)
{
lean_object* v___x_3070_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3059_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3059_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
else
{
lean_object* v_val_3072_; lean_object* v___x_3074_; 
v_val_3072_ = lean_ctor_get(v_fst_3068_, 0);
lean_inc(v_val_3072_);
lean_dec_ref(v_fst_3068_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_val_3072_);
v___x_3074_ = v___x_3066_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_val_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
v_a_3077_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3063_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3063_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3089_, lean_object* v_xs_3090_, lean_object* v_recArgPos_3091_, lean_object* v_a_3092_, lean_object* v___x_3093_, lean_object* v___x_3094_, lean_object* v_ys_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3089_, v_xs_3090_, v_recArgPos_3091_, v_a_3092_, v___x_3093_, v___x_3094_, v_ys_3095_, v_x_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v_x_3096_);
lean_dec_ref(v_ys_3095_);
lean_dec(v___x_3093_);
lean_dec_ref(v_a_3092_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3103_, lean_object* v_a_3104_, lean_object* v_xs_3105_, lean_object* v_value_3106_, lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_a_3117_; lean_object* v_val_3122_; uint8_t v___x_3124_; 
v___x_3124_ = lean_usize_dec_eq(v_i_3108_, v_stop_3109_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v_recArgPos_3126_; lean_object* v_indGroupInst_3127_; lean_object* v___x_3128_; 
v___x_3125_ = lean_array_uget_borrowed(v_as_3107_, v_i_3108_);
v_recArgPos_3126_ = lean_ctor_get(v___x_3125_, 2);
v_indGroupInst_3127_ = lean_ctor_get(v___x_3125_, 4);
lean_inc_ref(v_indGroupInst_3127_);
lean_inc_ref(v_group_3103_);
v___x_3128_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3103_, v_indGroupInst_3127_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; uint8_t v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_array_get_size(v_a_3104_);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = lean_nat_dec_eq(v___x_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___f_3134_; lean_object* v___x_3135_; 
lean_inc(v___x_3125_);
lean_inc_ref(v_a_3104_);
lean_inc(v_recArgPos_3126_);
lean_inc_ref(v_xs_3105_);
lean_inc_ref(v_group_3103_);
v___f_3134_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3134_, 0, v_group_3103_);
lean_closure_set(v___f_3134_, 1, v_xs_3105_);
lean_closure_set(v___f_3134_, 2, v_recArgPos_3126_);
lean_closure_set(v___f_3134_, 3, v_a_3104_);
lean_closure_set(v___f_3134_, 4, v___x_3131_);
lean_closure_set(v___f_3134_, 5, v___x_3125_);
lean_inc_ref(v_value_3106_);
v___x_3135_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3106_, v___f_3134_, v___x_3133_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
if (lean_obj_tag(v_a_3136_) == 0)
{
v_a_3117_ = v_b_3110_;
goto v___jp_3116_;
}
else
{
lean_object* v_val_3137_; 
v_val_3137_ = lean_ctor_get(v_a_3136_, 0);
lean_inc(v_val_3137_);
lean_dec_ref(v_a_3136_);
v_val_3122_ = v_val_3137_;
goto v___jp_3121_;
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_b_3110_);
lean_dec_ref(v_value_3106_);
lean_dec_ref(v_xs_3105_);
lean_dec_ref(v_a_3104_);
lean_dec_ref(v_group_3103_);
v_a_3138_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3135_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3135_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
v_a_3117_ = v_b_3110_;
goto v___jp_3116_;
}
}
else
{
lean_inc(v___x_3125_);
v_val_3122_ = v___x_3125_;
goto v___jp_3121_;
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_b_3110_);
lean_dec_ref(v_value_3106_);
lean_dec_ref(v_xs_3105_);
lean_dec_ref(v_a_3104_);
lean_dec_ref(v_group_3103_);
v_a_3146_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3128_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3128_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v___x_3154_; 
lean_dec_ref(v_value_3106_);
lean_dec_ref(v_xs_3105_);
lean_dec_ref(v_a_3104_);
lean_dec_ref(v_group_3103_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v_b_3110_);
return v___x_3154_;
}
v___jp_3116_:
{
size_t v___x_3118_; size_t v___x_3119_; 
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_add(v_i_3108_, v___x_3118_);
v_i_3108_ = v___x_3119_;
v_b_3110_ = v_a_3117_;
goto _start;
}
v___jp_3121_:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_array_push(v_b_3110_, v_val_3122_);
v_a_3117_ = v___x_3123_;
goto v___jp_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3155_, lean_object* v_a_3156_, lean_object* v_xs_3157_, lean_object* v_value_3158_, lean_object* v_as_3159_, lean_object* v_i_3160_, lean_object* v_stop_3161_, lean_object* v_b_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
size_t v_i_boxed_3168_; size_t v_stop_boxed_3169_; lean_object* v_res_3170_; 
v_i_boxed_3168_ = lean_unbox_usize(v_i_3160_);
lean_dec(v_i_3160_);
v_stop_boxed_3169_ = lean_unbox_usize(v_stop_3161_);
lean_dec(v_stop_3161_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3155_, v_a_3156_, v_xs_3157_, v_value_3158_, v_as_3159_, v_i_boxed_3168_, v_stop_boxed_3169_, v_b_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v_as_3159_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3171_, lean_object* v_a_3172_, lean_object* v_xs_3173_, lean_object* v_value_3174_, lean_object* v_as_3175_, lean_object* v_start_3176_, lean_object* v_stop_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3184_ = lean_nat_dec_lt(v_start_3176_, v_stop_3177_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
lean_dec_ref(v_value_3174_);
lean_dec_ref(v_xs_3173_);
lean_dec_ref(v_a_3172_);
lean_dec_ref(v_group_3171_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = lean_array_get_size(v_as_3175_);
v___x_3187_ = lean_nat_dec_le(v_stop_3177_, v___x_3186_);
if (v___x_3187_ == 0)
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_nat_dec_lt(v_start_3176_, v___x_3186_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v_value_3174_);
lean_dec_ref(v_xs_3173_);
lean_dec_ref(v_a_3172_);
lean_dec_ref(v_group_3171_);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3183_);
return v___x_3189_;
}
else
{
size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_usize_of_nat(v_start_3176_);
v___x_3191_ = lean_usize_of_nat(v___x_3186_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3171_, v_a_3172_, v_xs_3173_, v_value_3174_, v_as_3175_, v___x_3190_, v___x_3191_, v___x_3183_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3192_;
}
}
else
{
size_t v___x_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_usize_of_nat(v_start_3176_);
v___x_3194_ = lean_usize_of_nat(v_stop_3177_);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3171_, v_a_3172_, v_xs_3173_, v_value_3174_, v_as_3175_, v___x_3193_, v___x_3194_, v___x_3183_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3196_, lean_object* v_a_3197_, lean_object* v_xs_3198_, lean_object* v_value_3199_, lean_object* v_as_3200_, lean_object* v_start_3201_, lean_object* v_stop_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3196_, v_a_3197_, v_xs_3198_, v_value_3199_, v_as_3200_, v_start_3201_, v_stop_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v_stop_3202_);
lean_dec(v_start_3201_);
lean_dec_ref(v_as_3200_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3209_, lean_object* v_xs_3210_, lean_object* v_value_3211_, lean_object* v_recArgInfos_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3218_; 
lean_inc_ref(v_group_3209_);
v___x_3218_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3209_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref(v___x_3218_);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_array_get_size(v_recArgInfos_3212_);
v___x_3222_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3209_, v_a_3219_, v_xs_3210_, v_value_3211_, v_recArgInfos_3212_, v___x_3220_, v___x_3221_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3222_;
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v_value_3211_);
lean_dec_ref(v_xs_3210_);
lean_dec_ref(v_group_3209_);
v_a_3223_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3218_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3218_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3231_, lean_object* v_xs_3232_, lean_object* v_value_3233_, lean_object* v_recArgInfos_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Elab_Structural_argsInGroup(v_group_3231_, v_xs_3232_, v_value_3233_, v_recArgInfos_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec_ref(v_recArgInfos_3234_);
return v_res_3240_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_unsigned_to_nat(10u);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3244_, lean_object* v_i_3245_, lean_object* v_acc_3246_){
_start:
{
lean_object* v___x_3247_; uint8_t v___x_3248_; 
v___x_3247_ = lean_array_get_size(v_xss_3244_);
v___x_3248_ = lean_nat_dec_lt(v_i_3245_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_3249_);
v___x_3251_ = lean_array_push(v___x_3250_, v_acc_3246_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3252_ = lean_array_fget_borrowed(v_xss_3244_, v_i_3245_);
v___x_3253_ = lean_unsigned_to_nat(0u);
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3255_ = lean_array_get_size(v___x_3252_);
v___x_3256_ = lean_nat_dec_lt(v___x_3253_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_dec_ref(v_acc_3246_);
return v___x_3254_;
}
else
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_nat_dec_le(v___x_3255_, v___x_3255_);
if (v___x_3257_ == 0)
{
if (v___x_3256_ == 0)
{
lean_dec_ref(v_acc_3246_);
return v___x_3254_;
}
else
{
size_t v___x_3258_; size_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = ((size_t)0ULL);
v___x_3259_ = lean_usize_of_nat(v___x_3255_);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3245_, v_acc_3246_, v_xss_3244_, v___x_3252_, v___x_3258_, v___x_3259_, v___x_3254_);
return v___x_3260_;
}
}
else
{
size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = lean_usize_of_nat(v___x_3255_);
v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3245_, v_acc_3246_, v_xss_3244_, v___x_3252_, v___x_3261_, v___x_3262_, v___x_3254_);
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3264_, lean_object* v_acc_3265_, lean_object* v_xss_3266_, lean_object* v_as_3267_, size_t v_i_3268_, size_t v_stop_3269_, lean_object* v_b_3270_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_usize_dec_eq(v_i_3268_, v_stop_3269_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; 
v___x_3272_ = lean_array_uget_borrowed(v_as_3267_, v_i_3268_);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_add(v_i_3264_, v___x_3273_);
lean_inc(v___x_3272_);
lean_inc_ref(v_acc_3265_);
v___x_3275_ = lean_array_push(v_acc_3265_, v___x_3272_);
v___x_3276_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3266_, v___x_3274_, v___x_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = l_Array_append___redArg(v_b_3270_, v___x_3276_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_add(v_i_3268_, v___x_3278_);
v_i_3268_ = v___x_3279_;
v_b_3270_ = v___x_3277_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3265_);
return v_b_3270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3281_, lean_object* v_acc_3282_, lean_object* v_xss_3283_, lean_object* v_as_3284_, lean_object* v_i_3285_, lean_object* v_stop_3286_, lean_object* v_b_3287_){
_start:
{
size_t v_i_boxed_3288_; size_t v_stop_boxed_3289_; lean_object* v_res_3290_; 
v_i_boxed_3288_ = lean_unbox_usize(v_i_3285_);
lean_dec(v_i_3285_);
v_stop_boxed_3289_ = lean_unbox_usize(v_stop_3286_);
lean_dec(v_stop_3286_);
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3281_, v_acc_3282_, v_xss_3283_, v_as_3284_, v_i_boxed_3288_, v_stop_boxed_3289_, v_b_3287_);
lean_dec_ref(v_as_3284_);
lean_dec_ref(v_xss_3283_);
lean_dec(v_i_3281_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3291_, lean_object* v_i_3292_, lean_object* v_acc_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3291_, v_i_3292_, v_acc_3293_);
lean_dec(v_i_3292_);
lean_dec_ref(v_xss_3291_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3295_, lean_object* v_xss_3296_, lean_object* v_i_3297_, lean_object* v_acc_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3296_, v_i_3297_, v_acc_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3300_, lean_object* v_xss_3301_, lean_object* v_i_3302_, lean_object* v_acc_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3300_, v_xss_3301_, v_i_3302_, v_acc_3303_);
lean_dec(v_i_3302_);
lean_dec_ref(v_xss_3301_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3305_, lean_object* v_i_3306_, lean_object* v_acc_3307_, lean_object* v_xss_3308_, lean_object* v_as_3309_, size_t v_i_3310_, size_t v_stop_3311_, lean_object* v_b_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3306_, v_acc_3307_, v_xss_3308_, v_as_3309_, v_i_3310_, v_stop_3311_, v_b_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_i_3315_, lean_object* v_acc_3316_, lean_object* v_xss_3317_, lean_object* v_as_3318_, lean_object* v_i_3319_, lean_object* v_stop_3320_, lean_object* v_b_3321_){
_start:
{
size_t v_i_boxed_3322_; size_t v_stop_boxed_3323_; lean_object* v_res_3324_; 
v_i_boxed_3322_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_stop_boxed_3323_ = lean_unbox_usize(v_stop_3320_);
lean_dec(v_stop_3320_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3314_, v_i_3315_, v_acc_3316_, v_xss_3317_, v_as_3318_, v_i_boxed_3322_, v_stop_boxed_3323_, v_b_3321_);
lean_dec_ref(v_as_3318_);
lean_dec_ref(v_xss_3317_);
lean_dec(v_i_3315_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3325_, size_t v_i_3326_, size_t v_stop_3327_, lean_object* v_b_3328_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_eq(v_i_3326_, v_stop_3327_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; size_t v___x_3333_; size_t v___x_3334_; 
v___x_3330_ = lean_array_uget_borrowed(v_as_3325_, v_i_3326_);
v___x_3331_ = lean_array_get_size(v___x_3330_);
v___x_3332_ = lean_nat_mul(v_b_3328_, v___x_3331_);
lean_dec(v_b_3328_);
v___x_3333_ = ((size_t)1ULL);
v___x_3334_ = lean_usize_add(v_i_3326_, v___x_3333_);
v_i_3326_ = v___x_3334_;
v_b_3328_ = v___x_3332_;
goto _start;
}
else
{
return v_b_3328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3336_, lean_object* v_i_3337_, lean_object* v_stop_3338_, lean_object* v_b_3339_){
_start:
{
size_t v_i_boxed_3340_; size_t v_stop_boxed_3341_; lean_object* v_res_3342_; 
v_i_boxed_3340_ = lean_unbox_usize(v_i_3337_);
lean_dec(v_i_3337_);
v_stop_boxed_3341_ = lean_unbox_usize(v_stop_3338_);
lean_dec(v_stop_3338_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3336_, v_i_boxed_3340_, v_stop_boxed_3341_, v_b_3339_);
lean_dec_ref(v_as_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___y_3348_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3344_ = lean_unsigned_to_nat(10u);
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_array_get_size(v_xss_3343_);
v___x_3355_ = lean_nat_dec_lt(v___x_3346_, v___x_3354_);
if (v___x_3355_ == 0)
{
v___y_3348_ = v___x_3345_;
goto v___jp_3347_;
}
else
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
if (v___x_3356_ == 0)
{
if (v___x_3355_ == 0)
{
v___y_3348_ = v___x_3345_;
goto v___jp_3347_;
}
else
{
size_t v___x_3357_; size_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = ((size_t)0ULL);
v___x_3358_ = lean_usize_of_nat(v___x_3354_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3343_, v___x_3357_, v___x_3358_, v___x_3345_);
v___y_3348_ = v___x_3359_;
goto v___jp_3347_;
}
}
else
{
size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3354_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3343_, v___x_3360_, v___x_3361_, v___x_3345_);
v___y_3348_ = v___x_3362_;
goto v___jp_3347_;
}
}
v___jp_3347_:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_nat_dec_lt(v___x_3344_, v___y_3348_);
lean_dec(v___y_3348_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3351_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3343_, v___x_3346_, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_box(0);
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3363_);
lean_dec_ref(v_xss_3363_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3365_, lean_object* v_xss_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_xss_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3368_, v_xss_3369_);
lean_dec_ref(v_xss_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3371_, lean_object* v_as_3372_, size_t v_i_3373_, size_t v_stop_3374_, lean_object* v_b_3375_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3372_, v_i_3373_, v_stop_3374_, v_b_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3377_, lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_){
_start:
{
size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; lean_object* v_res_3384_; 
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3377_, v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_, v_b_3381_);
lean_dec_ref(v_as_3378_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_as_3385_, size_t v_i_3386_, size_t v_stop_3387_, lean_object* v_b_3388_){
_start:
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_usize_dec_eq(v_i_3386_, v_stop_3387_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; 
v___x_3390_ = lean_array_uget_borrowed(v_as_3385_, v_i_3386_);
v___x_3391_ = l_Array_append___redArg(v_b_3388_, v___x_3390_);
v___x_3392_ = ((size_t)1ULL);
v___x_3393_ = lean_usize_add(v_i_3386_, v___x_3392_);
v_i_3386_ = v___x_3393_;
v_b_3388_ = v___x_3391_;
goto _start;
}
else
{
return v_b_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6___boxed(lean_object* v_as_3395_, lean_object* v_i_3396_, lean_object* v_stop_3397_, lean_object* v_b_3398_){
_start:
{
size_t v_i_boxed_3399_; size_t v_stop_boxed_3400_; lean_object* v_res_3401_; 
v_i_boxed_3399_ = lean_unbox_usize(v_i_3396_);
lean_dec(v_i_3396_);
v_stop_boxed_3400_ = lean_unbox_usize(v_stop_3397_);
lean_dec(v_stop_3397_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v_as_3395_, v_i_boxed_3399_, v_stop_boxed_3400_, v_b_3398_);
lean_dec_ref(v_as_3395_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(lean_object* v_a_3402_, lean_object* v_as_3403_, size_t v_sz_3404_, size_t v_i_3405_, lean_object* v_b_3406_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_lt(v_i_3405_, v_sz_3404_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
lean_dec_ref(v_a_3402_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_b_3406_);
return v___x_3409_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; size_t v___x_3413_; size_t v___x_3414_; 
v_a_3410_ = lean_array_uget_borrowed(v_as_3403_, v_i_3405_);
lean_inc(v_a_3410_);
lean_inc_ref(v_a_3402_);
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_a_3402_);
lean_ctor_set(v___x_3411_, 1, v_a_3410_);
v___x_3412_ = lean_array_push(v_b_3406_, v___x_3411_);
v___x_3413_ = ((size_t)1ULL);
v___x_3414_ = lean_usize_add(v_i_3405_, v___x_3413_);
v_i_3405_ = v___x_3414_;
v_b_3406_ = v___x_3412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg___boxed(lean_object* v_a_3416_, lean_object* v_as_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_){
_start:
{
size_t v_sz_boxed_3422_; size_t v_i_boxed_3423_; lean_object* v_res_3424_; 
v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3423_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3416_, v_as_3417_, v_sz_boxed_3422_, v_i_boxed_3423_, v_b_3420_);
lean_dec_ref(v_as_3417_);
return v_res_3424_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0(lean_object* v___x_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = lean_array_get_size(v_x_3426_);
v___x_3428_ = lean_nat_dec_eq(v___x_3427_, v___x_3425_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0___boxed(lean_object* v___x_3429_, lean_object* v_x_3430_){
_start:
{
uint8_t v_res_3431_; lean_object* v_r_3432_; 
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___lam__0(v___x_3429_, v_x_3430_);
lean_dec_ref(v_x_3430_);
lean_dec(v___x_3429_);
v_r_3432_ = lean_box(v_res_3431_);
return v_r_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3433_, lean_object* v_xs_3434_, lean_object* v_as_3435_, size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_b_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; 
lean_dec_ref(v_xs_3434_);
lean_dec_ref(v_a_3433_);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_b_3438_);
return v___x_3445_;
}
else
{
lean_object* v_snd_3446_; lean_object* v_fst_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3490_; 
v_snd_3446_ = lean_ctor_get(v_b_3438_, 1);
v_fst_3447_ = lean_ctor_get(v_b_3438_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_b_3438_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3449_ = v_b_3438_;
v_isShared_3450_ = v_isSharedCheck_3490_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_snd_3446_);
lean_inc(v_fst_3447_);
lean_dec(v_b_3438_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3490_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_array_3451_; lean_object* v_start_3452_; lean_object* v_stop_3453_; uint8_t v___x_3454_; 
v_array_3451_ = lean_ctor_get(v_snd_3446_, 0);
v_start_3452_ = lean_ctor_get(v_snd_3446_, 1);
v_stop_3453_ = lean_ctor_get(v_snd_3446_, 2);
v___x_3454_ = lean_nat_dec_lt(v_start_3452_, v_stop_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3456_; 
lean_dec_ref(v_xs_3434_);
lean_dec_ref(v_a_3433_);
if (v_isShared_3450_ == 0)
{
v___x_3456_ = v___x_3449_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3447_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3446_);
v___x_3456_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
else
{
lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3486_; 
lean_inc(v_stop_3453_);
lean_inc(v_start_3452_);
lean_inc_ref(v_array_3451_);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_snd_3446_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3487_ = lean_ctor_get(v_snd_3446_, 2);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_snd_3446_, 1);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_snd_3446_, 0);
lean_dec(v_unused_3489_);
v___x_3460_ = v_snd_3446_;
v_isShared_3461_ = v_isSharedCheck_3486_;
goto v_resetjp_3459_;
}
else
{
lean_dec(v_snd_3446_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3486_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_array_uget_borrowed(v_as_3435_, v_i_3437_);
v___x_3463_ = lean_array_fget_borrowed(v_array_3451_, v_start_3452_);
lean_inc(v_a_3462_);
lean_inc_ref(v_xs_3434_);
lean_inc_ref(v_a_3433_);
v___x_3464_ = l_Lean_Elab_Structural_argsInGroup(v_a_3433_, v_xs_3434_, v_a_3462_, v___x_3463_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_add(v_start_3452_, v___x_3466_);
lean_dec(v_start_3452_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___x_3467_);
v___x_3469_ = v___x_3460_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_array_3451_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_stop_3453_);
v___x_3469_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_array_push(v_fst_3447_, v_a_3465_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v___x_3469_);
lean_ctor_set(v___x_3449_, 0, v___x_3470_);
v___x_3472_ = v___x_3449_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3469_);
v___x_3472_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
size_t v___x_3473_; size_t v___x_3474_; 
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3437_, v___x_3473_);
v_i_3437_ = v___x_3474_;
v_b_3438_ = v___x_3472_;
goto _start;
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_del_object(v___x_3460_);
lean_dec(v_stop_3453_);
lean_dec(v_start_3452_);
lean_dec_ref(v_array_3451_);
lean_del_object(v___x_3449_);
lean_dec(v_fst_3447_);
lean_dec_ref(v_xs_3434_);
lean_dec_ref(v_a_3433_);
v_a_3478_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3464_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3464_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3491_, lean_object* v_xs_3492_, lean_object* v_as_3493_, lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3491_, v_xs_3492_, v_as_3493_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_as_3493_);
return v_res_3504_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__2));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__4));
v___x_3514_ = l_Lean_stringToMessageData(v___x_3513_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__6));
v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
return v___x_3517_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__8));
v___x_3520_ = l_Lean_stringToMessageData(v___x_3519_);
return v___x_3520_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__10));
v___x_3523_ = l_Lean_stringToMessageData(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__12));
v___x_3526_ = l_Lean_stringToMessageData(v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(lean_object* v___x_3527_, lean_object* v_values_3528_, lean_object* v_xs_3529_, lean_object* v_fnNames_3530_, lean_object* v_as_3531_, size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_a_3541_; uint8_t v___x_3545_; 
v___x_3545_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref(v_xs_3529_);
lean_dec_ref(v___x_3527_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_b_3534_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v_recArgInfoss_3548_; lean_object* v_a_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; size_t v_sz_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v_a_3549_ = lean_array_uget_borrowed(v_as_3531_, v_i_3533_);
v___x_3550_ = lean_array_get_size(v___x_3527_);
lean_inc_ref(v___x_3527_);
v___x_3551_ = l_Array_toSubarray___redArg(v___x_3527_, v___x_3547_, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_recArgInfoss_3548_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v_sz_3553_ = lean_array_size(v_values_3528_);
v___x_3554_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3529_);
lean_inc(v_a_3549_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3549_, v_xs_3529_, v_values_3528_, v_sz_3553_, v___x_3554_, v___x_3552_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3617_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v_fst_3557_ = lean_ctor_get(v_b_3534_, 0);
v_snd_3558_ = lean_ctor_get(v_b_3534_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_b_3534_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3560_ = v_b_3534_;
v_isShared_3561_ = v_isSharedCheck_3617_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_inc(v_fst_3557_);
lean_dec(v_b_3534_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3617_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_fst_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3615_; 
v_fst_3562_ = lean_ctor_get(v_a_3556_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_a_3556_, 1);
lean_dec(v_unused_3616_);
v___x_3564_ = v_a_3556_;
v_isShared_3565_ = v_isSharedCheck_3615_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_fst_3562_);
lean_dec(v_a_3556_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3615_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___f_3566_; lean_object* v___x_3567_; 
v___f_3566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1));
v___x_3567_ = l_Array_findIdx_x3f_loop___redArg(v___f_3566_, v_fst_3562_, v___x_3547_);
if (lean_obj_tag(v___x_3567_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
lean_dec(v_fst_3562_);
v_val_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_val_3568_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3);
lean_inc(v_a_3549_);
v___x_3571_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3549_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 7);
lean_ctor_set(v___x_3560_, 1, v___x_3571_);
lean_ctor_set(v___x_3560_, 0, v___x_3570_);
v___x_3573_ = v___x_3560_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3574_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5);
v___x_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_array_get_borrowed(v___x_3569_, v_fnNames_3530_, v_val_3568_);
lean_dec(v_val_3568_);
lean_inc(v___x_3576_);
v___x_3577_ = l_Lean_MessageData_ofName(v___x_3576_);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3575_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v_fst_3557_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v_snd_3558_);
lean_ctor_set(v___x_3564_, 0, v___x_3581_);
v___x_3583_ = v___x_3564_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_snd_3558_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
v_a_3541_ = v___x_3583_;
goto v___jp_3540_;
}
}
}
else
{
lean_object* v___x_3586_; 
lean_dec(v___x_3567_);
v___x_3586_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3562_);
lean_dec(v_fst_3562_);
if (lean_obj_tag(v___x_3586_) == 1)
{
lean_object* v_val_3587_; size_t v_sz_3588_; lean_object* v___x_3589_; 
lean_del_object(v___x_3560_);
v_val_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_val_3587_);
lean_dec_ref(v___x_3586_);
v_sz_3588_ = lean_array_size(v_val_3587_);
lean_inc(v_a_3549_);
v___x_3589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3549_, v_val_3587_, v_sz_3588_, v___x_3554_, v_snd_3558_);
lean_dec(v_val_3587_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref(v___x_3589_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v_a_3590_);
lean_ctor_set(v___x_3564_, 0, v_fst_3557_);
v___x_3592_ = v___x_3564_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_fst_3557_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_a_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
v_a_3541_ = v___x_3592_;
goto v___jp_3540_;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_del_object(v___x_3564_);
lean_dec(v_fst_3557_);
lean_dec_ref(v_xs_3529_);
lean_dec_ref(v___x_3527_);
v_a_3594_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3589_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3589_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec(v___x_3586_);
v___x_3602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9);
lean_inc(v_a_3549_);
v___x_3603_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3549_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set_tag(v___x_3560_, 7);
lean_ctor_set(v___x_3560_, 1, v___x_3603_);
lean_ctor_set(v___x_3560_, 0, v___x_3602_);
v___x_3605_ = v___x_3560_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_fst_3557_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v_snd_3558_);
lean_ctor_set(v___x_3564_, 0, v___x_3610_);
v___x_3612_ = v___x_3564_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_snd_3558_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
v_a_3541_ = v___x_3612_;
goto v___jp_3540_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_b_3534_);
lean_dec_ref(v_xs_3529_);
lean_dec_ref(v___x_3527_);
v_a_3618_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3555_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3555_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
v___jp_3540_:
{
size_t v___x_3542_; size_t v___x_3543_; 
v___x_3542_ = ((size_t)1ULL);
v___x_3543_ = lean_usize_add(v_i_3533_, v___x_3542_);
v_i_3533_ = v___x_3543_;
v_b_3534_ = v_a_3541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___boxed(lean_object* v___x_3626_, lean_object* v_values_3627_, lean_object* v_xs_3628_, lean_object* v_fnNames_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(v___x_3626_, v_values_3627_, v_xs_3628_, v_fnNames_3629_, v_as_3630_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v_as_3630_);
lean_dec_ref(v_fnNames_3629_);
lean_dec_ref(v_values_3627_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_xs_3642_, lean_object* v___x_3643_, lean_object* v_values_3644_, lean_object* v_fnNames_3645_, lean_object* v_as_3646_, size_t v_sz_3647_, size_t v_i_3648_, lean_object* v_b_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_a_3656_; uint8_t v___x_3660_; 
v___x_3660_ = lean_usize_dec_lt(v_i_3648_, v_sz_3647_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec_ref(v___x_3643_);
lean_dec_ref(v_xs_3642_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_b_3649_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; lean_object* v_recArgInfoss_3663_; lean_object* v_a_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v_sz_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v___x_3662_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v_a_3664_ = lean_array_uget_borrowed(v_as_3646_, v_i_3648_);
v___x_3665_ = lean_array_get_size(v___x_3643_);
lean_inc_ref(v___x_3643_);
v___x_3666_ = l_Array_toSubarray___redArg(v___x_3643_, v___x_3662_, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v_recArgInfoss_3663_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v_sz_3668_ = lean_array_size(v_values_3644_);
v___x_3669_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3642_);
lean_inc(v_a_3664_);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3664_, v_xs_3642_, v_values_3644_, v_sz_3668_, v___x_3669_, v___x_3667_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_fst_3672_; lean_object* v_snd_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3732_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
v_fst_3672_ = lean_ctor_get(v_b_3649_, 0);
v_snd_3673_ = lean_ctor_get(v_b_3649_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_b_3649_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3675_ = v_b_3649_;
v_isShared_3676_ = v_isSharedCheck_3732_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_snd_3673_);
lean_inc(v_fst_3672_);
lean_dec(v_b_3649_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3732_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_fst_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3730_; 
v_fst_3677_ = lean_ctor_get(v_a_3671_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_a_3671_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_a_3671_, 1);
lean_dec(v_unused_3731_);
v___x_3679_ = v_a_3671_;
v_isShared_3680_ = v_isSharedCheck_3730_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_fst_3677_);
lean_dec(v_a_3671_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3730_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___f_3681_; lean_object* v___x_3682_; 
v___f_3681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__1));
v___x_3682_ = l_Array_findIdx_x3f_loop___redArg(v___f_3681_, v_fst_3677_, v___x_3662_);
if (lean_obj_tag(v___x_3682_) == 1)
{
lean_object* v_val_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_dec(v_fst_3677_);
v_val_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_val_3683_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__3);
lean_inc(v_a_3664_);
v___x_3686_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3664_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 7);
lean_ctor_set(v___x_3675_, 1, v___x_3686_);
lean_ctor_set(v___x_3675_, 0, v___x_3685_);
v___x_3688_ = v___x_3675_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__5);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_array_get_borrowed(v___x_3684_, v_fnNames_3645_, v_val_3683_);
lean_dec(v_val_3683_);
lean_inc(v___x_3691_);
v___x_3692_ = l_Lean_MessageData_ofName(v___x_3691_);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3690_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__7);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_fst_3672_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v_snd_3673_);
lean_ctor_set(v___x_3679_, 0, v___x_3696_);
v___x_3698_ = v___x_3679_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_snd_3673_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
v_a_3656_ = v___x_3698_;
goto v___jp_3655_;
}
}
}
else
{
lean_object* v___x_3701_; 
lean_dec(v___x_3682_);
v___x_3701_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3677_);
lean_dec(v_fst_3677_);
if (lean_obj_tag(v___x_3701_) == 1)
{
lean_object* v_val_3702_; size_t v_sz_3703_; lean_object* v___x_3704_; 
lean_del_object(v___x_3675_);
v_val_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_val_3702_);
lean_dec_ref(v___x_3701_);
v_sz_3703_ = lean_array_size(v_val_3702_);
lean_inc(v_a_3664_);
v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_3664_, v_val_3702_, v_sz_3703_, v___x_3669_, v_snd_3673_);
lean_dec(v_val_3702_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v_a_3705_);
lean_ctor_set(v___x_3679_, 0, v_fst_3672_);
v___x_3707_ = v___x_3679_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_fst_3672_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_a_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
v_a_3656_ = v___x_3707_;
goto v___jp_3655_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3679_);
lean_dec(v_fst_3672_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v_xs_3642_);
v_a_3709_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3704_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3704_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec(v___x_3701_);
v___x_3717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__9);
lean_inc(v_a_3664_);
v___x_3718_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3664_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 7);
lean_ctor_set(v___x_3675_, 1, v___x_3718_);
lean_ctor_set(v___x_3675_, 0, v___x_3717_);
v___x_3720_ = v___x_3675_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3721_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__11);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v_fst_3672_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__13);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v_snd_3673_);
lean_ctor_set(v___x_3679_, 0, v___x_3725_);
v___x_3727_ = v___x_3679_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_snd_3673_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
v_a_3656_ = v___x_3727_;
goto v___jp_3655_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_b_3649_);
lean_dec_ref(v___x_3643_);
lean_dec_ref(v_xs_3642_);
v_a_3733_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3670_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3670_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
v___jp_3655_:
{
size_t v___x_3657_; size_t v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = ((size_t)1ULL);
v___x_3658_ = lean_usize_add(v_i_3648_, v___x_3657_);
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4(v___x_3643_, v_values_3644_, v_xs_3642_, v_fnNames_3645_, v_as_3646_, v_sz_3647_, v___x_3658_, v_a_3656_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_xs_3741_, lean_object* v___x_3742_, lean_object* v_values_3743_, lean_object* v_fnNames_3744_, lean_object* v_as_3745_, lean_object* v_sz_3746_, lean_object* v_i_3747_, lean_object* v_b_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3746_);
lean_dec(v_sz_3746_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3747_);
lean_dec(v_i_3747_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_xs_3741_, v___x_3742_, v_values_3743_, v_fnNames_3744_, v_as_3745_, v_sz_boxed_3754_, v_i_boxed_3755_, v_b_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_as_3745_);
lean_dec_ref(v_fnNames_3744_);
lean_dec_ref(v_values_3743_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3757_, size_t v_i_3758_, lean_object* v_bs_3759_){
_start:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_usize_dec_lt(v_i_3758_, v_sz_3757_);
if (v___x_3760_ == 0)
{
return v_bs_3759_;
}
else
{
lean_object* v_v_3761_; lean_object* v___x_3762_; lean_object* v_bs_x27_3763_; lean_object* v___x_3764_; size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v_v_3761_ = lean_array_uget(v_bs_3759_, v_i_3758_);
v___x_3762_ = lean_unsigned_to_nat(0u);
v_bs_x27_3763_ = lean_array_uset(v_bs_3759_, v_i_3758_, v___x_3762_);
v___x_3764_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3761_);
lean_dec(v_v_3761_);
v___x_3765_ = ((size_t)1ULL);
v___x_3766_ = lean_usize_add(v_i_3758_, v___x_3765_);
v___x_3767_ = lean_array_uset(v_bs_x27_3763_, v_i_3758_, v___x_3764_);
v_i_3758_ = v___x_3766_;
v_bs_3759_ = v___x_3767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3769_, lean_object* v_i_3770_, lean_object* v_bs_3771_){
_start:
{
size_t v_sz_boxed_3772_; size_t v_i_boxed_3773_; lean_object* v_res_3774_; 
v_sz_boxed_3772_ = lean_unbox_usize(v_sz_3769_);
lean_dec(v_sz_3769_);
v_i_boxed_3773_ = lean_unbox_usize(v_i_3770_);
lean_dec(v_i_3770_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3772_, v_i_boxed_3773_, v_bs_3771_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3775_, lean_object* v_as_3776_, size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_b_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; 
lean_dec_ref(v_xs_3775_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v_b_3779_);
return v___x_3786_;
}
else
{
lean_object* v_snd_3787_; lean_object* v_snd_3788_; lean_object* v_snd_3789_; lean_object* v_snd_3790_; lean_object* v_fst_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3935_; 
v_snd_3787_ = lean_ctor_get(v_b_3779_, 1);
lean_inc(v_snd_3787_);
v_snd_3788_ = lean_ctor_get(v_snd_3787_, 1);
lean_inc(v_snd_3788_);
v_snd_3789_ = lean_ctor_get(v_snd_3788_, 1);
lean_inc(v_snd_3789_);
v_snd_3790_ = lean_ctor_get(v_snd_3789_, 1);
lean_inc(v_snd_3790_);
v_fst_3791_ = lean_ctor_get(v_b_3779_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_b_3779_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v_b_3779_, 1);
lean_dec(v_unused_3936_);
v___x_3793_ = v_b_3779_;
v_isShared_3794_ = v_isSharedCheck_3935_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_fst_3791_);
lean_dec(v_b_3779_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3935_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v_fst_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3933_; 
v_fst_3795_ = lean_ctor_get(v_snd_3787_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_snd_3787_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v_snd_3787_, 1);
lean_dec(v_unused_3934_);
v___x_3797_ = v_snd_3787_;
v_isShared_3798_ = v_isSharedCheck_3933_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_fst_3795_);
lean_dec(v_snd_3787_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3933_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v_fst_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3931_; 
v_fst_3799_ = lean_ctor_get(v_snd_3788_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_snd_3788_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_snd_3788_, 1);
lean_dec(v_unused_3932_);
v___x_3801_ = v_snd_3788_;
v_isShared_3802_ = v_isSharedCheck_3931_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_fst_3799_);
lean_dec(v_snd_3788_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3931_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v_fst_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3929_; 
v_fst_3803_ = lean_ctor_get(v_snd_3789_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_snd_3789_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_snd_3789_, 1);
lean_dec(v_unused_3930_);
v___x_3805_ = v_snd_3789_;
v_isShared_3806_ = v_isSharedCheck_3929_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_fst_3803_);
lean_dec(v_snd_3789_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3929_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_array_3807_; lean_object* v_start_3808_; lean_object* v_stop_3809_; uint8_t v___x_3810_; 
v_array_3807_ = lean_ctor_get(v_snd_3790_, 0);
v_start_3808_ = lean_ctor_get(v_snd_3790_, 1);
v_stop_3809_ = lean_ctor_get(v_snd_3790_, 2);
v___x_3810_ = lean_nat_dec_lt(v_start_3808_, v_stop_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3812_; 
lean_dec_ref(v_xs_3775_);
if (v_isShared_3806_ == 0)
{
v___x_3812_ = v___x_3805_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_fst_3803_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_snd_3790_);
v___x_3812_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3812_);
v___x_3814_ = v___x_3801_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_fst_3799_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v___x_3814_);
v___x_3816_ = v___x_3797_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_fst_3795_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3818_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___x_3816_);
v___x_3818_ = v___x_3793_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_fst_3791_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
return v___x_3819_;
}
}
}
}
}
else
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3925_; 
lean_inc(v_stop_3809_);
lean_inc(v_start_3808_);
lean_inc_ref(v_array_3807_);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_snd_3790_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; lean_object* v_unused_3927_; lean_object* v_unused_3928_; 
v_unused_3926_ = lean_ctor_get(v_snd_3790_, 2);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_snd_3790_, 1);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_snd_3790_, 0);
lean_dec(v_unused_3928_);
v___x_3825_ = v_snd_3790_;
v_isShared_3826_ = v_isSharedCheck_3925_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_snd_3790_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3925_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_array_3827_; lean_object* v_start_3828_; lean_object* v_stop_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v_array_3827_ = lean_ctor_get(v_fst_3803_, 0);
v_start_3828_ = lean_ctor_get(v_fst_3803_, 1);
v_stop_3829_ = lean_ctor_get(v_fst_3803_, 2);
v___x_3830_ = lean_array_fget(v_array_3807_, v_start_3808_);
v___x_3831_ = lean_unsigned_to_nat(1u);
v___x_3832_ = lean_nat_add(v_start_3808_, v___x_3831_);
lean_dec(v_start_3808_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 1, v___x_3832_);
v___x_3834_ = v___x_3825_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_array_3807_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_stop_3809_);
v___x_3834_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_lt(v_start_3828_, v_stop_3829_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3837_; 
lean_dec(v___x_3830_);
lean_dec_ref(v_xs_3775_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3834_);
v___x_3837_ = v___x_3805_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_fst_3803_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3834_);
v___x_3837_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3839_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3837_);
v___x_3839_ = v___x_3801_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_fst_3799_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3841_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v___x_3839_);
v___x_3841_ = v___x_3797_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_fst_3795_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3843_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___x_3841_);
v___x_3843_ = v___x_3793_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3791_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
return v___x_3844_;
}
}
}
}
}
else
{
lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3920_; 
lean_inc(v_stop_3829_);
lean_inc(v_start_3828_);
lean_inc_ref(v_array_3827_);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_fst_3803_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3921_ = lean_ctor_get(v_fst_3803_, 2);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_fst_3803_, 1);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_fst_3803_, 0);
lean_dec(v_unused_3923_);
v___x_3850_ = v_fst_3803_;
v_isShared_3851_ = v_isSharedCheck_3920_;
goto v_resetjp_3849_;
}
else
{
lean_dec(v_fst_3803_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3920_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v_array_3852_; lean_object* v_start_3853_; lean_object* v_stop_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v_array_3852_ = lean_ctor_get(v_fst_3799_, 0);
v_start_3853_ = lean_ctor_get(v_fst_3799_, 1);
v_stop_3854_ = lean_ctor_get(v_fst_3799_, 2);
v___x_3855_ = lean_array_fget(v_array_3827_, v_start_3828_);
v___x_3856_ = lean_nat_add(v_start_3828_, v___x_3831_);
lean_dec(v_start_3828_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3856_);
v___x_3858_ = v___x_3850_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_array_3827_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_stop_3829_);
v___x_3858_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
uint8_t v___x_3859_; 
v___x_3859_ = lean_nat_dec_lt(v_start_3853_, v_stop_3854_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v___x_3855_);
lean_dec(v___x_3830_);
lean_dec_ref(v_xs_3775_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3834_);
lean_ctor_set(v___x_3805_, 0, v___x_3858_);
v___x_3861_ = v___x_3805_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3834_);
v___x_3861_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3861_);
v___x_3863_ = v___x_3801_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_fst_3799_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v___x_3863_);
v___x_3865_ = v___x_3797_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_fst_3795_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___x_3865_);
v___x_3867_ = v___x_3793_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_fst_3791_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
}
}
}
else
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3915_; 
lean_inc(v_stop_3854_);
lean_inc(v_start_3853_);
lean_inc_ref(v_array_3852_);
lean_del_object(v___x_3793_);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_fst_3799_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; 
v_unused_3916_ = lean_ctor_get(v_fst_3799_, 2);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_fst_3799_, 1);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_fst_3799_, 0);
lean_dec(v_unused_3918_);
v___x_3874_ = v_fst_3799_;
v_isShared_3875_ = v_isSharedCheck_3915_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v_fst_3799_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3915_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_a_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3876_ = lean_array_uget_borrowed(v_as_3776_, v_i_3778_);
v___x_3877_ = lean_array_fget_borrowed(v_array_3852_, v_start_3853_);
lean_inc(v___x_3877_);
lean_inc_ref(v_xs_3775_);
lean_inc(v_a_3876_);
v___x_3878_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3876_, v___x_3830_, v_xs_3775_, v___x_3877_, v___x_3855_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_fst_3880_; lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3906_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref(v___x_3878_);
v_fst_3880_ = lean_ctor_get(v_a_3879_, 0);
v_snd_3881_ = lean_ctor_get(v_a_3879_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3883_ = v_a_3879_;
v_isShared_3884_ = v_isSharedCheck_3906_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_inc(v_fst_3880_);
lean_dec(v_a_3879_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3906_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_nat_add(v_start_3853_, v___x_3831_);
lean_dec(v_start_3853_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 1, v___x_3885_);
v___x_3887_ = v___x_3874_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_array_3852_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_stop_3854_);
v___x_3887_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v_fst_3791_);
lean_ctor_set(v___x_3888_, 1, v_snd_3881_);
v___x_3889_ = lean_array_push(v_fst_3795_, v_fst_3880_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v___x_3834_);
lean_ctor_set(v___x_3883_, 0, v___x_3858_);
v___x_3891_ = v___x_3883_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3834_);
v___x_3891_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3891_);
lean_ctor_set(v___x_3805_, 0, v___x_3887_);
v___x_3893_ = v___x_3805_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3895_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3893_);
lean_ctor_set(v___x_3801_, 0, v___x_3889_);
v___x_3895_ = v___x_3801_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v___x_3895_);
lean_ctor_set(v___x_3797_, 0, v___x_3888_);
v___x_3897_ = v___x_3797_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3778_, v___x_3898_);
v_i_3778_ = v___x_3899_;
v_b_3779_ = v___x_3897_;
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
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_del_object(v___x_3874_);
lean_dec_ref(v___x_3858_);
lean_dec(v_stop_3854_);
lean_dec(v_start_3853_);
lean_dec_ref(v_array_3852_);
lean_dec_ref(v___x_3834_);
lean_del_object(v___x_3805_);
lean_del_object(v___x_3801_);
lean_del_object(v___x_3797_);
lean_dec(v_fst_3795_);
lean_dec(v_fst_3791_);
lean_dec_ref(v_xs_3775_);
v_a_3907_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3878_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3878_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3937_, lean_object* v_as_3938_, lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
size_t v_sz_boxed_3947_; size_t v_i_boxed_3948_; lean_object* v_res_3949_; 
v_sz_boxed_3947_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3948_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3937_, v_as_3938_, v_sz_boxed_3947_, v_i_boxed_3948_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec_ref(v_as_3938_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
if (lean_obj_tag(v_a_3950_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = l_List_reverse___redArg(v_a_3951_);
return v___x_3952_;
}
else
{
lean_object* v_head_3953_; lean_object* v_tail_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3964_; 
v_head_3953_ = lean_ctor_get(v_a_3950_, 0);
v_tail_3954_ = lean_ctor_get(v_a_3950_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_a_3950_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3956_ = v_a_3950_;
v_isShared_3957_ = v_isSharedCheck_3964_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_tail_3954_);
lean_inc(v_head_3953_);
lean_dec(v_a_3950_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3964_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3958_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3953_);
v___x_3959_ = l_Lean_MessageData_ofFormat(v___x_3958_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v_a_3951_);
lean_ctor_set(v___x_3956_, 0, v___x_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_a_3951_);
v___x_3961_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
v_a_3950_ = v_tail_3954_;
v_a_3951_ = v___x_3961_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
if (lean_obj_tag(v_a_3965_) == 0)
{
lean_object* v___x_3967_; 
v___x_3967_ = l_List_reverse___redArg(v_a_3966_);
return v___x_3967_;
}
else
{
lean_object* v_head_3968_; lean_object* v_tail_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3978_; 
v_head_3968_ = lean_ctor_get(v_a_3965_, 0);
v_tail_3969_ = lean_ctor_get(v_a_3965_, 1);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_a_3965_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3971_ = v_a_3965_;
v_isShared_3972_ = v_isSharedCheck_3978_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_tail_3969_);
lean_inc(v_head_3968_);
lean_dec(v_a_3965_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3978_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3968_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v_a_3966_);
lean_ctor_set(v___x_3971_, 0, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_a_3966_);
v___x_3975_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
v_a_3965_ = v_tail_3969_;
v_a_3966_ = v___x_3975_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3983_ = l_Lean_MessageData_ofFormat(v___x_3982_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3985_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3986_ = l_Lean_stringToMessageData(v___x_3985_);
return v___x_3986_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3991_ = l_Lean_stringToMessageData(v___x_3990_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_box(1);
v___x_3993_ = l_Lean_MessageData_ofFormat(v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3994_, lean_object* v_fixedParamPerms_3995_, lean_object* v_xs_3996_, lean_object* v_values_3997_, lean_object* v_termMeasure_x3fs_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___x_4004_; lean_object* v_recArgInfoss_4005_; lean_object* v___x_4006_; lean_object* v_perms_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v_report_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; size_t v_sz_4018_; size_t v___x_4019_; lean_object* v___x_4020_; 
v___x_4004_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_4005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4_spec__4___closed__0));
v___x_4006_ = lean_array_get_size(v_values_3997_);
v_perms_4007_ = lean_ctor_get(v_fixedParamPerms_3995_, 1);
lean_inc_ref(v_perms_4007_);
lean_dec_ref(v_fixedParamPerms_3995_);
lean_inc_ref(v_values_3997_);
v___x_4008_ = l_Array_toSubarray___redArg(v_values_3997_, v___x_4004_, v___x_4006_);
v___x_4009_ = lean_array_get_size(v_termMeasure_x3fs_3998_);
v_report_4010_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_4011_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3998_, v___x_4004_, v___x_4009_);
v___x_4012_ = lean_array_get_size(v_perms_4007_);
v___x_4013_ = l_Array_toSubarray___redArg(v_perms_4007_, v___x_4004_, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4011_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4008_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v_recArgInfoss_4005_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4017_, 0, v_report_4010_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v_sz_4018_ = lean_array_size(v_fnNames_3994_);
v___x_4019_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3996_);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3996_, v_fnNames_3994_, v_sz_4018_, v___x_4019_, v___x_4017_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v_snd_4022_; lean_object* v_fst_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4162_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref(v___x_4020_);
v_snd_4022_ = lean_ctor_get(v_a_4021_, 1);
v_fst_4023_ = lean_ctor_get(v_a_4021_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_a_4021_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4025_ = v_a_4021_;
v_isShared_4026_ = v_isSharedCheck_4162_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_snd_4022_);
lean_inc(v_fst_4023_);
lean_dec(v_a_4021_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4162_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v_fst_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4160_; 
v_fst_4027_ = lean_ctor_get(v_snd_4022_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_snd_4022_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v_snd_4022_, 1);
lean_dec(v_unused_4161_);
v___x_4029_ = v_snd_4022_;
v_isShared_4030_ = v_isSharedCheck_4160_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_fst_4027_);
lean_dec(v_snd_4022_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4160_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_a_4033_; size_t v_sz_4034_; lean_object* v___x_4035_; lean_object* v___y_4037_; lean_object* v_report_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; uint8_t v___x_4132_; 
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4032_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v___x_4031_, v_a_4001_);
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v___x_4032_);
v_sz_4034_ = lean_array_size(v_fst_4027_);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4034_, v___x_4019_, v_fst_4027_);
v___x_4132_ = lean_unbox(v_a_4033_);
lean_dec(v_a_4033_);
if (v___x_4132_ == 0)
{
v___y_4120_ = v_a_3999_;
v___y_4121_ = v_a_4000_;
v___y_4122_ = v_a_4001_;
v___y_4123_ = v_a_4002_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4133_; lean_object* v___y_4135_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v___x_4133_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4153_ = lean_array_get_size(v___x_4035_);
v___x_4154_ = lean_nat_dec_lt(v___x_4004_, v___x_4153_);
if (v___x_4154_ == 0)
{
v___y_4135_ = v___x_4152_;
goto v___jp_4134_;
}
else
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_nat_dec_le(v___x_4153_, v___x_4153_);
if (v___x_4155_ == 0)
{
if (v___x_4154_ == 0)
{
v___y_4135_ = v___x_4152_;
goto v___jp_4134_;
}
else
{
size_t v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_usize_of_nat(v___x_4153_);
v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4035_, v___x_4019_, v___x_4156_, v___x_4152_);
v___y_4135_ = v___x_4157_;
goto v___jp_4134_;
}
}
else
{
size_t v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_usize_of_nat(v___x_4153_);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4035_, v___x_4019_, v___x_4158_, v___x_4152_);
v___y_4135_ = v___x_4159_;
goto v___jp_4134_;
}
}
v___jp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4136_ = lean_array_to_list(v___y_4135_);
v___x_4137_ = lean_box(0);
v___x_4138_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4136_, v___x_4137_);
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4140_ = l_Lean_MessageData_joinSep(v___x_4138_, v___x_4139_);
v___x_4141_ = l_Lean_indentD(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4133_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v___x_4031_, v___x_4142_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec_ref(v___x_4143_);
v___y_4120_ = v_a_3999_;
v___y_4121_ = v_a_4000_;
v___y_4122_ = v_a_4001_;
v___y_4123_ = v_a_4002_;
goto v___jp_4119_;
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___x_4035_);
lean_del_object(v___x_4029_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4023_);
lean_dec_ref(v_values_3997_);
lean_dec_ref(v_xs_3996_);
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
v___jp_4036_:
{
lean_object* v___x_4044_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 1, v_recArgInfoss_4005_);
lean_ctor_set(v___x_4029_, 0, v_report_4038_);
v___x_4044_ = v___x_4029_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_report_4038_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_recArgInfoss_4005_);
v___x_4044_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
size_t v_sz_4045_; lean_object* v___x_4046_; 
v_sz_4045_ = lean_array_size(v___y_4037_);
v___x_4046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_xs_3996_, v___x_4035_, v_values_3997_, v_fnNames_3994_, v___y_4037_, v_sz_4045_, v___x_4019_, v___x_4044_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec_ref(v___y_4037_);
lean_dec_ref(v_values_3997_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4063_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4063_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4063_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_fst_4051_; lean_object* v_snd_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4062_; 
v_fst_4051_ = lean_ctor_get(v_a_4047_, 0);
v_snd_4052_ = lean_ctor_get(v_a_4047_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_a_4047_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4054_ = v_a_4047_;
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_snd_4052_);
lean_inc(v_fst_4051_);
lean_dec(v_a_4047_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4062_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v_fst_4051_);
lean_ctor_set(v___x_4054_, 0, v_snd_4052_);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_snd_4052_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_fst_4051_);
v___x_4057_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4057_);
v___x_4059_ = v___x_4049_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4046_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4046_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
v___jp_4073_:
{
lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4079_ = lean_array_get_size(v___y_4074_);
v___x_4080_ = lean_nat_dec_eq(v___x_4079_, v___x_4004_);
if (v___x_4080_ == 0)
{
lean_del_object(v___x_4025_);
v___y_4037_ = v___y_4074_;
v_report_4038_ = v_fst_4023_;
v___y_4039_ = v___y_4075_;
v___y_4040_ = v___y_4076_;
v___y_4041_ = v___y_4077_;
v___y_4042_ = v___y_4078_;
goto v___jp_4036_;
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4026_ == 0)
{
lean_ctor_set_tag(v___x_4025_, 7);
lean_ctor_set(v___x_4025_, 1, v___x_4081_);
v___x_4083_ = v___x_4025_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_fst_4023_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
v___y_4037_ = v___y_4074_;
v_report_4038_ = v___x_4083_;
v___y_4039_ = v___y_4075_;
v___y_4040_ = v___y_4076_;
v___y_4041_ = v___y_4077_;
v___y_4042_ = v___y_4078_;
goto v___jp_4036_;
}
}
}
v___jp_4085_:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4090_, v___y_4088_, v___y_4089_, v___y_4087_, v___y_4086_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v_a_4094_; uint8_t v___x_4095_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref(v___x_4091_);
v___x_4093_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v___x_4031_, v___y_4087_);
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref(v___x_4093_);
v___x_4095_ = lean_unbox(v_a_4094_);
lean_dec(v_a_4094_);
if (v___x_4095_ == 0)
{
v___y_4074_ = v_a_4092_;
v___y_4075_ = v___y_4088_;
v___y_4076_ = v___y_4089_;
v___y_4077_ = v___y_4087_;
v___y_4078_ = v___y_4086_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4096_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4092_);
v___x_4097_ = lean_array_to_list(v_a_4092_);
v___x_4098_ = lean_box(0);
v___x_4099_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v___x_4097_, v___x_4098_);
v___x_4100_ = l_Lean_MessageData_ofList(v___x_4099_);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4096_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v___x_4031_, v___x_4101_, v___y_4088_, v___y_4089_, v___y_4087_, v___y_4086_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec_ref(v___x_4102_);
v___y_4074_ = v_a_4092_;
v___y_4075_ = v___y_4088_;
v___y_4076_ = v___y_4089_;
v___y_4077_ = v___y_4087_;
v___y_4078_ = v___y_4086_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4092_);
lean_dec_ref(v___x_4035_);
lean_del_object(v___x_4029_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4023_);
lean_dec_ref(v_values_3997_);
lean_dec_ref(v_xs_3996_);
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v___x_4035_);
lean_del_object(v___x_4029_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4023_);
lean_dec_ref(v_values_3997_);
lean_dec_ref(v_xs_3996_);
v_a_4111_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4091_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4091_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4119_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4124_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4125_ = lean_array_get_size(v___x_4035_);
v___x_4126_ = lean_nat_dec_lt(v___x_4004_, v___x_4125_);
if (v___x_4126_ == 0)
{
v___y_4086_ = v___y_4123_;
v___y_4087_ = v___y_4122_;
v___y_4088_ = v___y_4120_;
v___y_4089_ = v___y_4121_;
v___y_4090_ = v___x_4124_;
goto v___jp_4085_;
}
else
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_nat_dec_le(v___x_4125_, v___x_4125_);
if (v___x_4127_ == 0)
{
if (v___x_4126_ == 0)
{
v___y_4086_ = v___y_4123_;
v___y_4087_ = v___y_4122_;
v___y_4088_ = v___y_4120_;
v___y_4089_ = v___y_4121_;
v___y_4090_ = v___x_4124_;
goto v___jp_4085_;
}
else
{
size_t v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_usize_of_nat(v___x_4125_);
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4035_, v___x_4019_, v___x_4128_, v___x_4124_);
v___y_4086_ = v___y_4123_;
v___y_4087_ = v___y_4122_;
v___y_4088_ = v___y_4120_;
v___y_4089_ = v___y_4121_;
v___y_4090_ = v___x_4129_;
goto v___jp_4085_;
}
}
else
{
size_t v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_usize_of_nat(v___x_4125_);
v___x_4131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4035_, v___x_4019_, v___x_4130_, v___x_4124_);
v___y_4086_ = v___y_4123_;
v___y_4087_ = v___y_4122_;
v___y_4088_ = v___y_4120_;
v___y_4089_ = v___y_4121_;
v___y_4090_ = v___x_4131_;
goto v___jp_4085_;
}
}
}
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec_ref(v_values_3997_);
lean_dec_ref(v_xs_3996_);
v_a_4163_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4020_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4020_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4171_, lean_object* v_fixedParamPerms_4172_, lean_object* v_xs_4173_, lean_object* v_values_4174_, lean_object* v_termMeasure_x3fs_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4171_, v_fixedParamPerms_4172_, v_xs_4173_, v_values_4174_, v_termMeasure_x3fs_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec_ref(v_fnNames_4171_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_a_4182_, lean_object* v_as_4183_, size_t v_sz_4184_, size_t v_i_4185_, lean_object* v_b_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___redArg(v_a_4182_, v_as_4183_, v_sz_4184_, v_i_4185_, v_b_4186_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_a_4193_, lean_object* v_as_4194_, lean_object* v_sz_4195_, lean_object* v_i_4196_, lean_object* v_b_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
size_t v_sz_boxed_4203_; size_t v_i_boxed_4204_; lean_object* v_res_4205_; 
v_sz_boxed_4203_ = lean_unbox_usize(v_sz_4195_);
lean_dec(v_sz_4195_);
v_i_boxed_4204_ = lean_unbox_usize(v_i_4196_);
lean_dec(v_i_4196_);
v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_a_4193_, v_as_4194_, v_sz_boxed_4203_, v_i_boxed_4204_, v_b_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec_ref(v_as_4194_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4206_, uint8_t v_skipRealize_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; lean_object* v_env_4211_; uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4210_ = lean_st_ref_get(v___y_4208_);
v_env_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc_ref(v_env_4211_);
lean_dec(v___x_4210_);
v___x_4212_ = l_Lean_Environment_contains(v_env_4211_, v_constName_4206_, v_skipRealize_4207_);
v___x_4213_ = lean_box(v___x_4212_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4215_, lean_object* v_skipRealize_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
uint8_t v_skipRealize_boxed_4219_; lean_object* v_res_4220_; 
v_skipRealize_boxed_4219_ = lean_unbox(v_skipRealize_4216_);
v_res_4220_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4215_, v_skipRealize_boxed_4219_, v___y_4217_);
lean_dec(v___y_4217_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4221_, uint8_t v_skipRealize_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4221_, v_skipRealize_4222_, v___y_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4229_, lean_object* v_skipRealize_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
uint8_t v_skipRealize_boxed_4236_; lean_object* v_res_4237_; 
v_skipRealize_boxed_4236_ = lean_unbox(v_skipRealize_4230_);
v_res_4237_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4229_, v_skipRealize_boxed_4236_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Meta_saveState___redArg(v___y_4240_, v___y_4242_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref(v___x_4244_);
lean_inc(v___y_4242_);
lean_inc_ref(v___y_4241_);
lean_inc(v___y_4240_);
lean_inc_ref(v___y_4239_);
v___x_4246_ = lean_apply_5(v_x_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, lean_box(0));
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_dec(v_a_4245_);
return v___x_4246_;
}
else
{
lean_object* v_a_4247_; uint8_t v___y_4249_; uint8_t v___x_4267_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
v___x_4267_ = l_Lean_Exception_isInterrupt(v_a_4247_);
if (v___x_4267_ == 0)
{
uint8_t v___x_4268_; 
lean_inc(v_a_4247_);
v___x_4268_ = l_Lean_Exception_isRuntime(v_a_4247_);
v___y_4249_ = v___x_4268_;
goto v___jp_4248_;
}
else
{
v___y_4249_ = v___x_4267_;
goto v___jp_4248_;
}
v___jp_4248_:
{
if (v___y_4249_ == 0)
{
lean_object* v___x_4250_; 
lean_dec_ref(v___x_4246_);
v___x_4250_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4245_, v___y_4240_, v___y_4242_);
lean_dec(v_a_4245_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4257_ == 0)
{
lean_object* v_unused_4258_; 
v_unused_4258_ = lean_ctor_get(v___x_4250_, 0);
lean_dec(v_unused_4258_);
v___x_4252_ = v___x_4250_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_dec(v___x_4250_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set_tag(v___x_4252_, 1);
lean_ctor_set(v___x_4252_, 0, v_a_4247_);
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4247_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v_a_4247_);
v_a_4259_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4250_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4250_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_dec(v_a_4247_);
lean_dec(v_a_4245_);
return v___x_4246_;
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_x_4238_);
v_a_4269_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4244_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4244_);
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
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4284_, lean_object* v_x_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4292_, lean_object* v_x_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4292_, v_x_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
return v_res_4299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4302_ = l_Lean_stringToMessageData(v___x_4301_);
return v___x_4302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4305_ = l_Lean_stringToMessageData(v___x_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4306_, uint8_t v___x_4307_, lean_object* v_group_4308_, lean_object* v_k_4309_, lean_object* v_comb_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4306_, v___x_4307_, v___y_4314_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; uint8_t v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref(v___x_4316_);
v___x_4318_ = lean_unbox(v_a_4317_);
lean_dec(v_a_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4320_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4308_);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4321_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4323_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v___x_4325_; 
lean_dec_ref(v___x_4324_);
v___x_4325_ = lean_apply_6(v_k_4309_, v_comb_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, lean_box(0));
return v___x_4325_;
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_comb_4310_);
lean_dec_ref(v_k_4309_);
v_a_4326_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4324_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4324_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v___x_4334_; 
lean_dec_ref(v_group_4308_);
v___x_4334_ = lean_apply_6(v_k_4309_, v_comb_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, lean_box(0));
return v___x_4334_;
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_comb_4310_);
lean_dec_ref(v_k_4309_);
lean_dec_ref(v_group_4308_);
v_a_4335_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4316_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4316_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v_group_4345_, lean_object* v_k_4346_, lean_object* v_comb_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
uint8_t v___x_3897__boxed_4353_; lean_object* v_res_4354_; 
v___x_3897__boxed_4353_ = lean_unbox(v___x_4344_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4343_, v___x_3897__boxed_4353_, v_group_4345_, v_k_4346_, v_comb_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
return v_res_4354_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4357_ = l_Lean_stringToMessageData(v___x_4356_);
return v___x_4357_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4));
v___x_4359_ = l_Lean_stringToMessageData(v___x_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4360_, lean_object* v_fnNames_4361_, lean_object* v_xs_4362_, lean_object* v_values_4363_, lean_object* v_as_4364_, size_t v_sz_4365_, size_t v_i_4366_, lean_object* v_b_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
uint8_t v___x_4373_; 
v___x_4373_ = lean_usize_dec_lt(v_i_4366_, v_sz_4365_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; 
lean_dec_ref(v_values_4363_);
lean_dec_ref(v_xs_4362_);
lean_dec_ref(v_k_4360_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_b_4367_);
return v___x_4374_;
}
else
{
lean_object* v_snd_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4445_; 
v_snd_4375_ = lean_ctor_get(v_b_4367_, 1);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_b_4367_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; 
v_unused_4446_ = lean_ctor_get(v_b_4367_, 0);
lean_dec(v_unused_4446_);
v___x_4377_ = v_b_4367_;
v_isShared_4378_ = v_isSharedCheck_4445_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_snd_4375_);
lean_dec(v_b_4367_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4445_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v_a_4379_; lean_object* v_group_4380_; lean_object* v_comb_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4444_; 
v_a_4379_ = lean_array_uget(v_as_4364_, v_i_4366_);
v_group_4380_ = lean_ctor_get(v_a_4379_, 0);
v_comb_4381_ = lean_ctor_get(v_a_4379_, 1);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_a_4379_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4383_ = v_a_4379_;
v_isShared_4384_ = v_isSharedCheck_4444_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_comb_4381_);
lean_inc(v_group_4380_);
lean_dec(v_a_4379_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4444_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v_toIndGroupInfo_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___f_4389_; lean_object* v___x_4390_; 
v_toIndGroupInfo_4385_ = lean_ctor_get(v_group_4380_, 0);
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4387_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4385_, v___x_4386_);
v___x_4388_ = lean_box(v___x_4373_);
lean_inc_ref(v_comb_4381_);
lean_inc_ref(v_k_4360_);
v___f_4389_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4389_, 0, v___x_4387_);
lean_closure_set(v___f_4389_, 1, v___x_4388_);
lean_closure_set(v___f_4389_, 2, v_group_4380_);
lean_closure_set(v___f_4389_, 3, v_k_4360_);
lean_closure_set(v___f_4389_, 4, v_comb_4381_);
v___x_4390_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4389_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4402_; 
lean_del_object(v___x_4383_);
lean_dec_ref(v_comb_4381_);
lean_dec_ref(v_values_4363_);
lean_dec_ref(v_xs_4362_);
lean_dec_ref(v_k_4360_);
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4402_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4402_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4395_, 0, v_a_4391_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 0, v___x_4395_);
v___x_4397_ = v___x_4377_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_snd_4375_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4399_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4397_);
v___x_4399_ = v___x_4393_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
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
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4443_; 
v_a_4403_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4405_ = v___x_4390_;
v_isShared_4406_ = v_isSharedCheck_4443_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4390_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4443_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; uint8_t v___y_4409_; uint8_t v___x_4441_; 
v___x_4407_ = lean_box(0);
v___x_4441_ = l_Lean_Exception_isInterrupt(v_a_4403_);
if (v___x_4441_ == 0)
{
uint8_t v___x_4442_; 
lean_inc(v_a_4403_);
v___x_4442_ = l_Lean_Exception_isRuntime(v_a_4403_);
v___y_4409_ = v___x_4442_;
goto v___jp_4408_;
}
else
{
v___y_4409_ = v___x_4441_;
goto v___jp_4408_;
}
v___jp_4408_:
{
if (v___y_4409_ == 0)
{
lean_object* v___x_4410_; 
lean_del_object(v___x_4405_);
lean_inc_ref(v_values_4363_);
lean_inc_ref(v_xs_4362_);
v___x_4410_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4361_, v_xs_4362_, v_values_4363_, v_comb_4381_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v___x_4412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 7);
lean_ctor_set(v___x_4383_, 1, v_a_4411_);
lean_ctor_set(v___x_4383_, 0, v___x_4412_);
v___x_4414_ = v___x_4383_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4412_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_a_4411_);
v___x_4414_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3);
v___x_4416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4414_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = l_Lean_Exception_toMessageData(v_a_4403_);
v___x_4418_ = l_Lean_indentD(v___x_4417_);
v___x_4419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4416_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_snd_4375_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 1, v___x_4422_);
lean_ctor_set(v___x_4377_, 0, v___x_4407_);
v___x_4424_ = v___x_4377_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
size_t v___x_4425_; size_t v___x_4426_; 
v___x_4425_ = ((size_t)1ULL);
v___x_4426_ = lean_usize_add(v_i_4366_, v___x_4425_);
v_i_4366_ = v___x_4426_;
v_b_4367_ = v___x_4424_;
goto _start;
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4403_);
lean_del_object(v___x_4383_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec_ref(v_values_4363_);
lean_dec_ref(v_xs_4362_);
lean_dec_ref(v_k_4360_);
v_a_4430_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4410_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4410_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v___x_4439_; 
lean_del_object(v___x_4383_);
lean_dec_ref(v_comb_4381_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec_ref(v_values_4363_);
lean_dec_ref(v_xs_4362_);
lean_dec_ref(v_k_4360_);
if (v_isShared_4406_ == 0)
{
v___x_4439_ = v___x_4405_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4403_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4447_, lean_object* v_fnNames_4448_, lean_object* v_xs_4449_, lean_object* v_values_4450_, lean_object* v_as_4451_, lean_object* v_sz_4452_, lean_object* v_i_4453_, lean_object* v_b_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
size_t v_sz_boxed_4460_; size_t v_i_boxed_4461_; lean_object* v_res_4462_; 
v_sz_boxed_4460_ = lean_unbox_usize(v_sz_4452_);
lean_dec(v_sz_4452_);
v_i_boxed_4461_ = lean_unbox_usize(v_i_4453_);
lean_dec(v_i_4453_);
v_res_4462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4447_, v_fnNames_4448_, v_xs_4449_, v_values_4450_, v_as_4451_, v_sz_boxed_4460_, v_i_boxed_4461_, v_b_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec_ref(v_as_4451_);
lean_dec_ref(v_fnNames_4448_);
return v_res_4462_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4464_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4465_ = l_Lean_stringToMessageData(v___x_4464_);
return v___x_4465_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4468_ = l_Lean_stringToMessageData(v___x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4469_, lean_object* v_xs_4470_, lean_object* v_values_4471_, lean_object* v_candidates_4472_, lean_object* v_k_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v_candidates_4479_; lean_object* v_report_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4536_; 
v_candidates_4479_ = lean_ctor_get(v_candidates_4472_, 0);
v_report_4480_ = lean_ctor_get(v_candidates_4472_, 1);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_candidates_4472_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4482_ = v_candidates_4472_;
v_isShared_4483_ = v_isSharedCheck_4536_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_report_4480_);
lean_inc(v_candidates_4479_);
lean_dec(v_candidates_4472_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4536_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = lean_box(0);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4484_);
v___x_4486_ = v___x_4482_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_report_4480_);
v___x_4486_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
size_t v_sz_4487_; size_t v___x_4488_; lean_object* v___x_4489_; 
v_sz_4487_ = lean_array_size(v_candidates_4479_);
v___x_4488_ = ((size_t)0ULL);
v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4473_, v_fnNames_4469_, v_xs_4470_, v_values_4471_, v_candidates_4479_, v_sz_4487_, v___x_4488_, v___x_4486_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
lean_dec_ref(v_candidates_4479_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4526_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4526_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4526_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v_fst_4494_; 
v_fst_4494_ = lean_ctor_get(v_a_4490_, 0);
if (lean_obj_tag(v_fst_4494_) == 0)
{
lean_object* v_snd_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4520_; 
lean_del_object(v___x_4492_);
v_snd_4495_ = lean_ctor_get(v_a_4490_, 1);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_a_4490_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; 
v_unused_4521_ = lean_ctor_get(v_a_4490_, 0);
lean_dec(v_unused_4521_);
v___x_4497_ = v_a_4490_;
v_isShared_4498_ = v_isSharedCheck_4520_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snd_4495_);
lean_dec(v_a_4490_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4520_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v_a_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4500_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v___x_4499_, v_a_4476_);
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
v___x_4502_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 7);
lean_ctor_set(v___x_4497_, 0, v___x_4502_);
v___x_4504_ = v___x_4497_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_snd_4495_);
v___x_4504_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
uint8_t v___x_4505_; 
v___x_4505_ = lean_unbox(v_a_4501_);
lean_dec(v_a_4501_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4504_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4504_);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
lean_ctor_set(v___x_4508_, 1, v___x_4504_);
v___x_4509_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v___x_4499_, v___x_4508_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v___x_4510_; 
lean_dec_ref(v___x_4509_);
v___x_4510_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4504_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4510_;
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v___x_4504_);
v_a_4511_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4509_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4509_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_4522_; lean_object* v___x_4524_; 
lean_inc_ref(v_fst_4494_);
lean_dec(v_a_4490_);
v_val_4522_ = lean_ctor_get(v_fst_4494_, 0);
lean_inc(v_val_4522_);
lean_dec_ref(v_fst_4494_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v_val_4522_);
v___x_4524_ = v___x_4492_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_val_4522_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
v_a_4527_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4489_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4489_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4537_, lean_object* v_xs_4538_, lean_object* v_values_4539_, lean_object* v_candidates_4540_, lean_object* v_k_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4537_, v_xs_4538_, v_values_4539_, v_candidates_4540_, v_k_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec_ref(v_fnNames_4537_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4548_, lean_object* v_fnNames_4549_, lean_object* v_xs_4550_, lean_object* v_values_4551_, lean_object* v_candidates_4552_, lean_object* v_k_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4549_, v_xs_4550_, v_values_4551_, v_candidates_4552_, v_k_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4560_, lean_object* v_fnNames_4561_, lean_object* v_xs_4562_, lean_object* v_values_4563_, lean_object* v_candidates_4564_, lean_object* v_k_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4560_, v_fnNames_4561_, v_xs_4562_, v_values_4563_, v_candidates_4564_, v_k_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec_ref(v_fnNames_4561_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4572_, lean_object* v_k_4573_, lean_object* v_fnNames_4574_, lean_object* v_xs_4575_, lean_object* v_values_4576_, lean_object* v_as_4577_, size_t v_sz_4578_, size_t v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4573_, v_fnNames_4574_, v_xs_4575_, v_values_4576_, v_as_4577_, v_sz_4578_, v_i_4579_, v_b_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4587_, lean_object* v_k_4588_, lean_object* v_fnNames_4589_, lean_object* v_xs_4590_, lean_object* v_values_4591_, lean_object* v_as_4592_, lean_object* v_sz_4593_, lean_object* v_i_4594_, lean_object* v_b_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
size_t v_sz_boxed_4601_; size_t v_i_boxed_4602_; lean_object* v_res_4603_; 
v_sz_boxed_4601_ = lean_unbox_usize(v_sz_4593_);
lean_dec(v_sz_4593_);
v_i_boxed_4602_ = lean_unbox_usize(v_i_4594_);
lean_dec(v_i_4594_);
v_res_4603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4587_, v_k_4588_, v_fnNames_4589_, v_xs_4590_, v_values_4591_, v_as_4592_, v_sz_boxed_4601_, v_i_boxed_4602_, v_b_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec_ref(v_as_4592_);
lean_dec_ref(v_fnNames_4589_);
return v_res_4603_;
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
