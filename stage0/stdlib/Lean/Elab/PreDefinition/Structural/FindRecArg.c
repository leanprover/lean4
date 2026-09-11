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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParam___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParam___closed__0));
v___x_26_ = l_Lean_stringToMessageData(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam(lean_object* v_xs_27_, lean_object* v_i_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_34_; lean_object* v_x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_34_ = l_Lean_instInhabitedExpr;
v_x_35_ = lean_array_get_borrowed(v___x_34_, v_xs_27_, v_i_28_);
v___x_36_ = l_Lean_Expr_fvarId_x21(v_x_35_);
v___x_37_ = l_Lean_FVarId_getUserName___redArg(v___x_36_, v_a_29_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; uint8_t v___x_39_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_37_, 1);
v___x_39_ = l_Lean_Name_hasMacroScopes(v_a_38_);
lean_dec(v_a_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc(v_x_35_);
v___x_40_ = l_Lean_MessageData_ofExpr(v_x_35_);
v___x_41_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_40_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_42_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParam___closed__1, &l_Lean_Elab_Structural_prettyParam___closed__1_once, _init_l_Lean_Elab_Structural_prettyParam___closed__1);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_add(v_i_28_, v___x_43_);
v___x_45_ = l_Nat_reprFast(v___x_44_);
v___x_46_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
v___x_48_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_42_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_48_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
return v___x_49_;
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v_a_50_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_37_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_37_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParam___boxed(lean_object* v_xs_58_, lean_object* v_i_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Elab_Structural_prettyParam(v_xs_58_, v_i_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_i_59_);
lean_dec_ref(v_xs_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object* v_k_66_, lean_object* v_b_67_, lean_object* v_c_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
v___x_74_ = lean_apply_7(v_k_66_, v_b_67_, v_c_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object* v_k_75_, lean_object* v_b_76_, lean_object* v_c_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_75_, v_b_76_, v_c_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(lean_object* v_e_84_, lean_object* v_k_85_, uint8_t v_cleanupAnnotations_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___f_92_; uint8_t v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___f_92_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_92_, 0, v_k_85_);
v___x_93_ = 1;
v___x_94_ = 0;
v___x_95_ = lean_box(0);
v___x_96_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_84_, v___x_93_, v___x_94_, v___x_93_, v___x_94_, v___x_95_, v___f_92_, v_cleanupAnnotations_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_96_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_96_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(lean_object* v_e_113_, lean_object* v_k_114_, lean_object* v_cleanupAnnotations_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_121_; lean_object* v_res_122_; 
v_cleanupAnnotations_boxed_121_ = lean_unbox(v_cleanupAnnotations_115_);
v_res_122_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_113_, v_k_114_, v_cleanupAnnotations_boxed_121_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(lean_object* v_00_u03b1_123_, lean_object* v_e_124_, lean_object* v_k_125_, uint8_t v_cleanupAnnotations_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_e_124_, v_k_125_, v_cleanupAnnotations_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(lean_object* v_00_u03b1_133_, lean_object* v_e_134_, lean_object* v_k_135_, lean_object* v_cleanupAnnotations_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_142_; lean_object* v_res_143_; 
v_cleanupAnnotations_boxed_142_ = lean_unbox(v_cleanupAnnotations_136_);
v_res_143_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(v_00_u03b1_133_, v_e_134_, v_k_135_, v_cleanupAnnotations_boxed_142_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0(lean_object* v_recArgInfo_144_, lean_object* v_xs_145_, lean_object* v_ys_146_, lean_object* v_x_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_fixedParamPerm_153_; lean_object* v_recArgPos_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_fixedParamPerm_153_ = lean_ctor_get(v_recArgInfo_144_, 1);
lean_inc_ref(v_fixedParamPerm_153_);
v_recArgPos_154_ = lean_ctor_get(v_recArgInfo_144_, 2);
lean_inc(v_recArgPos_154_);
lean_dec_ref(v_recArgInfo_144_);
v___x_155_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_153_, v_xs_145_, v_ys_146_);
v___x_156_ = l_Lean_Elab_Structural_prettyParam(v___x_155_, v_recArgPos_154_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v_recArgPos_154_);
lean_dec_ref(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(lean_object* v_recArgInfo_157_, lean_object* v_xs_158_, lean_object* v_ys_159_, lean_object* v_x_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(v_recArgInfo_157_, v_xs_158_, v_ys_159_, v_x_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v_x_160_);
lean_dec_ref(v_xs_158_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg(lean_object* v_xs_167_, lean_object* v_value_168_, lean_object* v_recArgInfo_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___f_175_; uint8_t v___x_176_; lean_object* v___x_177_; 
v___f_175_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_175_, 0, v_recArgInfo_169_);
lean_closure_set(v___f_175_, 1, v_xs_167_);
v___x_176_ = 0;
v___x_177_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_168_, v___f_175_, v___x_176_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyRecArg___boxed(lean_object* v_xs_178_, lean_object* v_value_179_, lean_object* v_recArgInfo_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_178_, v_value_179_, v_recArgInfo_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(lean_object* v_xs_190_, lean_object* v_as_191_, size_t v_sz_192_, size_t v_i_193_, lean_object* v_b_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_usize_dec_lt(v_i_193_, v_sz_192_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec_ref(v_xs_190_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_b_194_);
return v___x_201_;
}
else
{
lean_object* v_snd_202_; lean_object* v_snd_203_; lean_object* v_fst_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_286_; 
v_snd_202_ = lean_ctor_get(v_b_194_, 1);
lean_inc(v_snd_202_);
v_snd_203_ = lean_ctor_get(v_snd_202_, 1);
lean_inc(v_snd_203_);
v_fst_204_ = lean_ctor_get(v_b_194_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_b_194_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_b_194_, 1);
lean_dec(v_unused_287_);
v___x_206_ = v_b_194_;
v_isShared_207_ = v_isSharedCheck_286_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_fst_204_);
lean_dec(v_b_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_286_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_fst_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_284_; 
v_fst_208_ = lean_ctor_get(v_snd_202_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_snd_202_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_snd_202_, 1);
lean_dec(v_unused_285_);
v___x_210_ = v_snd_202_;
v_isShared_211_ = v_isSharedCheck_284_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_fst_208_);
lean_dec(v_snd_202_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_284_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_array_212_; lean_object* v_start_213_; lean_object* v_stop_214_; uint8_t v___x_215_; 
v_array_212_ = lean_ctor_get(v_snd_203_, 0);
v_start_213_ = lean_ctor_get(v_snd_203_, 1);
v_stop_214_ = lean_ctor_get(v_snd_203_, 2);
v___x_215_ = lean_nat_dec_lt(v_start_213_, v_stop_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_xs_190_);
if (v_isShared_211_ == 0)
{
v___x_217_ = v___x_210_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_snd_203_);
v___x_217_ = v_reuseFailAlloc_222_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_217_);
v___x_219_ = v___x_206_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_221_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
else
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_280_; 
lean_inc(v_stop_214_);
lean_inc(v_start_213_);
lean_inc_ref(v_array_212_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_snd_203_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_snd_203_, 2);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_snd_203_, 1);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_snd_203_, 0);
lean_dec(v_unused_283_);
v___x_224_ = v_snd_203_;
v_isShared_225_ = v_isSharedCheck_280_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_snd_203_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_280_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_array_226_; lean_object* v_start_227_; lean_object* v_stop_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_array_226_ = lean_ctor_get(v_fst_208_, 0);
v_start_227_ = lean_ctor_get(v_fst_208_, 1);
v_stop_228_ = lean_ctor_get(v_fst_208_, 2);
v___x_229_ = lean_array_fget(v_array_212_, v_start_213_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_add(v_start_213_, v___x_230_);
lean_dec(v_start_213_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_231_);
v___x_233_ = v___x_224_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_array_212_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_stop_214_);
v___x_233_ = v_reuseFailAlloc_279_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_nat_dec_lt(v_start_227_, v_stop_228_);
if (v___x_234_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v___x_229_);
lean_dec_ref(v_xs_190_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_233_);
v___x_236_ = v___x_210_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_233_);
v___x_236_ = v_reuseFailAlloc_241_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_236_);
v___x_238_ = v___x_206_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
else
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_275_; 
lean_inc(v_stop_228_);
lean_inc(v_start_227_);
lean_inc_ref(v_array_226_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_fst_208_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_276_ = lean_ctor_get(v_fst_208_, 2);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_fst_208_, 1);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_fst_208_, 0);
lean_dec(v_unused_278_);
v___x_243_ = v_fst_208_;
v_isShared_244_ = v_isSharedCheck_275_;
goto v_resetjp_242_;
}
else
{
lean_dec(v_fst_208_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_275_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_array_fget_borrowed(v_array_226_, v_start_227_);
lean_inc(v___x_245_);
lean_inc_ref(v_xs_190_);
v___x_246_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_190_, v___x_245_, v___x_229_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v_a_248_ = lean_array_uget_borrowed(v_as_191_, v_i_193_);
v___x_249_ = lean_nat_add(v_start_227_, v___x_230_);
lean_dec(v_start_227_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_249_);
v___x_251_ = v___x_243_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_array_226_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_stop_228_);
v___x_251_ = v_reuseFailAlloc_266_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v_a_247_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_inc(v_a_248_);
v___x_254_ = l_Lean_MessageData_ofName(v_a_248_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_array_push(v_fst_204_, v___x_255_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_233_);
lean_ctor_set(v___x_210_, 0, v___x_251_);
v___x_258_ = v___x_210_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_233_);
v___x_258_ = v_reuseFailAlloc_265_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_258_);
lean_ctor_set(v___x_206_, 0, v___x_256_);
v___x_260_ = v___x_206_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
size_t v___x_261_; size_t v___x_262_; 
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_193_, v___x_261_);
v_i_193_ = v___x_262_;
v_b_194_ = v___x_260_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_del_object(v___x_243_);
lean_dec_ref(v___x_233_);
lean_dec(v_stop_228_);
lean_dec(v_start_227_);
lean_dec_ref(v_array_226_);
lean_del_object(v___x_210_);
lean_del_object(v___x_206_);
lean_dec(v_fst_204_);
lean_dec_ref(v_xs_190_);
v_a_267_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_246_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_246_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(lean_object* v_xs_288_, lean_object* v_as_289_, lean_object* v_sz_290_, lean_object* v_i_291_, lean_object* v_b_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
size_t v_sz_boxed_298_; size_t v_i_boxed_299_; lean_object* v_res_300_; 
v_sz_boxed_298_ = lean_unbox_usize(v_sz_290_);
lean_dec(v_sz_290_);
v_i_boxed_299_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_288_, v_as_289_, v_sz_boxed_298_, v_i_boxed_299_, v_b_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec_ref(v_as_289_);
return v_res_300_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__1));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__3));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet(lean_object* v_fnNames_309_, lean_object* v_xs_310_, lean_object* v_values_311_, lean_object* v_recArgInfos_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_array_get_size(v_fnNames_309_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v_l_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v_l_322_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_323_ = lean_array_get_size(v_values_311_);
v___x_324_ = l_Array_toSubarray___redArg(v_values_311_, v___x_321_, v___x_323_);
v___x_325_ = lean_array_get_size(v_recArgInfos_312_);
v___x_326_ = l_Array_toSubarray___redArg(v_recArgInfos_312_, v___x_321_, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_324_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_l_322_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v_sz_329_ = lean_array_size(v_fnNames_309_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_310_, v_fnNames_309_, v_sz_329_, v___x_330_, v___x_328_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_351_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_fst_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_349_; 
v_fst_336_ = lean_ctor_get(v_a_332_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_a_332_, 1);
lean_dec(v_unused_350_);
v___x_338_ = v_a_332_;
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_fst_336_);
lean_dec(v_a_332_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_340_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__2, &l_Lean_Elab_Structural_prettyParameterSet___closed__2_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2);
v___x_341_ = lean_array_to_list(v_fst_336_);
v___x_342_ = l_Lean_MessageData_andList(v___x_341_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 7);
lean_ctor_set(v___x_338_, 1, v___x_342_);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_344_);
v___x_346_ = v___x_334_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_331_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_360_ = l_Lean_instInhabitedExpr;
v___x_361_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_array_get(v___x_360_, v_values_311_, v___x_362_);
lean_dec_ref(v_values_311_);
v___x_364_ = lean_array_get(v___x_361_, v_recArgInfos_312_, v___x_362_);
lean_dec_ref(v_recArgInfos_312_);
v___x_365_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_310_, v___x_363_, v___x_364_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_obj_once(&l_Lean_Elab_Structural_prettyParameterSet___closed__4, &l_Lean_Elab_Structural_prettyParameterSet___closed__4_once, _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_prettyParameterSet___boxed(lean_object* v_fnNames_376_, lean_object* v_xs_377_, lean_object* v_values_378_, lean_object* v_recArgInfos_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_376_, v_xs_377_, v_values_378_, v_recArgInfos_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec_ref(v_fnNames_376_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(lean_object* v_xs_386_, lean_object* v_v_387_, lean_object* v_i_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v_xs_386_);
v___x_390_ = lean_nat_dec_lt(v_i_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v_i_388_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_array_fget_borrowed(v_xs_386_, v_i_388_);
v___x_393_ = lean_expr_eqv(v___x_392_, v_v_387_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_i_388_, v___x_394_);
lean_dec(v_i_388_);
v_i_388_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_i_388_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_398_, lean_object* v_v_399_, lean_object* v_i_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_398_, v_v_399_, v_i_400_);
lean_dec_ref(v_v_399_);
lean_dec_ref(v_xs_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(lean_object* v_xs_402_, lean_object* v_v_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_402_, v_v_403_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(lean_object* v_xs_406_, lean_object* v_v_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_406_, v_v_407_);
lean_dec_ref(v_v_407_);
lean_dec_ref(v_xs_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(lean_object* v_xs_409_, lean_object* v_v_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_409_, v_v_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
return v___x_412_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_val_413_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_val_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(lean_object* v_xs_421_, lean_object* v_v_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_421_, v_v_422_);
lean_dec_ref(v_v_422_);
lean_dec_ref(v_xs_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(lean_object* v_xs_424_, lean_object* v_as_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_b_428_){
_start:
{
lean_object* v_a_430_; uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_434_ == 0)
{
return v_b_428_;
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_array_uget_borrowed(v_as_425_, v_i_427_);
v___x_436_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_424_, v_a_435_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; uint8_t v___x_438_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = lean_nat_dec_lt(v_val_437_, v_b_428_);
if (v___x_438_ == 0)
{
lean_dec(v_val_437_);
v_a_430_ = v_b_428_;
goto v___jp_429_;
}
else
{
lean_dec(v_b_428_);
v_a_430_ = v_val_437_;
goto v___jp_429_;
}
}
else
{
lean_dec(v___x_436_);
v_a_430_ = v_b_428_;
goto v___jp_429_;
}
}
v___jp_429_:
{
size_t v___x_431_; size_t v___x_432_; 
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_427_, v___x_431_);
v_i_427_ = v___x_432_;
v_b_428_ = v_a_430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(lean_object* v_xs_439_, lean_object* v_as_440_, lean_object* v_sz_441_, lean_object* v_i_442_, lean_object* v_b_443_){
_start:
{
size_t v_sz_boxed_444_; size_t v_i_boxed_445_; lean_object* v_res_446_; 
v_sz_boxed_444_ = lean_unbox_usize(v_sz_441_);
lean_dec(v_sz_441_);
v_i_boxed_445_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_439_, v_as_440_, v_sz_boxed_444_, v_i_boxed_445_, v_b_443_);
lean_dec_ref(v_as_440_);
lean_dec_ref(v_xs_439_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(lean_object* v_xs_447_, lean_object* v_indices_448_){
_start:
{
lean_object* v_minPos_449_; size_t v_sz_450_; size_t v___x_451_; lean_object* v___x_452_; 
v_minPos_449_ = lean_array_get_size(v_xs_447_);
v_sz_450_ = lean_array_size(v_indices_448_);
v___x_451_ = ((size_t)0ULL);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_447_, v_indices_448_, v_sz_450_, v___x_451_, v_minPos_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* v_xs_453_, lean_object* v_indices_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_453_, v_indices_454_);
lean_dec_ref(v_indices_454_);
lean_dec_ref(v_xs_453_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(lean_object* v_x_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_458_);
lean_dec(v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(lean_object* v_fvarId_461_, lean_object* v_x_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = l_Lean_instBEqFVarId_beq(v_fvarId_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_fvarId_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_box(0);
v___x_470_ = lean_unsigned_to_nat(16u);
v___x_471_ = lean_mk_array(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(lean_object* v_e_475_, lean_object* v_fvarId_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; uint8_t v_fst_481_; lean_object* v_mctx_482_; lean_object* v___y_500_; lean_object* v_mctx_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_mctx_505_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref_n(v_mctx_505_, 2);
lean_dec(v___x_479_);
v___f_506_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_507_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_507_, 0, v_fvarId_476_);
v___x_508_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_mctx_505_);
v___x_510_ = l_Lean_Expr_hasFVar(v_e_475_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_Expr_hasMVar(v_e_475_);
if (v___x_511_ == 0)
{
lean_dec_ref_known(v___x_509_, 2);
lean_dec_ref(v___f_507_);
lean_dec_ref(v_e_475_);
v_fst_481_ = v___x_511_;
v_mctx_482_ = v_mctx_505_;
goto v___jp_480_;
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_mctx_505_);
v___x_512_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_507_, v___f_506_, v_e_475_, v___x_509_);
v___y_500_ = v___x_512_;
goto v___jp_499_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_mctx_505_);
v___x_513_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_507_, v___f_506_, v_e_475_, v___x_509_);
v___y_500_ = v___x_513_;
goto v___jp_499_;
}
v___jp_480_:
{
lean_object* v___x_483_; lean_object* v_cache_484_; lean_object* v_zetaDeltaFVarIds_485_; lean_object* v_postponed_486_; lean_object* v_diag_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_497_; 
v___x_483_ = lean_st_ref_take(v___y_477_);
v_cache_484_ = lean_ctor_get(v___x_483_, 1);
v_zetaDeltaFVarIds_485_ = lean_ctor_get(v___x_483_, 2);
v_postponed_486_ = lean_ctor_get(v___x_483_, 3);
v_diag_487_ = lean_ctor_get(v___x_483_, 4);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_483_, 0);
lean_dec(v_unused_498_);
v___x_489_ = v___x_483_;
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_diag_487_);
lean_inc(v_postponed_486_);
lean_inc(v_zetaDeltaFVarIds_485_);
lean_inc(v_cache_484_);
lean_dec(v___x_483_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_497_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v_mctx_482_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_mctx_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_cache_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_zetaDeltaFVarIds_485_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_postponed_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_diag_487_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_put(v___y_477_, v___x_492_);
v___x_494_ = lean_box(v_fst_481_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
v___jp_499_:
{
lean_object* v_snd_501_; lean_object* v_fst_502_; lean_object* v_mctx_503_; uint8_t v___x_504_; 
v_snd_501_ = lean_ctor_get(v___y_500_, 1);
lean_inc(v_snd_501_);
v_fst_502_ = lean_ctor_get(v___y_500_, 0);
lean_inc(v_fst_502_);
lean_dec_ref(v___y_500_);
v_mctx_503_ = lean_ctor_get(v_snd_501_, 1);
lean_inc_ref(v_mctx_503_);
lean_dec(v_snd_501_);
v___x_504_ = lean_unbox(v_fst_502_);
lean_dec(v_fst_502_);
v_fst_481_ = v___x_504_;
v_mctx_482_ = v_mctx_503_;
goto v___jp_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(lean_object* v_e_514_, lean_object* v_fvarId_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_514_, v_fvarId_515_, v___y_516_);
lean_dec(v___y_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(lean_object* v_e_519_, lean_object* v_fvarId_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_519_, v_fvarId_520_, v___y_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(lean_object* v_e_527_, lean_object* v_fvarId_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_527_, v_fvarId_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(lean_object* v_a_535_, lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_541_ = lean_expr_eqv(v_a_535_, v___x_540_);
if (v___x_541_ == 0)
{
size_t v___x_542_; size_t v___x_543_; 
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_537_, v___x_542_);
v_i_537_ = v___x_543_;
goto _start;
}
else
{
return v___x_541_;
}
}
else
{
uint8_t v___x_545_; 
v___x_545_ = 0;
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(lean_object* v_a_546_, lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_stop_549_){
_start:
{
size_t v_i_boxed_550_; size_t v_stop_boxed_551_; uint8_t v_res_552_; lean_object* v_r_553_; 
v_i_boxed_550_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_stop_boxed_551_ = lean_unbox_usize(v_stop_549_);
lean_dec(v_stop_549_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_546_, v_as_547_, v_i_boxed_550_, v_stop_boxed_551_);
lean_dec_ref(v_as_547_);
lean_dec_ref(v_a_546_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(lean_object* v_as_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_array_get_size(v_as_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
return v___x_558_;
}
else
{
if (v___x_558_ == 0)
{
return v___x_558_;
}
else
{
size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_557_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_555_, v_as_554_, v___x_559_, v___x_560_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(lean_object* v_as_562_, lean_object* v_a_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_562_, v_a_563_);
lean_dec_ref(v_a_563_);
lean_dec_ref(v_as_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(lean_object* v_a_569_, lean_object* v_indices_570_, lean_object* v_a_571_, lean_object* v_as_572_, size_t v_sz_573_, size_t v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_usize_dec_lt(v_i_574_, v_sz_573_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_a_571_);
lean_dec_ref(v_a_569_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_b_575_);
return v___x_582_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_b_575_);
v_a_583_ = lean_array_uget_borrowed(v_as_572_, v_i_574_);
v___x_584_ = l_Lean_Expr_fvarId_x21(v_a_583_);
lean_inc_ref(v_a_569_);
v___x_585_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_569_, v___x_584_, v___y_577_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_606_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_606_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_606_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_606_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_a_591_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_597_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_570_, v_a_583_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_598_ == 0)
{
lean_del_object(v___x_588_);
v_a_591_ = v___x_596_;
goto v___jp_590_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref(v_a_569_);
lean_inc(v_a_583_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_571_);
lean_ctor_set(v___x_599_, 1, v_a_583_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_595_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_602_);
v___x_604_ = v___x_588_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_del_object(v___x_588_);
lean_dec(v_a_586_);
v_a_591_ = v___x_596_;
goto v___jp_590_;
}
v___jp_590_:
{
size_t v___x_592_; size_t v___x_593_; 
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_574_, v___x_592_);
lean_inc_ref(v_a_591_);
v_i_574_ = v___x_593_;
v_b_575_ = v_a_591_;
goto _start;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_a_571_);
lean_dec_ref(v_a_569_);
v_a_607_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_585_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_585_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(lean_object* v_a_615_, lean_object* v_indices_616_, lean_object* v_a_617_, lean_object* v_as_618_, lean_object* v_sz_619_, lean_object* v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
size_t v_sz_boxed_627_; size_t v_i_boxed_628_; lean_object* v_res_629_; 
v_sz_boxed_627_ = lean_unbox_usize(v_sz_619_);
lean_dec(v_sz_619_);
v_i_boxed_628_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_615_, v_indices_616_, v_a_617_, v_as_618_, v_sz_boxed_627_, v_i_boxed_628_, v_b_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v_as_618_);
lean_dec_ref(v_indices_616_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(lean_object* v_ys_630_, lean_object* v_indices_631_, lean_object* v_as_632_, size_t v_sz_633_, size_t v_i_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_lt(v_i_634_, v_sz_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_b_635_);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_644_; 
lean_dec_ref(v_b_635_);
v_a_643_ = lean_array_uget_borrowed(v_as_632_, v_i_634_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v_a_643_);
v___x_644_ = lean_infer_type(v_a_643_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_648_ = lean_array_size(v_ys_630_);
v___x_649_ = ((size_t)0ULL);
lean_inc(v_a_643_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_645_, v_indices_631_, v_a_643_, v_ys_630_, v_sz_648_, v___x_649_, v___x_647_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_670_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_670_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_670_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_670_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_668_; 
v_fst_655_ = lean_ctor_get(v_a_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_a_651_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_a_651_, 1);
lean_dec(v_unused_669_);
v___x_657_ = v_a_651_;
v_isShared_658_ = v_isSharedCheck_668_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_fst_655_);
lean_dec(v_a_651_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_668_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
if (lean_obj_tag(v_fst_655_) == 0)
{
size_t v___x_659_; size_t v___x_660_; 
lean_del_object(v___x_657_);
lean_del_object(v___x_653_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_634_, v___x_659_);
v_i_634_ = v___x_660_;
v_b_635_ = v___x_647_;
goto _start;
}
else
{
lean_object* v___x_663_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_646_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_646_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_663_);
v___x_665_ = v___x_653_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
else
{
return v___x_650_;
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_a_671_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_644_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_644_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(lean_object* v_ys_679_, lean_object* v_indices_680_, lean_object* v_as_681_, lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_sz_boxed_690_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_691_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_679_, v_indices_680_, v_as_681_, v_sz_boxed_690_, v_i_boxed_691_, v_b_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_as_681_);
lean_dec_ref(v_indices_680_);
lean_dec_ref(v_ys_679_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(lean_object* v_indices_693_, lean_object* v_ys_694_, lean_object* v_as_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_b_698_);
return v___x_705_;
}
else
{
lean_object* v_a_706_; lean_object* v___x_707_; 
lean_dec_ref(v_b_698_);
v_a_706_ = lean_array_uget_borrowed(v_as_695_, v_i_697_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v_a_706_);
v___x_707_ = lean_infer_type(v_a_706_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; size_t v_sz_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_box(0);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_711_ = lean_array_size(v_ys_694_);
v___x_712_ = ((size_t)0ULL);
lean_inc(v_a_706_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_708_, v_indices_693_, v_a_706_, v_ys_694_, v_sz_711_, v___x_712_, v___x_710_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_733_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_733_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_733_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_733_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_fst_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_731_; 
v_fst_718_ = lean_ctor_get(v_a_714_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_a_714_, 1);
lean_dec(v_unused_732_);
v___x_720_ = v_a_714_;
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_fst_718_);
lean_dec(v_a_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_731_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
if (lean_obj_tag(v_fst_718_) == 0)
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
lean_del_object(v___x_720_);
lean_del_object(v___x_716_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_697_, v___x_722_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_694_, v_indices_693_, v_as_695_, v_sz_696_, v___x_723_, v___x_710_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_724_;
}
else
{
lean_object* v___x_726_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_709_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_709_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_726_);
v___x_728_ = v___x_716_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
return v___x_713_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_707_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_707_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(lean_object* v_indices_742_, lean_object* v_ys_743_, lean_object* v_as_744_, lean_object* v_sz_745_, lean_object* v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_745_);
lean_dec(v_sz_745_);
v_i_boxed_754_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_742_, v_ys_743_, v_as_744_, v_sz_boxed_753_, v_i_boxed_754_, v_b_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec_ref(v_as_744_);
lean_dec_ref(v_ys_743_);
lean_dec_ref(v_indices_742_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* v_ys_756_, lean_object* v_indices_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; size_t v_sz_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_763_ = lean_box(0);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_765_ = lean_array_size(v_indices_757_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_757_, v_ys_756_, v_indices_757_, v_sz_765_, v___x_766_, v___x_764_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_780_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_fst_772_; 
v_fst_772_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_fst_772_);
lean_dec(v_a_768_);
if (lean_obj_tag(v_fst_772_) == 0)
{
lean_object* v___x_774_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_763_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_763_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
else
{
lean_object* v_val_776_; lean_object* v___x_778_; 
v_val_776_ = lean_ctor_get(v_fst_772_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_fst_772_, 1);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_val_776_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_val_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_767_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_767_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* v_ys_789_, lean_object* v_indices_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_789_, v_indices_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_indices_790_);
lean_dec_ref(v_ys_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(lean_object* v_a_797_, lean_object* v_as_798_, size_t v_sz_799_, size_t v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v_a_797_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_b_801_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_b_801_);
v_a_806_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
v___x_807_ = l_Lean_Expr_fvarId_x21(v_a_806_);
lean_inc_ref(v_a_797_);
v___x_808_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_797_, v___x_807_, v___y_802_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_826_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_826_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_826_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_826_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; 
lean_del_object(v___x_811_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_800_, v___x_816_);
v_i_800_ = v___x_817_;
v_b_801_ = v___x_815_;
goto _start;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_inc(v_a_806_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_a_797_);
lean_ctor_set(v___x_819_, 1, v_a_806_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_813_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_822_);
v___x_824_ = v___x_811_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_a_797_);
v_a_827_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_808_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_808_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(lean_object* v_a_835_, lean_object* v_as_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
size_t v_sz_boxed_842_; size_t v_i_boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_842_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_843_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_835_, v_as_836_, v_sz_boxed_842_, v_i_boxed_843_, v_b_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v_as_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(lean_object* v_ys_845_, lean_object* v_as_846_, size_t v_sz_847_, size_t v_i_848_, lean_object* v_b_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_848_, v_sz_847_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_849_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_a_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v_b_849_);
v___x_857_ = lean_box(0);
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_859_ = lean_array_uget_borrowed(v_as_846_, v_i_848_);
v_sz_860_ = lean_array_size(v_ys_845_);
v___x_861_ = ((size_t)0ULL);
lean_inc(v_a_859_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_859_, v_ys_845_, v_sz_860_, v___x_861_, v___x_858_, v___y_851_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_882_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_882_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_fst_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_880_; 
v_fst_867_ = lean_ctor_get(v_a_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v_a_863_, 1);
lean_dec(v_unused_881_);
v___x_869_ = v_a_863_;
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_fst_867_);
lean_dec(v_a_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_fst_867_) == 0)
{
size_t v___x_871_; size_t v___x_872_; 
lean_del_object(v___x_869_);
lean_del_object(v___x_865_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_848_, v___x_871_);
v_i_848_ = v___x_872_;
v_b_849_ = v___x_858_;
goto _start;
}
else
{
lean_object* v___x_875_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_857_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_857_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_875_);
v___x_877_ = v___x_865_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
else
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(lean_object* v_ys_883_, lean_object* v_as_884_, lean_object* v_sz_885_, lean_object* v_i_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
size_t v_sz_boxed_893_; size_t v_i_boxed_894_; lean_object* v_res_895_; 
v_sz_boxed_893_ = lean_unbox_usize(v_sz_885_);
lean_dec(v_sz_885_);
v_i_boxed_894_ = lean_unbox_usize(v_i_886_);
lean_dec(v_i_886_);
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_883_, v_as_884_, v_sz_boxed_893_, v_i_boxed_894_, v_b_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v_as_884_);
lean_dec_ref(v_ys_883_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* v_ys_896_, lean_object* v_indParams_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; size_t v_sz_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___x_903_ = lean_box(0);
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_sz_905_ = lean_array_size(v_indParams_897_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_896_, v_indParams_897_, v_sz_905_, v___x_906_, v___x_904_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_920_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_fst_912_; 
v_fst_912_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v_fst_912_);
lean_dec(v_a_908_);
if (lean_obj_tag(v_fst_912_) == 0)
{
lean_object* v___x_914_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_903_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_903_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v_val_916_; lean_object* v___x_918_; 
v_val_916_ = lean_ctor_get(v_fst_912_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_fst_912_, 1);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_val_916_);
v___x_918_ = v___x_910_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_val_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_907_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_907_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* v_ys_929_, lean_object* v_indParams_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_929_, v_indParams_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_indParams_930_);
lean_dec_ref(v_ys_929_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(lean_object* v_a_937_, lean_object* v_as_938_, size_t v_sz_939_, size_t v_i_940_, lean_object* v_b_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_937_, v_as_938_, v_sz_939_, v_i_940_, v_b_941_, v___y_943_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(lean_object* v_a_948_, lean_object* v_as_949_, lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_959_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_948_, v_as_949_, v_sz_boxed_958_, v_i_boxed_959_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(lean_object* v_msg_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_panic_fn_borrowed(v___x_962_, v_msg_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___f_971_; lean_object* v___x_4715__overap_972_; lean_object* v___x_973_; 
v___f_971_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4715__overap_972_ = lean_panic_fn_borrowed(v___f_971_, v_msg_965_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
v___x_973_ = lean_apply_5(v___x_4715__overap_972_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_985_ = lean_unsigned_to_nat(107u);
v___x_986_ = lean_unsigned_to_nat(97u);
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_989_ = l_mkPanicMessageWithDecl(v___x_988_, v___x_987_, v___x_986_, v___x_985_, v___x_984_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_xs_990_, size_t v_sz_991_, size_t v_i_992_, lean_object* v_bs_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = lean_usize_dec_lt(v_i_992_, v_sz_991_);
if (v___x_994_ == 0)
{
return v_bs_993_;
}
else
{
lean_object* v_v_995_; lean_object* v___x_996_; lean_object* v_bs_x27_997_; lean_object* v___y_999_; lean_object* v___x_1004_; 
v_v_995_ = lean_array_uget(v_bs_993_, v_i_992_);
v___x_996_ = lean_unsigned_to_nat(0u);
v_bs_x27_997_ = lean_array_uset(v_bs_993_, v_i_992_, v___x_996_);
v___x_1004_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_990_, v_v_995_);
lean_dec(v_v_995_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3);
v___x_1006_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1005_);
v___y_999_ = v___x_1006_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1007_; 
v_val_1007_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___x_1004_, 1);
v___y_999_ = v_val_1007_;
goto v___jp_998_;
}
v___jp_998_:
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_992_, v___x_1000_);
v___x_1002_ = lean_array_uset(v_bs_x27_997_, v_i_992_, v___y_999_);
v_i_992_ = v___x_1001_;
v_bs_993_ = v___x_1002_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_xs_1008_, lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_bs_1011_){
_start:
{
size_t v_sz_boxed_1012_; size_t v_i_boxed_1013_; lean_object* v_res_1014_; 
v_sz_boxed_1012_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1013_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1008_, v_sz_boxed_1012_, v_i_boxed_1013_, v_bs_1011_);
lean_dec_ref(v_xs_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_ref_1021_; lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_ref_1021_ = lean_ctor_get(v___y_1018_, 2);
v___x_1022_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_inc(v_ref_1021_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_ref_1021_);
lean_ctor_set(v___x_1027_, 1, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(lean_object* v_xs_1039_, lean_object* v_v_1040_, lean_object* v_i_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_array_get_size(v_xs_1039_);
v___x_1043_ = lean_nat_dec_lt(v_i_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec(v_i_1041_);
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_array_fget_borrowed(v_xs_1039_, v_i_1041_);
v___x_1046_ = lean_name_eq(v___x_1045_, v_v_1040_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_i_1041_, v___x_1047_);
lean_dec(v_i_1041_);
v_i_1041_ = v___x_1048_;
goto _start;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_i_1041_);
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7___boxed(lean_object* v_xs_1051_, lean_object* v_v_1052_, lean_object* v_i_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1051_, v_v_1052_, v_i_1053_);
lean_dec(v_v_1052_);
lean_dec_ref(v_xs_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(lean_object* v_xs_1055_, lean_object* v_v_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1055_, v_v_1056_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5___boxed(lean_object* v_xs_1059_, lean_object* v_v_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1059_, v_v_1060_);
lean_dec(v_v_1060_);
lean_dec_ref(v_xs_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1062_, lean_object* v_v_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1062_, v_v_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
else
{
lean_object* v_val_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_val_1066_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1064_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_val_1066_);
lean_dec(v___x_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_val_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1074_, lean_object* v_v_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1074_, v_v_1075_);
lean_dec(v_v_1075_);
lean_dec_ref(v_xs_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_i_1077_, lean_object* v___x_1078_, lean_object* v_as_1079_, size_t v_i_1080_, size_t v_stop_1081_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_usize_dec_eq(v_i_1080_, v_stop_1081_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_array_uget_borrowed(v_as_1079_, v_i_1080_);
v___x_1088_ = l_Lean_Expr_isFVar(v___x_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_nat_dec_lt(v_i_1077_, v___x_1078_);
if (v___x_1089_ == 0)
{
goto v___jp_1082_;
}
else
{
return v___x_1089_;
}
}
else
{
goto v___jp_1082_;
}
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = 0;
return v___x_1090_;
}
v___jp_1082_:
{
size_t v___x_1083_; size_t v___x_1084_; 
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1080_, v___x_1083_);
v_i_1080_ = v___x_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_i_1091_, lean_object* v___x_1092_, lean_object* v_as_1093_, lean_object* v_i_1094_, lean_object* v_stop_1095_){
_start:
{
size_t v_i_boxed_1096_; size_t v_stop_boxed_1097_; uint8_t v_res_1098_; lean_object* v_r_1099_; 
v_i_boxed_1096_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_stop_boxed_1097_ = lean_unbox_usize(v_stop_1095_);
lean_dec(v_stop_1095_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1091_, v___x_1092_, v_as_1093_, v_i_boxed_1096_, v_stop_boxed_1097_);
lean_dec_ref(v_as_1093_);
lean_dec(v___x_1092_);
lean_dec(v_i_1091_);
v_r_1099_ = lean_box(v_res_1098_);
return v_r_1099_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(lean_object* v_as_1100_, lean_object* v_a_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_zero_1103_; uint8_t v_isZero_1104_; 
v_zero_1103_ = lean_unsigned_to_nat(0u);
v_isZero_1104_ = lean_nat_dec_eq(v_x_1102_, v_zero_1103_);
if (v_isZero_1104_ == 1)
{
lean_dec(v_x_1102_);
return v_isZero_1104_;
}
else
{
lean_object* v_one_1105_; lean_object* v_n_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_one_1105_ = lean_unsigned_to_nat(1u);
v_n_1106_ = lean_nat_sub(v_x_1102_, v_one_1105_);
lean_dec(v_x_1102_);
v___x_1107_ = lean_array_fget_borrowed(v_as_1100_, v_n_1106_);
v___x_1108_ = lean_expr_eqv(v_a_1101_, v___x_1107_);
if (v___x_1108_ == 0)
{
v_x_1102_ = v_n_1106_;
goto _start;
}
else
{
lean_dec(v_n_1106_);
return v_isZero_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_as_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1110_, v_a_1111_, v_x_1112_);
lean_dec_ref(v_a_1111_);
lean_dec_ref(v_as_1110_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(lean_object* v_as_1115_, lean_object* v_i_1116_){
_start:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_array_get_size(v_as_1115_);
v___x_1118_ = lean_nat_dec_lt(v_i_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; 
lean_dec(v_i_1116_);
v___x_1119_ = 1;
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_array_fget_borrowed(v_as_1115_, v_i_1116_);
lean_inc(v_i_1116_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1115_, v___x_1120_, v_i_1116_);
if (v___x_1121_ == 0)
{
lean_dec(v_i_1116_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1116_, v___x_1122_);
lean_dec(v_i_1116_);
v_i_1116_ = v___x_1123_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3___boxed(lean_object* v_as_1125_, lean_object* v_i_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1125_, v_i_1126_);
lean_dec_ref(v_as_1125_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_as_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1129_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_as_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_as_1132_);
lean_dec_ref(v_as_1132_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1146_ = lean_unsigned_to_nat(59u);
v___x_1147_ = lean_unsigned_to_nat(96u);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1150_ = l_mkPanicMessageWithDecl(v___x_1149_, v___x_1148_, v___x_1147_, v___x_1146_, v___x_1145_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1175_; lean_object* v_dummy_1176_; 
v___x_1175_ = lean_box(0);
v_dummy_1176_ = l_Lean_Expr_sort___override(v___x_1175_);
return v_dummy_1176_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1182_ = lean_unsigned_to_nat(2u);
v___x_1183_ = lean_unsigned_to_nat(68u);
v___x_1184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1186_ = l_mkPanicMessageWithDecl(v___x_1185_, v___x_1184_, v___x_1183_, v___x_1182_, v___x_1181_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1192_ = l_Lean_stringToMessageData(v___x_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1199_, lean_object* v_fixedParamPerm_1200_, lean_object* v_xs_1201_, lean_object* v_i_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v_lower_1349_; lean_object* v_upper_1350_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___x_1435_; 
v___x_1334_ = lean_array_get_size(v_fixedParamPerm_1200_);
v___x_1335_ = lean_array_get_size(v_xs_1201_);
v___x_1435_ = lean_nat_dec_eq(v___x_1334_, v___x_1335_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1436_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1437_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1436_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1437_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_lt(v_i_1202_, v___x_1335_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1439_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_i_1202_, v___x_1440_);
lean_dec(v_i_1202_);
v___x_1442_ = l_Nat_reprFast(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___x_1444_ = l_Lean_MessageData_ofFormat(v___x_1443_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1439_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Nat_reprFast(v___x_1335_);
v___x_1449_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
v___x_1450_ = l_Lean_MessageData_ofFormat(v___x_1449_);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1447_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1453_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1454_;
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1200_, v_i_1202_);
if (v___x_1455_ == 0)
{
v___y_1408_ = v_a_1203_;
v___y_1409_ = v_a_1204_;
v___y_1410_ = v_a_1205_;
v___y_1411_ = v_a_1206_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1456_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1457_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1456_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
v___jp_1208_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1214_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1213_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1214_;
}
v___jp_1215_:
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1218_);
if (v___x_1227_ == 0)
{
lean_object* v_name_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_name_1228_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_name_1228_);
lean_dec_ref(v___y_1219_);
v___x_1229_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1230_ = l_Lean_MessageData_ofName(v_name_1228_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_indentExpr(v___y_1217_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1235_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1200_, v_xs_1201_);
v___x_1238_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1237_, v___y_1218_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
if (lean_obj_tag(v_a_1239_) == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1237_, v___y_1225_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
lean_dec_ref(v___x_1237_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1291_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1291_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1291_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
if (lean_obj_tag(v_a_1241_) == 0)
{
lean_object* v_name_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v___y_1217_);
v_name_1245_ = lean_ctor_get(v___y_1219_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___y_1219_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1266_ = lean_ctor_get(v___y_1219_, 2);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v___y_1219_, 1);
lean_dec(v_unused_1267_);
v___x_1247_ = v___y_1219_;
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_name_1245_);
lean_dec(v___y_1219_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_array_mk(v___y_1223_);
v___x_1250_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1249_, v_name_1245_);
lean_dec(v_name_1245_);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_val_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_sz_1252_ = lean_array_size(v___y_1218_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1201_, v_sz_1252_, v___x_1253_, v___y_1218_);
v___x_1255_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1220_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 2, v___y_1225_);
lean_ctor_set(v___x_1247_, 1, v___y_1224_);
lean_ctor_set(v___x_1247_, 0, v___x_1255_);
v___x_1257_ = v___x_1247_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___y_1224_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___y_1225_);
v___x_1257_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1258_, 0, v_fnName_1199_);
lean_ctor_set(v___x_1258_, 1, v_fixedParamPerm_1200_);
lean_ctor_set(v___x_1258_, 2, v_i_1202_);
lean_ctor_set(v___x_1258_, 3, v___x_1254_);
lean_ctor_set(v___x_1258_, 4, v___x_1257_);
lean_ctor_set(v___x_1258_, 5, v_val_1251_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1258_);
v___x_1260_ = v___x_1243_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v___x_1250_);
lean_del_object(v___x_1247_);
lean_del_object(v___x_1243_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1263_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1264_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1263_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
return v___x_1264_;
}
}
}
else
{
lean_object* v_val_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1243_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_val_1268_ = lean_ctor_get(v_a_1241_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v_a_1241_, 1);
v_fst_1269_ = lean_ctor_get(v_val_1268_, 0);
v_snd_1270_ = lean_ctor_get(v_val_1268_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_val_1268_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1272_ = v_val_1268_;
v_isShared_1273_ = v_isSharedCheck_1290_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_snd_1270_);
lean_inc(v_fst_1269_);
lean_dec(v_val_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1290_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1275_ = l_Lean_indentExpr(v___y_1217_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 7);
lean_ctor_set(v___x_1272_, 1, v___x_1275_);
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1278_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_indentExpr(v_fst_1269_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_indentExpr(v_snd_1270_);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1287_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_a_1292_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1240_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1240_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_val_1300_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v___x_1237_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_val_1300_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_val_1300_);
lean_dec_ref_known(v_a_1239_, 1);
v_fst_1301_ = lean_ctor_get(v_val_1300_, 0);
v_snd_1302_ = lean_ctor_get(v_val_1300_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_val_1300_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1304_ = v_val_1300_;
v_isShared_1305_ = v_isSharedCheck_1325_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snd_1302_);
lean_inc(v_fst_1301_);
lean_dec(v_val_1300_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1325_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_name_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v_name_1306_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_name_1306_);
lean_dec_ref(v___y_1219_);
v___x_1307_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1308_ = l_Lean_MessageData_ofName(v_name_1306_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 7);
lean_ctor_set(v___x_1304_, 1, v___x_1308_);
lean_ctor_set(v___x_1304_, 0, v___x_1307_);
v___x_1310_ = v___x_1304_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_indentExpr(v___y_1217_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_indentExpr(v_fst_1301_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Lean_indentExpr(v_snd_1302_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1322_, v___y_1226_, v___y_1221_, v___y_1216_, v___y_1222_);
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v___x_1237_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_a_1326_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1238_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1238_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
v___jp_1336_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1351_ = l_Array_toSubarray___redArg(v___y_1337_, v_lower_1349_, v_upper_1350_);
v___x_1352_ = l_Subarray_copy___redArg(v___x_1351_);
v___x_1353_ = lean_array_get_size(v___x_1352_);
v___x_1354_ = lean_nat_dec_lt(v___y_1346_, v___x_1353_);
lean_dec(v___y_1346_);
if (v___x_1354_ == 0)
{
v___y_1216_ = v___y_1343_;
v___y_1217_ = v___y_1344_;
v___y_1218_ = v___x_1352_;
v___y_1219_ = v___y_1345_;
v___y_1220_ = v___y_1338_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1342_;
v___y_1225_ = v___y_1347_;
v___y_1226_ = v___y_1348_;
goto v___jp_1215_;
}
else
{
if (v___x_1354_ == 0)
{
v___y_1216_ = v___y_1343_;
v___y_1217_ = v___y_1344_;
v___y_1218_ = v___x_1352_;
v___y_1219_ = v___y_1345_;
v___y_1220_ = v___y_1338_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1342_;
v___y_1225_ = v___y_1347_;
v___y_1226_ = v___y_1348_;
goto v___jp_1215_;
}
else
{
size_t v___x_1355_; size_t v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1353_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1202_, v___x_1335_, v___x_1352_, v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
v___y_1216_ = v___y_1343_;
v___y_1217_ = v___y_1344_;
v___y_1218_ = v___x_1352_;
v___y_1219_ = v___y_1345_;
v___y_1220_ = v___y_1338_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1342_;
v___y_1225_ = v___y_1347_;
v___y_1226_ = v___y_1348_;
goto v___jp_1215_;
}
else
{
lean_object* v_name_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1338_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_name_1358_ = lean_ctor_get(v___y_1345_, 0);
lean_inc(v_name_1358_);
lean_dec_ref(v___y_1345_);
v___x_1359_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1360_ = l_Lean_MessageData_ofName(v_name_1358_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_indentExpr(v___y_1344_);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1365_, v___y_1348_, v___y_1339_, v___y_1343_, v___y_1340_);
return v___x_1366_;
}
}
}
}
v___jp_1367_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = l_Lean_LocalDecl_type(v___y_1368_);
lean_dec_ref(v___y_1368_);
v___x_1374_ = l_Lean_Meta_whnfD(v___x_1373_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Expr_getAppFn(v_a_1375_);
if (lean_obj_tag(v___x_1376_) == 4)
{
lean_object* v_declName_1377_; lean_object* v_us_1378_; lean_object* v___x_1379_; lean_object* v_env_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v_declName_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_declName_1377_);
v_us_1378_ = lean_ctor_get(v___x_1376_, 1);
lean_inc(v_us_1378_);
lean_dec_ref_known(v___x_1376_, 2);
v___x_1379_ = lean_st_ref_get(v___y_1372_);
v_env_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = 0;
v___x_1382_ = l_Lean_Environment_find_x3f(v_env_1380_, v_declName_1377_, v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec(v_us_1378_);
lean_dec(v_a_1375_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1383_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v___x_1382_, 1);
if (lean_obj_tag(v_val_1383_) == 5)
{
lean_object* v_val_1384_; lean_object* v_toConstantVal_1385_; lean_object* v_numParams_1386_; lean_object* v_all_1387_; lean_object* v_nargs_1388_; lean_object* v_dummy_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_val_1384_ = lean_ctor_get(v_val_1383_, 0);
lean_inc_ref(v_val_1384_);
lean_dec_ref_known(v_val_1383_, 1);
v_toConstantVal_1385_ = lean_ctor_get(v_val_1384_, 0);
lean_inc_ref(v_toConstantVal_1385_);
v_numParams_1386_ = lean_ctor_get(v_val_1384_, 1);
v_all_1387_ = lean_ctor_get(v_val_1384_, 3);
lean_inc(v_all_1387_);
v_nargs_1388_ = l_Lean_Expr_getAppNumArgs(v_a_1375_);
v_dummy_1389_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1388_);
v___x_1390_ = lean_mk_array(v_nargs_1388_, v_dummy_1389_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_sub(v_nargs_1388_, v___x_1391_);
lean_dec(v_nargs_1388_);
lean_inc(v_a_1375_);
v___x_1393_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1375_, v___x_1390_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1386_);
lean_inc_ref(v___x_1393_);
v___x_1395_ = l_Array_toSubarray___redArg(v___x_1393_, v___x_1394_, v_numParams_1386_);
v___x_1396_ = l_Subarray_copy___redArg(v___x_1395_);
v___x_1397_ = lean_array_get_size(v___x_1393_);
v___x_1398_ = lean_nat_dec_le(v_numParams_1386_, v___x_1394_);
if (v___x_1398_ == 0)
{
lean_inc(v_numParams_1386_);
v___y_1337_ = v___x_1393_;
v___y_1338_ = v_val_1384_;
v___y_1339_ = v___y_1370_;
v___y_1340_ = v___y_1372_;
v___y_1341_ = v_all_1387_;
v___y_1342_ = v_us_1378_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v_a_1375_;
v___y_1345_ = v_toConstantVal_1385_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___x_1396_;
v___y_1348_ = v___y_1369_;
v_lower_1349_ = v_numParams_1386_;
v_upper_1350_ = v___x_1397_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v___x_1393_;
v___y_1338_ = v_val_1384_;
v___y_1339_ = v___y_1370_;
v___y_1340_ = v___y_1372_;
v___y_1341_ = v_all_1387_;
v___y_1342_ = v_us_1378_;
v___y_1343_ = v___y_1371_;
v___y_1344_ = v_a_1375_;
v___y_1345_ = v_toConstantVal_1385_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___x_1396_;
v___y_1348_ = v___y_1369_;
v_lower_1349_ = v___x_1394_;
v_upper_1350_ = v___x_1397_;
goto v___jp_1336_;
}
}
else
{
lean_dec(v_val_1383_);
lean_dec(v_us_1378_);
lean_dec(v_a_1375_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
goto v___jp_1208_;
}
}
}
else
{
lean_dec_ref(v___x_1376_);
lean_dec(v_a_1375_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
v___y_1212_ = v___y_1372_;
goto v___jp_1208_;
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_a_1399_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1374_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1374_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
v___jp_1407_:
{
lean_object* v_x_1412_; lean_object* v___x_1413_; 
v_x_1412_ = lean_array_fget_borrowed(v_xs_1201_, v_i_1202_);
v___x_1413_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1412_, v___y_1408_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; uint8_t v___x_1415_; uint8_t v___x_1416_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_LocalDecl_isLet(v_a_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
v___y_1368_ = v_a_1414_;
v___y_1369_ = v___y_1408_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
v___y_1372_ = v___y_1411_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_a_1414_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1418_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1417_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
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
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_a_1427_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1413_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1413_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1466_, lean_object* v_fixedParamPerm_1467_, lean_object* v_xs_1468_, lean_object* v_i_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1466_, v_fixedParamPerm_1467_, v_xs_1468_, v_i_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec_ref(v_xs_1468_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1476_, lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_msg_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1484_, v_msg_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(lean_object* v_as_1492_, lean_object* v_a_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1492_, v_a_1493_, v_x_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___boxed(lean_object* v_as_1497_, lean_object* v_a_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(v_as_1497_, v_a_1498_, v_x_1499_, v_x_1500_);
lean_dec_ref(v_a_1498_);
lean_dec_ref(v_as_1497_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1503_, lean_object* v_e_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = l_Lean_indentD(v_e_1504_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1503_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1507_, lean_object* v_fnName_1508_, lean_object* v_fixedParamPerm_1509_, lean_object* v_args_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1507_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1508_, v_fixedParamPerm_1509_, v_args_1510_, v_a_1517_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1518_;
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_fixedParamPerm_1509_);
lean_dec(v_fnName_1508_);
v_a_1519_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1516_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1516_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1527_, lean_object* v_fnName_1528_, lean_object* v_fixedParamPerm_1529_, lean_object* v_args_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1527_, v_fnName_1528_, v_fixedParamPerm_1529_, v_args_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_args_1530_);
return v_res_1536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1548_, lean_object* v_fnName_1549_, lean_object* v_fixedParamPerm_1550_, lean_object* v_args_1551_, lean_object* v_a_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_fst_1560_; lean_object* v_snd_1561_; uint8_t v___x_1566_; 
v___x_1566_ = lean_nat_dec_lt(v_a_1552_, v_upperBound_1548_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec(v_a_1552_);
lean_dec_ref(v_fixedParamPerm_1550_);
lean_dec(v_fnName_1549_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_b_1553_);
return v___x_1567_;
}
else
{
lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1614_; 
v_fst_1568_ = lean_ctor_get(v_b_1553_, 0);
v_snd_1569_ = lean_ctor_get(v_b_1553_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_b_1553_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1571_ = v_b_1553_;
v_isShared_1572_ = v_isSharedCheck_1614_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_inc(v_fst_1568_);
lean_dec(v_b_1553_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1614_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; 
lean_inc(v_a_1552_);
lean_inc_ref(v_fixedParamPerm_1550_);
lean_inc(v_fnName_1549_);
v___x_1573_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1549_, v_fixedParamPerm_1550_, v_args_1551_, v_a_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1571_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = lean_array_push(v_fst_1568_, v_a_1574_);
v_fst_1560_ = v___x_1575_;
v_snd_1561_ = v_snd_1569_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1613_; 
v_a_1576_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1578_ = v___x_1573_;
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1573_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
uint8_t v___y_1581_; uint8_t v___x_1611_; 
v___x_1611_ = l_Lean_Exception_isInterrupt(v_a_1576_);
if (v___x_1611_ == 0)
{
uint8_t v___x_1612_; 
lean_inc(v_a_1576_);
v___x_1612_ = l_Lean_Exception_isRuntime(v_a_1576_);
v___y_1581_ = v___x_1612_;
goto v___jp_1580_;
}
else
{
v___y_1581_ = v___x_1611_;
goto v___jp_1580_;
}
v___jp_1580_:
{
if (v___y_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_del_object(v___x_1578_);
v___x_1582_ = l_Lean_Elab_Structural_prettyParam(v_args_1551_, v_a_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 7);
lean_ctor_set(v___x_1571_, 1, v_a_1583_);
lean_ctor_set(v___x_1571_, 0, v___x_1584_);
v___x_1586_ = v___x_1571_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_a_1583_);
v___x_1586_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_inc(v_fnName_1549_);
v___x_1589_ = l_Lean_MessageData_ofName(v_fnName_1549_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_Exception_toMessageData(v_a_1576_);
v___x_1594_ = l_Lean_indentD(v___x_1593_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_snd_1569_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v_fst_1560_ = v_fst_1568_;
v_snd_1561_ = v___x_1598_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1576_);
lean_del_object(v___x_1571_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec(v_a_1552_);
lean_dec_ref(v_fixedParamPerm_1550_);
lean_dec(v_fnName_1549_);
v_a_1600_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1582_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1582_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
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
else
{
lean_object* v___x_1609_; 
lean_del_object(v___x_1571_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec(v_a_1552_);
lean_dec_ref(v_fixedParamPerm_1550_);
lean_dec(v_fnName_1549_);
if (v_isShared_1579_ == 0)
{
v___x_1609_ = v___x_1578_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1576_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
}
v___jp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_fst_1560_);
lean_ctor_set(v___x_1562_, 1, v_snd_1561_);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_a_1552_, v___x_1563_);
lean_dec(v_a_1552_);
v_a_1552_ = v___x_1564_;
v_b_1553_ = v___x_1562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1615_, lean_object* v_fnName_1616_, lean_object* v_fixedParamPerm_1617_, lean_object* v_args_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1615_, v_fnName_1616_, v_fixedParamPerm_1617_, v_args_1618_, v_a_1619_, v_b_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_args_1618_);
lean_dec(v_upperBound_1615_);
return v_res_1626_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1627_; double v___x_1628_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_float_of_nat(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1630_, lean_object* v_msg_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_ref_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1683_; 
v_ref_1637_ = lean_ctor_get(v___y_1634_, 2);
v___x_1638_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1683_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1683_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v_traceState_1644_; lean_object* v_env_1645_; lean_object* v_nextMacroScope_1646_; lean_object* v_ngen_1647_; lean_object* v_auxDeclNGen_1648_; lean_object* v_cache_1649_; lean_object* v_messages_1650_; lean_object* v_infoState_1651_; lean_object* v_snapshotTasks_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1682_; 
v___x_1643_ = lean_st_ref_take(v___y_1635_);
v_traceState_1644_ = lean_ctor_get(v___x_1643_, 4);
v_env_1645_ = lean_ctor_get(v___x_1643_, 0);
v_nextMacroScope_1646_ = lean_ctor_get(v___x_1643_, 1);
v_ngen_1647_ = lean_ctor_get(v___x_1643_, 2);
v_auxDeclNGen_1648_ = lean_ctor_get(v___x_1643_, 3);
v_cache_1649_ = lean_ctor_get(v___x_1643_, 5);
v_messages_1650_ = lean_ctor_get(v___x_1643_, 6);
v_infoState_1651_ = lean_ctor_get(v___x_1643_, 7);
v_snapshotTasks_1652_ = lean_ctor_get(v___x_1643_, 8);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1654_ = v___x_1643_;
v_isShared_1655_ = v_isSharedCheck_1682_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snapshotTasks_1652_);
lean_inc(v_infoState_1651_);
lean_inc(v_messages_1650_);
lean_inc(v_cache_1649_);
lean_inc(v_traceState_1644_);
lean_inc(v_auxDeclNGen_1648_);
lean_inc(v_ngen_1647_);
lean_inc(v_nextMacroScope_1646_);
lean_inc(v_env_1645_);
lean_dec(v___x_1643_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1682_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
uint64_t v_tid_1656_; lean_object* v_traces_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1681_; 
v_tid_1656_ = lean_ctor_get_uint64(v_traceState_1644_, sizeof(void*)*1);
v_traces_1657_ = lean_ctor_get(v_traceState_1644_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_traceState_1644_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1659_ = v_traceState_1644_;
v_isShared_1660_ = v_isSharedCheck_1681_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_traces_1657_);
lean_dec(v_traceState_1644_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1681_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; double v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1663_ = 0;
v___x_1664_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1665_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1665_, 0, v_cls_1630_);
lean_ctor_set(v___x_1665_, 1, v___x_1661_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
lean_ctor_set_float(v___x_1665_, sizeof(void*)*3, v___x_1662_);
lean_ctor_set_float(v___x_1665_, sizeof(void*)*3 + 8, v___x_1662_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*3 + 16, v___x_1663_);
v___x_1666_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1667_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v_a_1639_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
lean_inc(v_ref_1637_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_ref_1637_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_PersistentArray_push___redArg(v_traces_1657_, v___x_1668_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1669_);
v___x_1671_ = v___x_1659_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1669_);
lean_ctor_set_uint64(v_reuseFailAlloc_1680_, sizeof(void*)*1, v_tid_1656_);
v___x_1671_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 4, v___x_1671_);
v___x_1673_ = v___x_1654_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_env_1645_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_nextMacroScope_1646_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_ngen_1647_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_auxDeclNGen_1648_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1679_, 5, v_cache_1649_);
lean_ctor_set(v_reuseFailAlloc_1679_, 6, v_messages_1650_);
lean_ctor_set(v_reuseFailAlloc_1679_, 7, v_infoState_1651_);
lean_ctor_set(v_reuseFailAlloc_1679_, 8, v_snapshotTasks_1652_);
v___x_1673_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = lean_st_ref_put(v___y_1635_, v___x_1673_);
v___x_1675_ = lean_box(0);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1675_);
v___x_1677_ = v___x_1641_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1684_, lean_object* v_msg_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1684_, v_msg_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___f_1696_; 
v___x_1695_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1696_, 0, v___x_1695_);
return v___f_1696_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1701_; lean_object* v_recArgInfos_1702_; lean_object* v___x_1703_; 
v_report_1701_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1702_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_recArgInfos_1702_);
lean_ctor_set(v___x_1703_, 1, v_report_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1716_ = l_Lean_Name_append(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1720_, lean_object* v_fixedParamPerm_1721_, lean_object* v_xs_1722_, lean_object* v_fnName_1723_, lean_object* v_ys_1724_, lean_object* v_x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1720_) == 1)
{
lean_object* v_val_1731_; lean_object* v_ref_1732_; lean_object* v_toCold_1733_; lean_object* v_currRecDepth_1734_; lean_object* v_ref_1735_; uint8_t v_diag_1736_; uint8_t v_suppressElabErrors_1737_; lean_object* v___f_1738_; lean_object* v_args_1739_; lean_object* v___f_1740_; lean_object* v_ref_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_val_1731_ = lean_ctor_get(v_termMeasure_x3f_1720_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v_termMeasure_x3f_1720_, 1);
v_ref_1732_ = lean_ctor_get(v_val_1731_, 0);
lean_inc(v_ref_1732_);
v_toCold_1733_ = lean_ctor_get(v___y_1728_, 0);
v_currRecDepth_1734_ = lean_ctor_get(v___y_1728_, 1);
v_ref_1735_ = lean_ctor_get(v___y_1728_, 2);
v_diag_1736_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*3);
v_suppressElabErrors_1737_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*3 + 1);
v___f_1738_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1721_);
v_args_1739_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1721_, v_xs_1722_, v_ys_1724_);
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1740_, 0, v_val_1731_);
lean_closure_set(v___f_1740_, 1, v_fnName_1723_);
lean_closure_set(v___f_1740_, 2, v_fixedParamPerm_1721_);
lean_closure_set(v___f_1740_, 3, v_args_1739_);
v_ref_1741_ = l_Lean_replaceRef(v_ref_1732_, v_ref_1735_);
lean_dec(v_ref_1732_);
lean_inc(v_currRecDepth_1734_);
lean_inc_ref(v_toCold_1733_);
v___x_1742_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1742_, 0, v_toCold_1733_);
lean_ctor_set(v___x_1742_, 1, v_currRecDepth_1734_);
lean_ctor_set(v___x_1742_, 2, v_ref_1741_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*3, v_diag_1736_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*3 + 1, v_suppressElabErrors_1737_);
v___x_1743_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1740_, v___f_1738_, v___y_1726_, v___y_1727_, v___x_1742_, v___y_1729_);
lean_dec_ref_known(v___x_1742_, 3);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1756_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_mk_empty_array_with_capacity(v___x_1748_);
v___x_1750_ = lean_array_push(v___x_1749_, v_a_1744_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1752_);
v___x_1754_ = v___x_1746_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1743_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1743_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v_args_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_termMeasure_x3f_1720_);
lean_inc_ref(v_fixedParamPerm_1721_);
v_args_1765_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1721_, v_xs_1722_, v_ys_1724_);
v___x_1766_ = lean_array_get_size(v_args_1765_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1769_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1766_, v_fnName_1723_, v_fixedParamPerm_1721_, v_args_1765_, v___x_1767_, v___x_1768_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec_ref(v_args_1765_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1805_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1805_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1805_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1804_; 
v_fst_1774_ = lean_ctor_get(v_a_1770_, 0);
v_snd_1775_ = lean_ctor_get(v_a_1770_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_a_1770_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1777_ = v_a_1770_;
v_isShared_1778_ = v_isSharedCheck_1804_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_snd_1775_);
lean_inc(v_fst_1774_);
lean_dec(v_a_1770_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1804_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_toCold_1786_; lean_object* v_options_1787_; uint8_t v_hasTrace_1788_; 
v_toCold_1786_ = lean_ctor_get(v___y_1728_, 0);
v_options_1787_ = lean_ctor_get(v_toCold_1786_, 2);
v_hasTrace_1788_ = lean_ctor_get_uint8(v_options_1787_, sizeof(void*)*1);
if (v_hasTrace_1788_ == 0)
{
goto v___jp_1779_;
}
else
{
lean_object* v_inheritedTraceOptions_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_inheritedTraceOptions_1789_ = lean_ctor_get(v_toCold_1786_, 11);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1791_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1789_, v_options_1787_, v___x_1791_);
if (v___x_1792_ == 0)
{
goto v___jp_1779_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1775_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_snd_1775_);
v___x_1795_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1790_, v___x_1794_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_dec_ref_known(v___x_1795_, 1);
goto v___jp_1779_;
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_del_object(v___x_1777_);
lean_dec(v_snd_1775_);
lean_dec(v_fst_1774_);
lean_del_object(v___x_1772_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
v___jp_1779_:
{
lean_object* v___x_1781_; 
if (v_isShared_1778_ == 0)
{
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1774_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1775_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1781_);
v___x_1783_ = v___x_1772_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
else
{
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1806_, lean_object* v_fixedParamPerm_1807_, lean_object* v_xs_1808_, lean_object* v_fnName_1809_, lean_object* v_ys_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1806_, v_fixedParamPerm_1807_, v_xs_1808_, v_fnName_1809_, v_ys_1810_, v_x_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_x_1811_);
lean_dec_ref(v_xs_1808_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1818_, lean_object* v_fixedParamPerm_1819_, lean_object* v_xs_1820_, lean_object* v_value_1821_, lean_object* v_termMeasure_x3f_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v___f_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; 
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1828_, 0, v_termMeasure_x3f_1822_);
lean_closure_set(v___f_1828_, 1, v_fixedParamPerm_1819_);
lean_closure_set(v___f_1828_, 2, v_xs_1820_);
lean_closure_set(v___f_1828_, 3, v_fnName_1818_);
v___x_1829_ = 0;
v___x_1830_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1821_, v___f_1828_, v___x_1829_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1831_, lean_object* v_fixedParamPerm_1832_, lean_object* v_xs_1833_, lean_object* v_value_1834_, lean_object* v_termMeasure_x3f_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1831_, v_fixedParamPerm_1832_, v_xs_1833_, v_value_1834_, v_termMeasure_x3f_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1842_, lean_object* v_fnName_1843_, lean_object* v_fixedParamPerm_1844_, lean_object* v_args_1845_, lean_object* v_inst_1846_, lean_object* v_R_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v_c_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1842_, v_fnName_1843_, v_fixedParamPerm_1844_, v_args_1845_, v_a_1848_, v_b_1849_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1857_, lean_object* v_fnName_1858_, lean_object* v_fixedParamPerm_1859_, lean_object* v_args_1860_, lean_object* v_inst_1861_, lean_object* v_R_1862_, lean_object* v_a_1863_, lean_object* v_b_1864_, lean_object* v_c_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1857_, v_fnName_1858_, v_fixedParamPerm_1859_, v_args_1860_, v_inst_1861_, v_R_1862_, v_a_1863_, v_b_1864_, v_c_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_args_1860_);
lean_dec(v_upperBound_1857_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
return v_x_1872_;
}
else
{
lean_object* v_key_1874_; lean_object* v_value_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1899_; 
v_key_1874_ = lean_ctor_get(v_x_1873_, 0);
v_value_1875_ = lean_ctor_get(v_x_1873_, 1);
v_tail_1876_ = lean_ctor_get(v_x_1873_, 2);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1873_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1878_ = v_x_1873_;
v_isShared_1879_ = v_isSharedCheck_1899_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_value_1875_);
lean_inc(v_key_1874_);
lean_dec(v_x_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1899_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v_fold_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1880_ = lean_array_get_size(v_x_1872_);
v___x_1881_ = lean_uint64_of_nat(v_key_1874_);
v___x_1882_ = 32ULL;
v___x_1883_ = lean_uint64_shift_right(v___x_1881_, v___x_1882_);
v_fold_1884_ = lean_uint64_xor(v___x_1881_, v___x_1883_);
v___x_1885_ = 16ULL;
v___x_1886_ = lean_uint64_shift_right(v_fold_1884_, v___x_1885_);
v___x_1887_ = lean_uint64_xor(v_fold_1884_, v___x_1886_);
v___x_1888_ = lean_uint64_to_usize(v___x_1887_);
v___x_1889_ = lean_usize_of_nat(v___x_1880_);
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_sub(v___x_1889_, v___x_1890_);
v___x_1892_ = lean_usize_land(v___x_1888_, v___x_1891_);
v___x_1893_ = lean_array_uget_borrowed(v_x_1872_, v___x_1892_);
lean_inc(v___x_1893_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 2, v___x_1893_);
v___x_1895_ = v___x_1878_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_key_1874_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_value_1875_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_array_uset(v_x_1872_, v___x_1892_, v___x_1895_);
v_x_1872_ = v___x_1896_;
v_x_1873_ = v_tail_1876_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1900_, lean_object* v_source_1901_, lean_object* v_target_1902_){
_start:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_array_get_size(v_source_1901_);
v___x_1904_ = lean_nat_dec_lt(v_i_1900_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_dec_ref(v_source_1901_);
lean_dec(v_i_1900_);
return v_target_1902_;
}
else
{
lean_object* v_es_1905_; lean_object* v___x_1906_; lean_object* v_source_1907_; lean_object* v_target_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_es_1905_ = lean_array_fget(v_source_1901_, v_i_1900_);
v___x_1906_ = lean_box(0);
v_source_1907_ = lean_array_fset(v_source_1901_, v_i_1900_, v___x_1906_);
v_target_1908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1902_, v_es_1905_);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_i_1900_, v___x_1909_);
lean_dec(v_i_1900_);
v_i_1900_ = v___x_1910_;
v_source_1901_ = v_source_1907_;
v_target_1902_ = v_target_1908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_nbuckets_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1913_ = lean_array_get_size(v_data_1912_);
v___x_1914_ = lean_unsigned_to_nat(2u);
v_nbuckets_1915_ = lean_nat_mul(v___x_1913_, v___x_1914_);
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_mk_array(v_nbuckets_1915_, v___x_1917_);
v___x_1919_ = lean_array_propagate_mark(v_data_1912_, v___x_1918_);
v___x_1920_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1916_, v_data_1912_, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1921_, lean_object* v_x_1922_){
_start:
{
if (lean_obj_tag(v_x_1922_) == 0)
{
uint8_t v___x_1923_; 
v___x_1923_ = 0;
return v___x_1923_;
}
else
{
lean_object* v_key_1924_; lean_object* v_tail_1925_; uint8_t v___x_1926_; 
v_key_1924_ = lean_ctor_get(v_x_1922_, 0);
v_tail_1925_ = lean_ctor_get(v_x_1922_, 2);
v___x_1926_ = lean_nat_dec_eq(v_key_1924_, v_a_1921_);
if (v___x_1926_ == 0)
{
v_x_1922_ = v_tail_1925_;
goto _start;
}
else
{
return v___x_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1928_, lean_object* v_x_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1928_, v_x_1929_);
lean_dec(v_x_1929_);
lean_dec(v_a_1928_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1932_, lean_object* v_a_1933_, lean_object* v_b_1934_){
_start:
{
lean_object* v_size_1935_; lean_object* v_buckets_1936_; lean_object* v___x_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v_fold_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v_bkt_1950_; uint8_t v___x_1951_; 
v_size_1935_ = lean_ctor_get(v_m_1932_, 0);
v_buckets_1936_ = lean_ctor_get(v_m_1932_, 1);
v___x_1937_ = lean_array_get_size(v_buckets_1936_);
v___x_1938_ = lean_uint64_of_nat(v_a_1933_);
v___x_1939_ = 32ULL;
v___x_1940_ = lean_uint64_shift_right(v___x_1938_, v___x_1939_);
v_fold_1941_ = lean_uint64_xor(v___x_1938_, v___x_1940_);
v___x_1942_ = 16ULL;
v___x_1943_ = lean_uint64_shift_right(v_fold_1941_, v___x_1942_);
v___x_1944_ = lean_uint64_xor(v_fold_1941_, v___x_1943_);
v___x_1945_ = lean_uint64_to_usize(v___x_1944_);
v___x_1946_ = lean_usize_of_nat(v___x_1937_);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_sub(v___x_1946_, v___x_1947_);
v___x_1949_ = lean_usize_land(v___x_1945_, v___x_1948_);
v_bkt_1950_ = lean_array_uget_borrowed(v_buckets_1936_, v___x_1949_);
v___x_1951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1933_, v_bkt_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1972_; 
lean_inc_ref(v_buckets_1936_);
lean_inc(v_size_1935_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_m_1932_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; lean_object* v_unused_1974_; 
v_unused_1973_ = lean_ctor_get(v_m_1932_, 1);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_m_1932_, 0);
lean_dec(v_unused_1974_);
v___x_1953_ = v_m_1932_;
v_isShared_1954_ = v_isSharedCheck_1972_;
goto v_resetjp_1952_;
}
else
{
lean_dec(v_m_1932_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1972_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v_size_x27_1956_; lean_object* v___x_1957_; lean_object* v_buckets_x27_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1955_ = lean_unsigned_to_nat(1u);
v_size_x27_1956_ = lean_nat_add(v_size_1935_, v___x_1955_);
lean_dec(v_size_1935_);
lean_inc(v_bkt_1950_);
v___x_1957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1933_);
lean_ctor_set(v___x_1957_, 1, v_b_1934_);
lean_ctor_set(v___x_1957_, 2, v_bkt_1950_);
v_buckets_x27_1958_ = lean_array_uset(v_buckets_1936_, v___x_1949_, v___x_1957_);
v___x_1959_ = lean_unsigned_to_nat(4u);
v___x_1960_ = lean_nat_mul(v_size_x27_1956_, v___x_1959_);
v___x_1961_ = lean_unsigned_to_nat(3u);
v___x_1962_ = lean_nat_div(v___x_1960_, v___x_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_array_get_size(v_buckets_x27_1958_);
v___x_1964_ = lean_nat_dec_le(v___x_1962_, v___x_1963_);
lean_dec(v___x_1962_);
if (v___x_1964_ == 0)
{
lean_object* v_val_1965_; lean_object* v___x_1967_; 
v_val_1965_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1958_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_val_1965_);
lean_ctor_set(v___x_1953_, 0, v_size_x27_1956_);
v___x_1967_ = v___x_1953_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_size_x27_1956_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_val_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
lean_object* v___x_1970_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_buckets_x27_1958_);
lean_ctor_set(v___x_1953_, 0, v_size_x27_1956_);
v___x_1970_ = v___x_1953_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_size_x27_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_buckets_x27_1958_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_dec(v_b_1934_);
lean_dec(v_a_1933_);
return v_m_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1975_, size_t v_sz_1976_, size_t v_i_1977_, lean_object* v_b_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
if (v___x_1979_ == 0)
{
return v_b_1978_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; size_t v___x_1983_; size_t v___x_1984_; 
v_a_1980_ = lean_array_uget_borrowed(v_as_1975_, v_i_1977_);
v___x_1981_ = lean_box(0);
lean_inc(v_a_1980_);
v___x_1982_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1978_, v_a_1980_, v___x_1981_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1977_, v___x_1983_);
v_i_1977_ = v___x_1984_;
v_b_1978_ = v___x_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1986_, lean_object* v_sz_1987_, lean_object* v_i_1988_, lean_object* v_b_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1986_, v_sz_boxed_1990_, v_i_boxed_1991_, v_b_1989_);
lean_dec_ref(v_as_1986_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1993_, size_t v_sz_1994_, size_t v_i_1995_, lean_object* v_b_1996_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
if (v___x_1997_ == 0)
{
return v_b_1996_;
}
else
{
lean_object* v_a_1998_; lean_object* v_indicesPos_1999_; size_t v_sz_2000_; size_t v___x_2001_; lean_object* v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; 
v_a_1998_ = lean_array_uget_borrowed(v_as_1993_, v_i_1995_);
v_indicesPos_1999_ = lean_ctor_get(v_a_1998_, 3);
v_sz_2000_ = lean_array_size(v_indicesPos_1999_);
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_1999_, v_sz_2000_, v___x_2001_, v_b_1996_);
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1995_, v___x_2003_);
v_i_1995_ = v___x_2004_;
v_b_1996_ = v___x_2002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2006_, lean_object* v_sz_2007_, lean_object* v_i_2008_, lean_object* v_b_2009_){
_start:
{
size_t v_sz_boxed_2010_; size_t v_i_boxed_2011_; lean_object* v_res_2012_; 
v_sz_boxed_2010_ = lean_unbox_usize(v_sz_2007_);
lean_dec(v_sz_2007_);
v_i_boxed_2011_ = lean_unbox_usize(v_i_2008_);
lean_dec(v_i_2008_);
v_res_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2006_, v_sz_boxed_2010_, v_i_boxed_2011_, v_b_2009_);
lean_dec_ref(v_as_2006_);
return v_res_2012_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_buckets_2015_; lean_object* v___x_2016_; uint64_t v___x_2017_; uint64_t v___x_2018_; uint64_t v___x_2019_; uint64_t v_fold_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_buckets_2015_ = lean_ctor_get(v_m_2013_, 1);
v___x_2016_ = lean_array_get_size(v_buckets_2015_);
v___x_2017_ = lean_uint64_of_nat(v_a_2014_);
v___x_2018_ = 32ULL;
v___x_2019_ = lean_uint64_shift_right(v___x_2017_, v___x_2018_);
v_fold_2020_ = lean_uint64_xor(v___x_2017_, v___x_2019_);
v___x_2021_ = 16ULL;
v___x_2022_ = lean_uint64_shift_right(v_fold_2020_, v___x_2021_);
v___x_2023_ = lean_uint64_xor(v_fold_2020_, v___x_2022_);
v___x_2024_ = lean_uint64_to_usize(v___x_2023_);
v___x_2025_ = lean_usize_of_nat(v___x_2016_);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_sub(v___x_2025_, v___x_2026_);
v___x_2028_ = lean_usize_land(v___x_2024_, v___x_2027_);
v___x_2029_ = lean_array_uget_borrowed(v_buckets_2015_, v___x_2028_);
v___x_2030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2014_, v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2031_, lean_object* v_a_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_m_2031_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2035_, lean_object* v_as_2036_, size_t v_sz_2037_, size_t v_i_2038_, lean_object* v_b_2039_){
_start:
{
lean_object* v_a_2041_; uint8_t v___x_2045_; 
v___x_2045_ = lean_usize_dec_lt(v_i_2038_, v_sz_2037_);
if (v___x_2045_ == 0)
{
return v_b_2039_;
}
else
{
lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2062_; 
v_fst_2046_ = lean_ctor_get(v_b_2039_, 0);
v_snd_2047_ = lean_ctor_get(v_b_2039_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_b_2039_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2049_ = v_b_2039_;
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_snd_2047_);
lean_inc(v_fst_2046_);
lean_dec(v_b_2039_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2062_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_a_2051_; lean_object* v_recArgPos_2052_; uint8_t v___x_2053_; 
v_a_2051_ = lean_array_uget_borrowed(v_as_2036_, v_i_2038_);
v_recArgPos_2052_ = lean_ctor_get(v_a_2051_, 2);
v___x_2053_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2035_, v_recArgPos_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_inc(v_a_2051_);
v___x_2054_ = lean_array_push(v_snd_2047_, v_a_2051_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_fst_2046_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v_a_2041_ = v___x_2056_;
goto v___jp_2040_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_inc(v_a_2051_);
v___x_2058_ = lean_array_push(v_fst_2046_, v_a_2051_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2058_);
v___x_2060_ = v___x_2049_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_snd_2047_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v_a_2041_ = v___x_2060_;
goto v___jp_2040_;
}
}
}
}
v___jp_2040_:
{
size_t v___x_2042_; size_t v___x_2043_; 
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_add(v_i_2038_, v___x_2042_);
v_i_2038_ = v___x_2043_;
v_b_2039_ = v_a_2041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2063_, lean_object* v_as_2064_, lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_b_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2063_, v_as_2064_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2067_);
lean_dec_ref(v_as_2064_);
lean_dec_ref(v___x_2063_);
return v_res_2070_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_unsigned_to_nat(16u);
v___x_2073_ = lean_mk_array(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_indicesPos_2076_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2075_ = lean_unsigned_to_nat(0u);
v_indicesPos_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2076_, 0, v___x_2075_);
lean_ctor_set(v_indicesPos_2076_, 1, v___x_2074_);
return v_indicesPos_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2079_){
_start:
{
lean_object* v_indicesPos_2080_; size_t v_sz_2081_; size_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v___x_2088_; 
v_indicesPos_2080_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2081_ = lean_array_size(v_recArgInfos_2079_);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2079_, v_sz_2081_, v___x_2082_, v_indicesPos_2080_);
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2083_, v_recArgInfos_2079_, v_sz_2081_, v___x_2082_, v___x_2084_);
lean_dec_ref(v___x_2083_);
v_fst_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_fst_2086_);
v_snd_2087_ = lean_ctor_get(v___x_2085_, 1);
lean_inc(v_snd_2087_);
lean_dec_ref(v___x_2085_);
v___x_2088_ = l_Array_append___redArg(v_snd_2087_, v_fst_2086_);
lean_dec(v_fst_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2089_);
lean_dec_ref(v_recArgInfos_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2091_, lean_object* v_m_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2092_, v_a_2093_, v_b_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2096_, lean_object* v_m_2097_, lean_object* v_a_2098_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2097_, v_a_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2100_, lean_object* v_m_2101_, lean_object* v_a_2102_){
_start:
{
uint8_t v_res_2103_; lean_object* v_r_2104_; 
v_res_2103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2100_, v_m_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_m_2101_);
v_r_2104_ = lean_box(v_res_2103_);
return v_r_2104_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2105_, lean_object* v_a_2106_, lean_object* v_x_2107_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2106_, v_x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2109_, lean_object* v_a_2110_, lean_object* v_x_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2109_, v_a_2110_, v_x_2111_);
lean_dec(v_x_2111_);
lean_dec(v_a_2110_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2114_, lean_object* v_data_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2117_, lean_object* v_i_2118_, lean_object* v_source_2119_, lean_object* v_target_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2118_, v_source_2119_, v_target_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2123_, v_x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2126_, lean_object* v_a_2127_, lean_object* v_toPure_2128_, uint8_t v_____do__lift_2129_){
_start:
{
if (v_____do__lift_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_array_push(v___y_2126_, v_a_2127_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
v___x_2132_ = lean_apply_2(v_toPure_2128_, lean_box(0), v___x_2131_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec(v_a_2127_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___y_2126_);
v___x_2134_ = lean_apply_2(v_toPure_2128_, lean_box(0), v___x_2133_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2135_, lean_object* v_a_2136_, lean_object* v_toPure_2137_, lean_object* v_____do__lift_2138_){
_start:
{
uint8_t v_____do__lift_159__boxed_2139_; lean_object* v_res_2140_; 
v_____do__lift_159__boxed_2139_ = lean_unbox(v_____do__lift_2138_);
v_res_2140_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2135_, v_a_2136_, v_toPure_2137_, v_____do__lift_159__boxed_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2141_, lean_object* v_a_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_apply_2(v_eq_2141_, v_x_2143_, v_a_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2145_, lean_object* v___x_2146_, lean_object* v_toBind_2147_, lean_object* v_eq_2148_, lean_object* v_inst_2149_, lean_object* v_a_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___f_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
lean_inc(v_toPure_2145_);
lean_inc(v_a_2150_);
lean_inc_ref(v___y_2152_);
v___f_2153_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2153_, 0, v___y_2152_);
lean_closure_set(v___f_2153_, 1, v_a_2150_);
lean_closure_set(v___f_2153_, 2, v_toPure_2145_);
v___x_2154_ = lean_array_get_size(v___y_2152_);
v___x_2155_ = lean_nat_dec_lt(v___x_2146_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v___y_2152_);
lean_dec(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec(v_eq_2148_);
v___x_2156_ = lean_box(v___x_2155_);
v___x_2157_ = lean_apply_2(v_toPure_2145_, lean_box(0), v___x_2156_);
v___x_2158_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2157_, v___f_2153_);
return v___x_2158_;
}
else
{
if (v___x_2155_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___y_2152_);
lean_dec(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec(v_eq_2148_);
v___x_2159_ = lean_box(v___x_2155_);
v___x_2160_ = lean_apply_2(v_toPure_2145_, lean_box(0), v___x_2159_);
v___x_2161_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2160_, v___f_2153_);
return v___x_2161_;
}
else
{
lean_object* v___f_2162_; size_t v___x_2163_; size_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_toPure_2145_);
v___f_2162_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2162_, 0, v_eq_2148_);
lean_closure_set(v___f_2162_, 1, v_a_2150_);
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = lean_usize_of_nat(v___x_2154_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2149_, v___f_2162_, v___y_2152_, v___x_2163_, v___x_2164_);
v___x_2166_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2165_, v___f_2153_);
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2167_, lean_object* v___x_2168_, lean_object* v_toBind_2169_, lean_object* v_eq_2170_, lean_object* v_inst_2171_, lean_object* v_a_2172_, lean_object* v_x_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2167_, v___x_2168_, v_toBind_2169_, v_eq_2170_, v_inst_2171_, v_a_2172_, v_x_2173_, v___y_2174_);
lean_dec(v___x_2168_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2176_, lean_object* v_____s_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_apply_2(v_toPure_2176_, lean_box(0), v_____s_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2181_, lean_object* v_eq_2182_, lean_object* v_xs_2183_){
_start:
{
lean_object* v_toApplicative_2184_; lean_object* v_toBind_2185_; lean_object* v_toPure_2186_; lean_object* v___x_2187_; lean_object* v_ret_2188_; lean_object* v___f_2189_; lean_object* v___f_2190_; size_t v_sz_2191_; size_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_toApplicative_2184_ = lean_ctor_get(v_inst_2181_, 0);
v_toBind_2185_ = lean_ctor_get(v_inst_2181_, 1);
lean_inc_n(v_toBind_2185_, 2);
v_toPure_2186_ = lean_ctor_get(v_toApplicative_2184_, 1);
v___x_2187_ = lean_unsigned_to_nat(0u);
v_ret_2188_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2181_);
lean_inc_n(v_toPure_2186_, 2);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2189_, 0, v_toPure_2186_);
lean_closure_set(v___f_2189_, 1, v___x_2187_);
lean_closure_set(v___f_2189_, 2, v_toBind_2185_);
lean_closure_set(v___f_2189_, 3, v_eq_2182_);
lean_closure_set(v___f_2189_, 4, v_inst_2181_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2190_, 0, v_toPure_2186_);
v_sz_2191_ = lean_array_size(v_xs_2183_);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2181_, v_xs_2183_, v___f_2189_, v_sz_2191_, v___x_2192_, v_ret_2188_);
v___x_2194_ = lean_apply_4(v_toBind_2185_, lean_box(0), lean_box(0), v___x_2193_, v___f_2190_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2195_, lean_object* v_00_u03b1_2196_, lean_object* v_inst_2197_, lean_object* v_eq_2198_, lean_object* v_xs_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2197_, v_eq_2198_, v_xs_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_bs_2203_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_usize_dec_lt(v_i_2202_, v_sz_2201_);
if (v___x_2204_ == 0)
{
return v_bs_2203_;
}
else
{
lean_object* v_v_2205_; lean_object* v_indGroupInst_2206_; lean_object* v___x_2207_; lean_object* v_bs_x27_2208_; size_t v___x_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v_v_2205_ = lean_array_uget_borrowed(v_bs_2203_, v_i_2202_);
v_indGroupInst_2206_ = lean_ctor_get(v_v_2205_, 4);
lean_inc_ref(v_indGroupInst_2206_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v_bs_x27_2208_ = lean_array_uset(v_bs_2203_, v_i_2202_, v___x_2207_);
v___x_2209_ = ((size_t)1ULL);
v___x_2210_ = lean_usize_add(v_i_2202_, v___x_2209_);
v___x_2211_ = lean_array_uset(v_bs_x27_2208_, v_i_2202_, v_indGroupInst_2206_);
v_i_2202_ = v___x_2210_;
v_bs_2203_ = v___x_2211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_bs_2215_){
_start:
{
size_t v_sz_boxed_2216_; size_t v_i_boxed_2217_; lean_object* v_res_2218_; 
v_sz_boxed_2216_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2217_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2216_, v_i_boxed_2217_, v_bs_2215_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2219_, lean_object* v_a_2220_, lean_object* v_as_2221_, size_t v_i_2222_, size_t v_stop_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v___x_2229_; 
v___x_2229_ = lean_usize_dec_eq(v_i_2222_, v_stop_2223_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_array_uget_borrowed(v_as_2221_, v_i_2222_);
lean_inc_ref(v_eq_2219_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
lean_inc(v_a_2220_);
lean_inc(v___x_2230_);
v___x_2231_ = lean_apply_7(v_eq_2219_, v___x_2230_, v_a_2220_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2243_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
uint8_t v___x_2236_; 
v___x_2236_ = lean_unbox(v_a_2232_);
if (v___x_2236_ == 0)
{
size_t v___x_2237_; size_t v___x_2238_; 
lean_del_object(v___x_2234_);
lean_dec(v_a_2232_);
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2222_, v___x_2237_);
v_i_2222_ = v___x_2238_;
goto _start;
}
else
{
lean_object* v___x_2241_; 
lean_dec(v_a_2220_);
lean_dec_ref(v_eq_2219_);
if (v_isShared_2235_ == 0)
{
v___x_2241_ = v___x_2234_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2232_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_dec(v_a_2220_);
lean_dec_ref(v_eq_2219_);
return v___x_2231_;
}
}
else
{
uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_a_2220_);
lean_dec_ref(v_eq_2219_);
v___x_2244_ = 0;
v___x_2245_ = lean_box(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2247_, lean_object* v_a_2248_, lean_object* v_as_2249_, lean_object* v_i_2250_, lean_object* v_stop_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
size_t v_i_boxed_2257_; size_t v_stop_boxed_2258_; lean_object* v_res_2259_; 
v_i_boxed_2257_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_stop_boxed_2258_ = lean_unbox_usize(v_stop_2251_);
lean_dec(v_stop_2251_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2247_, v_a_2248_, v_as_2249_, v_i_boxed_2257_, v_stop_boxed_2258_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v_as_2249_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2260_, lean_object* v_a_2261_, uint8_t v_____do__lift_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
if (v_____do__lift_2262_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_array_push(v_b_2260_, v_a_2261_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v_a_2261_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_b_2260_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2273_, lean_object* v_a_2274_, lean_object* v_____do__lift_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v_____do__lift_1269__boxed_2281_; lean_object* v_res_2282_; 
v_____do__lift_1269__boxed_2281_ = lean_unbox(v_____do__lift_2275_);
v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2273_, v_a_2274_, v_____do__lift_1269__boxed_2281_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2283_, lean_object* v_as_2284_, size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_a_2294_; lean_object* v___y_2299_; uint8_t v___x_2318_; 
v___x_2318_ = lean_usize_dec_lt(v_i_2286_, v_sz_2285_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
lean_dec_ref(v_eq_2283_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_b_2287_);
return v___x_2319_;
}
else
{
lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2320_ = lean_unsigned_to_nat(0u);
v_a_2321_ = lean_array_uget_borrowed(v_as_2284_, v_i_2286_);
v___x_2322_ = lean_array_get_size(v_b_2287_);
v___x_2323_ = lean_nat_dec_lt(v___x_2320_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_inc(v_a_2321_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2287_, v_a_2321_, v___x_2323_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
v___y_2299_ = v___x_2324_;
goto v___jp_2298_;
}
else
{
if (v___x_2323_ == 0)
{
lean_object* v___x_2325_; 
lean_inc(v_a_2321_);
v___x_2325_ = lean_array_push(v_b_2287_, v_a_2321_);
v_a_2294_ = v___x_2325_;
goto v___jp_2293_;
}
else
{
size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = ((size_t)0ULL);
v___x_2327_ = lean_usize_of_nat(v___x_2322_);
lean_inc(v_a_2321_);
lean_inc_ref(v_eq_2283_);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2283_, v_a_2321_, v_b_2287_, v___x_2326_, v___x_2327_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
lean_inc(v_a_2321_);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2287_, v_a_2321_, v___x_2330_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
v___y_2299_ = v___x_2331_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_b_2287_);
lean_dec_ref(v_eq_2283_);
v_a_2332_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2328_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2328_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
v___jp_2293_:
{
size_t v___x_2295_; size_t v___x_2296_; 
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_add(v_i_2286_, v___x_2295_);
v_i_2286_ = v___x_2296_;
v_b_2287_ = v_a_2294_;
goto _start;
}
v___jp_2298_:
{
if (lean_obj_tag(v___y_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2309_; 
v_a_2300_ = lean_ctor_get(v___y_2299_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___y_2299_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2302_ = v___y_2299_;
v_isShared_2303_ = v_isSharedCheck_2309_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___y_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2309_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
if (lean_obj_tag(v_a_2300_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; 
lean_dec_ref(v_eq_2283_);
v_a_2304_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v_a_2300_, 1);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v_a_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
lean_object* v_a_2308_; 
lean_del_object(v___x_2302_);
v_a_2308_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v_a_2300_, 1);
v_a_2294_ = v_a_2308_;
goto v___jp_2293_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_eq_2283_);
v_a_2310_ = lean_ctor_get(v___y_2299_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___y_2299_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___y_2299_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___y_2299_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2340_, lean_object* v_as_2341_, lean_object* v_sz_2342_, lean_object* v_i_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
size_t v_sz_boxed_2350_; size_t v_i_boxed_2351_; lean_object* v_res_2352_; 
v_sz_boxed_2350_ = lean_unbox_usize(v_sz_2342_);
lean_dec(v_sz_2342_);
v_i_boxed_2351_ = lean_unbox_usize(v_i_2343_);
lean_dec(v_i_2343_);
v_res_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2340_, v_as_2341_, v_sz_boxed_2350_, v_i_boxed_2351_, v_b_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v_as_2341_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2353_, lean_object* v_xs_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_ret_2360_; size_t v_sz_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v_ret_2360_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2361_ = lean_array_size(v_xs_2354_);
v___x_2362_ = ((size_t)0ULL);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2353_, v_xs_2354_, v_sz_2361_, v___x_2362_, v_ret_2360_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2364_, lean_object* v_xs_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2364_, v_xs_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec_ref(v_xs_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; size_t v_sz_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2379_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2380_ = lean_array_size(v_recArgInfos_2373_);
v___x_2381_ = ((size_t)0ULL);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2380_, v___x_2381_, v_recArgInfos_2373_);
v___x_2383_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2379_, v___x_2382_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec_ref(v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2391_, lean_object* v_eq_2392_, lean_object* v_xs_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2392_, v_xs_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2400_, lean_object* v_eq_2401_, lean_object* v_xs_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2400_, v_eq_2401_, v_xs_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_xs_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2409_, lean_object* v_eq_2410_, lean_object* v_a_2411_, lean_object* v_as_2412_, size_t v_i_2413_, size_t v_stop_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2410_, v_a_2411_, v_as_2412_, v_i_2413_, v_stop_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_eq_2422_, lean_object* v_a_2423_, lean_object* v_as_2424_, lean_object* v_i_2425_, lean_object* v_stop_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
size_t v_i_boxed_2432_; size_t v_stop_boxed_2433_; lean_object* v_res_2434_; 
v_i_boxed_2432_ = lean_unbox_usize(v_i_2425_);
lean_dec(v_i_2425_);
v_stop_boxed_2433_ = lean_unbox_usize(v_stop_2426_);
lean_dec(v_stop_2426_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2421_, v_eq_2422_, v_a_2423_, v_as_2424_, v_i_boxed_2432_, v_stop_boxed_2433_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_as_2424_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2435_, lean_object* v_eq_2436_, lean_object* v_as_2437_, size_t v_sz_2438_, size_t v_i_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2436_, v_as_2437_, v_sz_2438_, v_i_2439_, v_b_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_eq_2448_, lean_object* v_as_2449_, lean_object* v_sz_2450_, lean_object* v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2450_);
lean_dec(v_sz_2450_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2447_, v_eq_2448_, v_as_2449_, v_sz_boxed_2458_, v_i_boxed_2459_, v_b_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_as_2449_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2461_, lean_object* v___y_2462_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Lean_Expr_hasMVar(v_e_2461_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_e_2461_);
return v___x_2465_;
}
else
{
lean_object* v___x_2466_; lean_object* v_mctx_2467_; lean_object* v___x_2468_; lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2471_; lean_object* v_cache_2472_; lean_object* v_zetaDeltaFVarIds_2473_; lean_object* v_postponed_2474_; lean_object* v_diag_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2484_; 
v___x_2466_ = lean_st_ref_get(v___y_2462_);
v_mctx_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_mctx_2467_);
lean_dec(v___x_2466_);
v___x_2468_ = l_Lean_instantiateMVarsCore(v_mctx_2467_, v_e_2461_);
v_fst_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_fst_2469_);
v_snd_2470_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2470_);
lean_dec_ref(v___x_2468_);
v___x_2471_ = lean_st_ref_take(v___y_2462_);
v_cache_2472_ = lean_ctor_get(v___x_2471_, 1);
v_zetaDeltaFVarIds_2473_ = lean_ctor_get(v___x_2471_, 2);
v_postponed_2474_ = lean_ctor_get(v___x_2471_, 3);
v_diag_2475_ = lean_ctor_get(v___x_2471_, 4);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2471_, 0);
lean_dec(v_unused_2485_);
v___x_2477_ = v___x_2471_;
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_diag_2475_);
lean_inc(v_postponed_2474_);
lean_inc(v_zetaDeltaFVarIds_2473_);
lean_inc(v_cache_2472_);
lean_dec(v___x_2471_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2484_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v_snd_2470_);
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_snd_2470_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_cache_2472_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_zetaDeltaFVarIds_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_postponed_2474_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_diag_2475_);
v___x_2480_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_st_ref_put(v___y_2462_, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_fst_2469_);
return v___x_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2486_, v___y_2487_);
lean_dec(v___y_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2490_, v___y_2492_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2506_ = lean_unsigned_to_nat(109u);
v___x_2507_ = lean_unsigned_to_nat(216u);
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2510_ = l_mkPanicMessageWithDecl(v___x_2509_, v___x_2508_, v___x_2507_, v___x_2506_, v___x_2505_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2511_, size_t v_sz_2512_, size_t v_i_2513_, lean_object* v_bs_2514_){
_start:
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_usize_dec_lt(v_i_2513_, v_sz_2512_);
if (v___x_2515_ == 0)
{
return v_bs_2514_;
}
else
{
lean_object* v_v_2516_; lean_object* v___x_2517_; lean_object* v_bs_x27_2518_; lean_object* v___y_2520_; lean_object* v___x_2525_; 
v_v_2516_ = lean_array_uget(v_bs_2514_, v_i_2513_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v_bs_x27_2518_ = lean_array_uset(v_bs_2514_, v_i_2513_, v___x_2517_);
v___x_2525_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2511_, v_v_2516_);
lean_dec(v_v_2516_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2527_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2526_);
v___y_2520_ = v___x_2527_;
goto v___jp_2519_;
}
else
{
lean_object* v_val_2528_; 
v_val_2528_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v___x_2525_, 1);
v___y_2520_ = v_val_2528_;
goto v___jp_2519_;
}
v___jp_2519_:
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_add(v_i_2513_, v___x_2521_);
v___x_2523_ = lean_array_uset(v_bs_x27_2518_, v_i_2513_, v___y_2520_);
v_i_2513_ = v___x_2522_;
v_bs_2514_ = v___x_2523_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2529_, lean_object* v_sz_2530_, lean_object* v_i_2531_, lean_object* v_bs_2532_){
_start:
{
size_t v_sz_boxed_2533_; size_t v_i_boxed_2534_; lean_object* v_res_2535_; 
v_sz_boxed_2533_ = lean_unbox_usize(v_sz_2530_);
lean_dec(v_sz_2530_);
v_i_boxed_2534_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2529_, v_sz_boxed_2533_, v_i_boxed_2534_, v_bs_2532_);
lean_dec_ref(v___x_2529_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2536_, size_t v_i_2537_, lean_object* v_bs_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v___x_2544_; 
v___x_2544_ = lean_usize_dec_lt(v_i_2537_, v_sz_2536_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_bs_2538_);
return v___x_2545_;
}
else
{
lean_object* v_v_2546_; lean_object* v___x_2547_; 
v_v_2546_ = lean_array_uget_borrowed(v_bs_2538_, v_i_2537_);
lean_inc(v_v_2546_);
v___x_2547_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2546_, v___y_2540_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v_bs_x27_2550_; size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = lean_unsigned_to_nat(0u);
v_bs_x27_2550_ = lean_array_uset(v_bs_2538_, v_i_2537_, v___x_2549_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_add(v_i_2537_, v___x_2551_);
v___x_2553_ = lean_array_uset(v_bs_x27_2550_, v_i_2537_, v_a_2548_);
v_i_2537_ = v___x_2552_;
v_bs_2538_ = v___x_2553_;
goto _start;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_bs_2538_);
v_a_2555_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2547_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2547_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2563_, lean_object* v_i_2564_, lean_object* v_bs_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
size_t v_sz_boxed_2571_; size_t v_i_boxed_2572_; lean_object* v_res_2573_; 
v_sz_boxed_2571_ = lean_unbox_usize(v_sz_2563_);
lean_dec(v_sz_2563_);
v_i_boxed_2572_ = lean_unbox_usize(v_i_2564_);
lean_dec(v_i_2564_);
v_res_2573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2571_, v_i_boxed_2572_, v_bs_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2573_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2574_, lean_object* v___x_2575_, lean_object* v_as_2576_, size_t v_i_2577_, size_t v_stop_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_usize_dec_eq(v_i_2577_, v_stop_2578_);
if (v___x_2579_ == 0)
{
uint8_t v___x_2580_; uint8_t v___y_2582_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2580_ = 1;
v___x_2586_ = lean_array_uget_borrowed(v_as_2576_, v_i_2577_);
v___x_2587_ = l_Lean_Expr_isFVar(v___x_2586_);
if (v___x_2587_ == 0)
{
v___y_2582_ = v_a_2574_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_nat_dec_eq(v___x_2575_, v___x_2588_);
v___y_2582_ = v___x_2589_;
goto v___jp_2581_;
}
v___jp_2581_:
{
if (v___y_2582_ == 0)
{
size_t v___x_2583_; size_t v___x_2584_; 
v___x_2583_ = ((size_t)1ULL);
v___x_2584_ = lean_usize_add(v_i_2577_, v___x_2583_);
v_i_2577_ = v___x_2584_;
goto _start;
}
else
{
return v___x_2580_;
}
}
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = 0;
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2591_, lean_object* v___x_2592_, lean_object* v_as_2593_, lean_object* v_i_2594_, lean_object* v_stop_2595_){
_start:
{
uint8_t v_a_7782__boxed_2596_; size_t v_i_boxed_2597_; size_t v_stop_boxed_2598_; uint8_t v_res_2599_; lean_object* v_r_2600_; 
v_a_7782__boxed_2596_ = lean_unbox(v_a_2591_);
v_i_boxed_2597_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_stop_boxed_2598_ = lean_unbox_usize(v_stop_2595_);
lean_dec(v_stop_2595_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7782__boxed_2596_, v___x_2592_, v_as_2593_, v_i_boxed_2597_, v_stop_boxed_2598_);
lean_dec_ref(v_as_2593_);
lean_dec(v___x_2592_);
v_r_2600_ = lean_box(v_res_2599_);
return v_r_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2601_, lean_object* v_ys_2602_, lean_object* v___x_2603_, lean_object* v_recArgInfo_2604_, lean_object* v___x_2605_, lean_object* v___x_2606_, lean_object* v_group_2607_, lean_object* v___x_2608_, lean_object* v_as_2609_, size_t v_sz_2610_, size_t v_i_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_a_2619_; uint8_t v___x_2623_; 
v___x_2623_ = lean_usize_dec_lt(v_i_2611_, v_sz_2610_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_b_2612_);
return v___x_2624_;
}
else
{
lean_object* v_snd_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2781_; 
v_snd_2625_ = lean_ctor_get(v_b_2612_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_b_2612_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v_b_2612_, 0);
lean_dec(v_unused_2782_);
v___x_2627_ = v_b_2612_;
v_isShared_2628_ = v_isSharedCheck_2781_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_snd_2625_);
lean_dec(v_b_2612_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2781_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v_next_2629_; lean_object* v_upperBound_2630_; lean_object* v___x_2631_; 
v_next_2629_ = lean_ctor_get(v_snd_2625_, 0);
lean_inc(v_next_2629_);
v_upperBound_2630_ = lean_ctor_get(v_snd_2625_, 1);
v___x_2631_ = lean_box(0);
if (lean_obj_tag(v_next_2629_) == 0)
{
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
goto v___jp_2632_;
}
else
{
lean_object* v_val_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2780_; 
v_val_2637_ = lean_ctor_get(v_next_2629_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_next_2629_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2639_ = v_next_2629_;
v_isShared_2640_ = v_isSharedCheck_2780_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_val_2637_);
lean_dec(v_next_2629_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2780_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
uint8_t v___x_2641_; 
v___x_2641_ = lean_nat_dec_lt(v_val_2637_, v_upperBound_2630_);
if (v___x_2641_ == 0)
{
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
goto v___jp_2632_;
}
else
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2777_; 
lean_inc(v_upperBound_2630_);
lean_del_object(v___x_2627_);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_snd_2625_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; lean_object* v_unused_2779_; 
v_unused_2778_ = lean_ctor_get(v_snd_2625_, 1);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_snd_2625_, 0);
lean_dec(v_unused_2779_);
v___x_2643_ = v_snd_2625_;
v_isShared_2644_ = v_isSharedCheck_2777_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v_snd_2625_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2777_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; 
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc_ref(v___x_2601_);
v___x_2645_ = lean_infer_type(v___x_2601_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2647_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = l_Lean_Meta_whnfD(v_a_2646_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v_a_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v_a_2649_ = lean_array_uget_borrowed(v_as_2609_, v_i_2611_);
v___x_2650_ = 0;
lean_inc(v_a_2649_);
v___x_2651_ = l_Lean_Meta_forallMetaTelescope(v_a_2649_, v___x_2650_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v_snd_2653_; lean_object* v_fst_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2752_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v_snd_2653_ = lean_ctor_get(v_a_2652_, 1);
v_fst_2654_ = lean_ctor_get(v_a_2652_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_a_2652_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2656_ = v_a_2652_;
v_isShared_2657_ = v_isSharedCheck_2752_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_snd_2653_);
lean_inc(v_fst_2654_);
lean_dec(v_a_2652_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2752_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2750_; 
v_snd_2658_ = lean_ctor_get(v_snd_2653_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_snd_2653_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v_snd_2653_, 0);
lean_dec(v_unused_2751_);
v___x_2660_ = v_snd_2653_;
v_isShared_2661_ = v_isSharedCheck_2750_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_dec(v_snd_2653_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2750_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2658_, v_a_2648_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_add(v_val_2637_, v___x_2664_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2665_);
v___x_2667_ = v___x_2639_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2667_);
v___x_2669_ = v___x_2643_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_upperBound_2630_);
v___x_2669_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_unbox(v_a_2663_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2672_; 
lean_dec(v_a_2663_);
lean_del_object(v___x_2656_);
lean_dec(v_fst_2654_);
lean_dec(v_val_2637_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2669_);
lean_ctor_set(v___x_2660_, 0, v___x_2631_);
v___x_2672_ = v___x_2660_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2669_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
v_a_2619_ = v___x_2672_;
goto v___jp_2618_;
}
}
else
{
size_t v_sz_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
v_sz_2674_ = lean_array_size(v_fst_2654_);
v___x_2675_ = ((size_t)0ULL);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2674_, v___x_2675_, v_fst_2654_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = lean_array_get_size(v_a_2677_);
v___x_2725_ = lean_nat_dec_lt(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_dec(v_a_2663_);
lean_del_object(v___x_2656_);
goto v___jp_2678_;
}
else
{
if (v___x_2725_ == 0)
{
lean_dec(v_a_2663_);
lean_del_object(v___x_2656_);
goto v___jp_2678_;
}
else
{
size_t v___x_2726_; uint8_t v___x_2727_; uint8_t v___x_2728_; 
v___x_2726_ = lean_usize_of_nat(v___x_2724_);
v___x_2727_ = lean_unbox(v_a_2663_);
lean_dec(v_a_2663_);
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2727_, v___x_2608_, v_a_2677_, v___x_2675_, v___x_2726_);
if (v___x_2728_ == 0)
{
lean_del_object(v___x_2656_);
goto v___jp_2678_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_a_2677_);
lean_del_object(v___x_2660_);
lean_dec(v_val_2637_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2669_);
lean_ctor_set(v___x_2656_, 0, v___x_2631_);
v___x_2730_ = v___x_2656_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v___x_2669_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
v_a_2619_ = v___x_2730_;
goto v___jp_2618_;
}
}
}
}
v___jp_2678_:
{
uint8_t v___x_2679_; 
v___x_2679_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2677_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2681_; 
lean_dec(v_a_2677_);
lean_dec(v_val_2637_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2669_);
lean_ctor_set(v___x_2660_, 0, v___x_2631_);
v___x_2681_ = v___x_2660_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2669_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v_a_2619_ = v___x_2681_;
goto v___jp_2618_;
}
}
else
{
lean_object* v___x_2683_; 
v___x_2683_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2602_, v_a_2677_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2714_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2714_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2714_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
if (lean_obj_tag(v_a_2684_) == 1)
{
lean_object* v___x_2689_; 
lean_dec_ref_known(v_a_2684_, 1);
lean_del_object(v___x_2686_);
lean_dec(v_a_2677_);
lean_dec(v_val_2637_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2669_);
lean_ctor_set(v___x_2660_, 0, v___x_2631_);
v___x_2689_ = v___x_2660_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2669_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2619_ = v___x_2689_;
goto v___jp_2618_;
}
}
else
{
lean_object* v_fnName_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2684_);
lean_dec_ref(v___x_2601_);
v_fnName_2691_ = lean_ctor_get(v_recArgInfo_2604_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_recArgInfo_2604_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2709_ = lean_ctor_get(v_recArgInfo_2604_, 5);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_recArgInfo_2604_, 4);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_recArgInfo_2604_, 3);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_recArgInfo_2604_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_recArgInfo_2604_, 1);
lean_dec(v_unused_2713_);
v___x_2693_ = v_recArgInfo_2604_;
v_isShared_2694_ = v_isSharedCheck_2708_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_fnName_2691_);
lean_dec(v_recArgInfo_2604_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2708_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
size_t v_sz_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v_sz_2695_ = lean_array_size(v_a_2677_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2603_, v_sz_2695_, v___x_2675_, v_a_2677_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 5, v_val_2637_);
lean_ctor_set(v___x_2693_, 4, v_group_2607_);
lean_ctor_set(v___x_2693_, 3, v___x_2696_);
lean_ctor_set(v___x_2693_, 2, v___x_2606_);
lean_ctor_set(v___x_2693_, 1, v___x_2605_);
v___x_2698_ = v___x_2693_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_fnName_2691_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_group_2607_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_val_2637_);
v___x_2698_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2669_);
lean_ctor_set(v___x_2660_, 0, v___x_2700_);
v___x_2702_ = v___x_2660_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2669_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2702_);
v___x_2704_ = v___x_2686_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2677_);
lean_dec_ref(v___x_2669_);
lean_del_object(v___x_2660_);
lean_dec(v_val_2637_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2715_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2683_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2683_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v___x_2669_);
lean_dec(v_a_2663_);
lean_del_object(v___x_2660_);
lean_del_object(v___x_2656_);
lean_dec(v_val_2637_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2732_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2676_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2676_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_del_object(v___x_2660_);
lean_del_object(v___x_2656_);
lean_dec(v_fst_2654_);
lean_del_object(v___x_2643_);
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
lean_dec(v_upperBound_2630_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2742_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2662_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2662_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2648_);
lean_del_object(v___x_2643_);
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
lean_dec(v_upperBound_2630_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2753_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2651_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2651_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_del_object(v___x_2643_);
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
lean_dec(v_upperBound_2630_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2761_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2647_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2647_);
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
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_del_object(v___x_2643_);
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
lean_dec(v_upperBound_2630_);
lean_dec_ref(v_group_2607_);
lean_dec(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_recArgInfo_2604_);
lean_dec_ref(v___x_2601_);
v_a_2769_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2645_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2645_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
}
v___jp_2632_:
{
lean_object* v___x_2634_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2631_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_snd_2625_);
v___x_2634_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
}
}
v___jp_2618_:
{
size_t v___x_2620_; size_t v___x_2621_; 
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_add(v_i_2611_, v___x_2620_);
v_i_2611_ = v___x_2621_;
v_b_2612_ = v_a_2619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2783_ = _args[0];
lean_object* v_ys_2784_ = _args[1];
lean_object* v___x_2785_ = _args[2];
lean_object* v_recArgInfo_2786_ = _args[3];
lean_object* v___x_2787_ = _args[4];
lean_object* v___x_2788_ = _args[5];
lean_object* v_group_2789_ = _args[6];
lean_object* v___x_2790_ = _args[7];
lean_object* v_as_2791_ = _args[8];
lean_object* v_sz_2792_ = _args[9];
lean_object* v_i_2793_ = _args[10];
lean_object* v_b_2794_ = _args[11];
lean_object* v___y_2795_ = _args[12];
lean_object* v___y_2796_ = _args[13];
lean_object* v___y_2797_ = _args[14];
lean_object* v___y_2798_ = _args[15];
lean_object* v___y_2799_ = _args[16];
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2792_);
lean_dec(v_sz_2792_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2793_);
lean_dec(v_i_2793_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2783_, v_ys_2784_, v___x_2785_, v_recArgInfo_2786_, v___x_2787_, v___x_2788_, v_group_2789_, v___x_2790_, v_as_2791_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v_as_2791_);
lean_dec(v___x_2790_);
lean_dec_ref(v___x_2785_);
lean_dec_ref(v_ys_2784_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v_ys_2805_, lean_object* v___x_2806_, lean_object* v_recArgInfo_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_group_2810_, lean_object* v_as_2811_, size_t v_sz_2812_, size_t v_i_2813_, lean_object* v_b_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_a_2821_; uint8_t v___x_2825_; 
v___x_2825_ = lean_usize_dec_lt(v_i_2813_, v_sz_2812_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2814_);
return v___x_2826_;
}
else
{
lean_object* v_snd_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2983_; 
v_snd_2827_ = lean_ctor_get(v_b_2814_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_b_2814_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_b_2814_, 0);
lean_dec(v_unused_2984_);
v___x_2829_ = v_b_2814_;
v_isShared_2830_ = v_isSharedCheck_2983_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_snd_2827_);
lean_dec(v_b_2814_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2983_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_next_2831_; lean_object* v_upperBound_2832_; lean_object* v___x_2833_; 
v_next_2831_ = lean_ctor_get(v_snd_2827_, 0);
lean_inc(v_next_2831_);
v_upperBound_2832_ = lean_ctor_get(v_snd_2827_, 1);
v___x_2833_ = lean_box(0);
if (lean_obj_tag(v_next_2831_) == 0)
{
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
goto v___jp_2834_;
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2982_; 
v_val_2839_ = lean_ctor_get(v_next_2831_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_next_2831_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2841_ = v_next_2831_;
v_isShared_2842_ = v_isSharedCheck_2982_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v_next_2831_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2982_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_nat_dec_lt(v_val_2839_, v_upperBound_2832_);
if (v___x_2843_ == 0)
{
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
goto v___jp_2834_;
}
else
{
lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2979_; 
lean_inc(v_upperBound_2832_);
lean_del_object(v___x_2829_);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_snd_2827_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; lean_object* v_unused_2981_; 
v_unused_2980_ = lean_ctor_get(v_snd_2827_, 1);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_snd_2827_, 0);
lean_dec(v_unused_2981_);
v___x_2845_ = v_snd_2827_;
v_isShared_2846_ = v_isSharedCheck_2979_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v_snd_2827_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2979_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; 
lean_inc(v___y_2818_);
lean_inc_ref(v___y_2817_);
lean_inc(v___y_2816_);
lean_inc_ref(v___y_2815_);
lean_inc_ref(v___x_2803_);
v___x_2847_ = lean_infer_type(v___x_2803_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = l_Lean_Meta_whnfD(v_a_2848_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v_a_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v_a_2851_ = lean_array_uget_borrowed(v_as_2811_, v_i_2813_);
v___x_2852_ = 0;
lean_inc(v_a_2851_);
v___x_2853_ = l_Lean_Meta_forallMetaTelescope(v_a_2851_, v___x_2852_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v_snd_2855_; lean_object* v_fst_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2954_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v_snd_2855_ = lean_ctor_get(v_a_2854_, 1);
v_fst_2856_ = lean_ctor_get(v_a_2854_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_a_2854_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2858_ = v_a_2854_;
v_isShared_2859_ = v_isSharedCheck_2954_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snd_2855_);
lean_inc(v_fst_2856_);
lean_dec(v_a_2854_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2954_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2952_; 
v_snd_2860_ = lean_ctor_get(v_snd_2855_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_snd_2855_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_snd_2855_, 0);
lean_dec(v_unused_2953_);
v___x_2862_ = v_snd_2855_;
v_isShared_2863_ = v_isSharedCheck_2952_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_dec(v_snd_2855_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2952_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2860_, v_a_2850_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = lean_unsigned_to_nat(1u);
v___x_2867_ = lean_nat_add(v_val_2839_, v___x_2866_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2867_);
v___x_2869_ = v___x_2841_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2869_);
v___x_2871_ = v___x_2845_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_upperBound_2832_);
v___x_2871_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_unbox(v_a_2865_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v_a_2865_);
lean_del_object(v___x_2858_);
lean_dec(v_fst_2856_);
lean_dec(v_val_2839_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2871_);
lean_ctor_set(v___x_2862_, 0, v___x_2833_);
v___x_2874_ = v___x_2862_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2871_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v_a_2821_ = v___x_2874_;
goto v___jp_2820_;
}
}
else
{
size_t v_sz_2876_; size_t v___x_2877_; lean_object* v___x_2878_; 
v_sz_2876_ = lean_array_size(v_fst_2856_);
v___x_2877_ = ((size_t)0ULL);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2876_, v___x_2877_, v_fst_2856_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = lean_array_get_size(v_a_2879_);
v___x_2927_ = lean_nat_dec_lt(v___x_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_dec(v_a_2865_);
lean_del_object(v___x_2858_);
goto v___jp_2880_;
}
else
{
if (v___x_2927_ == 0)
{
lean_dec(v_a_2865_);
lean_del_object(v___x_2858_);
goto v___jp_2880_;
}
else
{
size_t v___x_2928_; uint8_t v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_usize_of_nat(v___x_2926_);
v___x_2929_ = lean_unbox(v_a_2865_);
lean_dec(v_a_2865_);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2929_, v___x_2804_, v_a_2879_, v___x_2877_, v___x_2928_);
if (v___x_2930_ == 0)
{
lean_del_object(v___x_2858_);
goto v___jp_2880_;
}
else
{
lean_object* v___x_2932_; 
lean_dec(v_a_2879_);
lean_del_object(v___x_2862_);
lean_dec(v_val_2839_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2871_);
lean_ctor_set(v___x_2858_, 0, v___x_2833_);
v___x_2932_ = v___x_2858_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2871_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
v_a_2821_ = v___x_2932_;
goto v___jp_2820_;
}
}
}
}
v___jp_2880_:
{
uint8_t v___x_2881_; 
v___x_2881_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2879_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2883_; 
lean_dec(v_a_2879_);
lean_dec(v_val_2839_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2871_);
lean_ctor_set(v___x_2862_, 0, v___x_2833_);
v___x_2883_ = v___x_2862_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2871_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2821_ = v___x_2883_;
goto v___jp_2820_;
}
}
else
{
lean_object* v___x_2885_; 
v___x_2885_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2805_, v_a_2879_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2916_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
if (lean_obj_tag(v_a_2886_) == 1)
{
lean_object* v___x_2891_; 
lean_dec_ref_known(v_a_2886_, 1);
lean_del_object(v___x_2888_);
lean_dec(v_a_2879_);
lean_dec(v_val_2839_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2871_);
lean_ctor_set(v___x_2862_, 0, v___x_2833_);
v___x_2891_ = v___x_2862_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2871_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
v_a_2821_ = v___x_2891_;
goto v___jp_2820_;
}
}
else
{
lean_object* v_fnName_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2886_);
lean_dec_ref(v___x_2803_);
v_fnName_2893_ = lean_ctor_get(v_recArgInfo_2807_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_recArgInfo_2807_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; lean_object* v_unused_2912_; lean_object* v_unused_2913_; lean_object* v_unused_2914_; lean_object* v_unused_2915_; 
v_unused_2911_ = lean_ctor_get(v_recArgInfo_2807_, 5);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_recArgInfo_2807_, 4);
lean_dec(v_unused_2912_);
v_unused_2913_ = lean_ctor_get(v_recArgInfo_2807_, 3);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_recArgInfo_2807_, 2);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_recArgInfo_2807_, 1);
lean_dec(v_unused_2915_);
v___x_2895_ = v_recArgInfo_2807_;
v_isShared_2896_ = v_isSharedCheck_2910_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_fnName_2893_);
lean_dec(v_recArgInfo_2807_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2910_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
size_t v_sz_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v_sz_2897_ = lean_array_size(v_a_2879_);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2806_, v_sz_2897_, v___x_2877_, v_a_2879_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 5, v_val_2839_);
lean_ctor_set(v___x_2895_, 4, v_group_2810_);
lean_ctor_set(v___x_2895_, 3, v___x_2898_);
lean_ctor_set(v___x_2895_, 2, v___x_2809_);
lean_ctor_set(v___x_2895_, 1, v___x_2808_);
v___x_2900_ = v___x_2895_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_fnName_2893_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_group_2810_);
lean_ctor_set(v_reuseFailAlloc_2909_, 5, v_val_2839_);
v___x_2900_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2871_);
lean_ctor_set(v___x_2862_, 0, v___x_2902_);
v___x_2904_ = v___x_2862_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2871_);
v___x_2904_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2906_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2904_);
v___x_2906_ = v___x_2888_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_a_2879_);
lean_dec_ref(v___x_2871_);
lean_del_object(v___x_2862_);
lean_dec(v_val_2839_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2917_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2885_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2885_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___x_2871_);
lean_dec(v_a_2865_);
lean_del_object(v___x_2862_);
lean_del_object(v___x_2858_);
lean_dec(v_val_2839_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2934_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2878_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2878_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2862_);
lean_del_object(v___x_2858_);
lean_dec(v_fst_2856_);
lean_del_object(v___x_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec(v_upperBound_2832_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2944_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2864_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2864_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2850_);
lean_del_object(v___x_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec(v_upperBound_2832_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2955_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2853_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2853_);
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
lean_del_object(v___x_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec(v_upperBound_2832_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2963_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2849_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2849_);
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
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_del_object(v___x_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_val_2839_);
lean_dec(v_upperBound_2832_);
lean_dec_ref(v_group_2810_);
lean_dec(v___x_2809_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_recArgInfo_2807_);
lean_dec_ref(v___x_2803_);
v_a_2971_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2847_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2847_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
}
v___jp_2834_:
{
lean_object* v___x_2836_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2833_);
v___x_2836_ = v___x_2829_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_snd_2827_);
v___x_2836_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
}
}
v___jp_2820_:
{
size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = lean_usize_add(v_i_2813_, v___x_2822_);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2803_, v_ys_2805_, v___x_2806_, v_recArgInfo_2807_, v___x_2808_, v___x_2809_, v_group_2810_, v___x_2804_, v_as_2811_, v_sz_2812_, v___x_2823_, v_a_2821_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2985_ = _args[0];
lean_object* v___x_2986_ = _args[1];
lean_object* v_ys_2987_ = _args[2];
lean_object* v___x_2988_ = _args[3];
lean_object* v_recArgInfo_2989_ = _args[4];
lean_object* v___x_2990_ = _args[5];
lean_object* v___x_2991_ = _args[6];
lean_object* v_group_2992_ = _args[7];
lean_object* v_as_2993_ = _args[8];
lean_object* v_sz_2994_ = _args[9];
lean_object* v_i_2995_ = _args[10];
lean_object* v_b_2996_ = _args[11];
lean_object* v___y_2997_ = _args[12];
lean_object* v___y_2998_ = _args[13];
lean_object* v___y_2999_ = _args[14];
lean_object* v___y_3000_ = _args[15];
lean_object* v___y_3001_ = _args[16];
_start:
{
size_t v_sz_boxed_3002_; size_t v_i_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3002_ = lean_unbox_usize(v_sz_2994_);
lean_dec(v_sz_2994_);
v_i_boxed_3003_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2985_, v___x_2986_, v_ys_2987_, v___x_2988_, v_recArgInfo_2989_, v___x_2990_, v___x_2991_, v_group_2992_, v_as_2993_, v_sz_boxed_3002_, v_i_boxed_3003_, v_b_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_as_2993_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_ys_2987_);
lean_dec(v___x_2986_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3005_, lean_object* v_fixedParamPerm_3006_, lean_object* v_xs_3007_, lean_object* v___x_3008_, lean_object* v_recArgPos_3009_, lean_object* v_a_3010_, lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_ys_3013_, lean_object* v_x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_toIndGroupInfo_3020_; lean_object* v_all_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3059_; 
v_toIndGroupInfo_3020_ = lean_ctor_get(v_group_3005_, 0);
lean_inc_ref(v_toIndGroupInfo_3020_);
v_all_3021_ = lean_ctor_get(v_toIndGroupInfo_3020_, 0);
lean_inc_ref(v_ys_3013_);
lean_inc_ref(v_fixedParamPerm_3006_);
v___x_3022_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3006_, v_xs_3007_, v_ys_3013_);
v___x_3023_ = lean_array_get(v___x_3008_, v___x_3022_, v_recArgPos_3009_);
v___x_3024_ = lean_array_get_size(v_all_3021_);
v___x_3025_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3020_);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_toIndGroupInfo_3020_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; lean_object* v_unused_3061_; 
v_unused_3060_ = lean_ctor_get(v_toIndGroupInfo_3020_, 1);
lean_dec(v_unused_3060_);
v_unused_3061_ = lean_ctor_get(v_toIndGroupInfo_3020_, 0);
lean_dec(v_unused_3061_);
v___x_3027_ = v_toIndGroupInfo_3020_;
v_isShared_3028_ = v_isSharedCheck_3059_;
goto v_resetjp_3026_;
}
else
{
lean_dec(v_toIndGroupInfo_3020_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3059_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3024_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
lean_ctor_set(v___x_3027_, 0, v___x_3029_);
v___x_3031_ = v___x_3027_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___x_3025_);
v___x_3031_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; size_t v_sz_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
v_sz_3034_ = lean_array_size(v_a_3010_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3023_, v___x_3011_, v_ys_3013_, v___x_3022_, v___x_3012_, v_fixedParamPerm_3006_, v_recArgPos_3009_, v_group_3005_, v_a_3010_, v_sz_3034_, v___x_3035_, v___x_3033_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec_ref(v___x_3022_);
lean_dec_ref(v_ys_3013_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3049_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_fst_3041_; 
v_fst_3041_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_fst_3041_);
lean_dec(v_a_3037_);
if (lean_obj_tag(v_fst_3041_) == 0)
{
lean_object* v___x_3043_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3032_);
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3032_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v_val_3045_; lean_object* v___x_3047_; 
v_val_3045_ = lean_ctor_get(v_fst_3041_, 0);
lean_inc(v_val_3045_);
lean_dec_ref_known(v_fst_3041_, 1);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_val_3045_);
v___x_3047_ = v___x_3039_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_val_3045_);
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
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3036_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3036_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3062_, lean_object* v_fixedParamPerm_3063_, lean_object* v_xs_3064_, lean_object* v___x_3065_, lean_object* v_recArgPos_3066_, lean_object* v_a_3067_, lean_object* v___x_3068_, lean_object* v___x_3069_, lean_object* v_ys_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3062_, v_fixedParamPerm_3063_, v_xs_3064_, v___x_3065_, v_recArgPos_3066_, v_a_3067_, v___x_3068_, v___x_3069_, v_ys_3070_, v_x_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_x_3071_);
lean_dec(v___x_3068_);
lean_dec_ref(v_a_3067_);
lean_dec_ref(v___x_3065_);
lean_dec_ref(v_xs_3064_);
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
lean_object* v___x_3100_; lean_object* v_fixedParamPerm_3101_; lean_object* v_recArgPos_3102_; lean_object* v_indGroupInst_3103_; lean_object* v___x_3104_; 
v___x_3100_ = lean_array_uget_borrowed(v_as_3082_, v_i_3083_);
v_fixedParamPerm_3101_ = lean_ctor_get(v___x_3100_, 1);
v_recArgPos_3102_ = lean_ctor_get(v___x_3100_, 2);
v_indGroupInst_3103_ = lean_ctor_get(v___x_3100_, 4);
lean_inc_ref(v_indGroupInst_3103_);
lean_inc_ref(v_group_3078_);
v___x_3104_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3078_, v_indGroupInst_3103_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; uint8_t v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = lean_unbox(v_a_3105_);
lean_dec(v_a_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3107_ = lean_array_get_size(v_a_3079_);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = lean_nat_dec_eq(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___f_3111_; lean_object* v___x_3112_; 
v___x_3110_ = l_Lean_instInhabitedExpr;
lean_inc(v___x_3100_);
lean_inc_ref(v_a_3079_);
lean_inc(v_recArgPos_3102_);
lean_inc_ref(v_xs_3080_);
lean_inc_ref(v_fixedParamPerm_3101_);
lean_inc_ref(v_group_3078_);
v___f_3111_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3111_, 0, v_group_3078_);
lean_closure_set(v___f_3111_, 1, v_fixedParamPerm_3101_);
lean_closure_set(v___f_3111_, 2, v_xs_3080_);
lean_closure_set(v___f_3111_, 3, v___x_3110_);
lean_closure_set(v___f_3111_, 4, v_recArgPos_3102_);
lean_closure_set(v___f_3111_, 5, v_a_3079_);
lean_closure_set(v___f_3111_, 6, v___x_3107_);
lean_closure_set(v___f_3111_, 7, v___x_3100_);
lean_inc_ref(v_value_3081_);
v___x_3112_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3081_, v___f_3111_, v___x_3109_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
if (lean_obj_tag(v_a_3113_) == 0)
{
v_a_3092_ = v_b_3085_;
goto v___jp_3091_;
}
else
{
lean_object* v_val_3114_; 
v_val_3114_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_val_3114_);
lean_dec_ref_known(v_a_3113_, 1);
v_val_3097_ = v_val_3114_;
goto v___jp_3096_;
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v_b_3085_);
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v_a_3115_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3112_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3112_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
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
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_b_3085_);
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v_a_3123_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3104_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3104_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v___x_3131_; 
lean_dec_ref(v_value_3081_);
lean_dec_ref(v_xs_3080_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_group_3078_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_b_3085_);
return v___x_3131_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3132_, lean_object* v_a_3133_, lean_object* v_xs_3134_, lean_object* v_value_3135_, lean_object* v_as_3136_, lean_object* v_i_3137_, lean_object* v_stop_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
size_t v_i_boxed_3145_; size_t v_stop_boxed_3146_; lean_object* v_res_3147_; 
v_i_boxed_3145_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_stop_boxed_3146_ = lean_unbox_usize(v_stop_3138_);
lean_dec(v_stop_3138_);
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3132_, v_a_3133_, v_xs_3134_, v_value_3135_, v_as_3136_, v_i_boxed_3145_, v_stop_boxed_3146_, v_b_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v_as_3136_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3148_, lean_object* v_a_3149_, lean_object* v_xs_3150_, lean_object* v_value_3151_, lean_object* v_as_3152_, lean_object* v_start_3153_, lean_object* v_stop_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3161_ = lean_nat_dec_lt(v_start_3153_, v_stop_3154_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
lean_dec_ref(v_value_3151_);
lean_dec_ref(v_xs_3150_);
lean_dec_ref(v_a_3149_);
lean_dec_ref(v_group_3148_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
return v___x_3162_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_array_get_size(v_as_3152_);
v___x_3164_ = lean_nat_dec_le(v_stop_3154_, v___x_3163_);
if (v___x_3164_ == 0)
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_nat_dec_lt(v_start_3153_, v___x_3163_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v_value_3151_);
lean_dec_ref(v_xs_3150_);
lean_dec_ref(v_a_3149_);
lean_dec_ref(v_group_3148_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3160_);
return v___x_3166_;
}
else
{
size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_usize_of_nat(v_start_3153_);
v___x_3168_ = lean_usize_of_nat(v___x_3163_);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3148_, v_a_3149_, v_xs_3150_, v_value_3151_, v_as_3152_, v___x_3167_, v___x_3168_, v___x_3160_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
return v___x_3169_;
}
}
else
{
size_t v___x_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_usize_of_nat(v_start_3153_);
v___x_3171_ = lean_usize_of_nat(v_stop_3154_);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3148_, v_a_3149_, v_xs_3150_, v_value_3151_, v_as_3152_, v___x_3170_, v___x_3171_, v___x_3160_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3173_, lean_object* v_a_3174_, lean_object* v_xs_3175_, lean_object* v_value_3176_, lean_object* v_as_3177_, lean_object* v_start_3178_, lean_object* v_stop_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3173_, v_a_3174_, v_xs_3175_, v_value_3176_, v_as_3177_, v_start_3178_, v_stop_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v_stop_3179_);
lean_dec(v_start_3178_);
lean_dec_ref(v_as_3177_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3186_, lean_object* v_xs_3187_, lean_object* v_value_3188_, lean_object* v_recArgInfos_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3195_; 
lean_inc_ref(v_group_3186_);
v___x_3195_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3186_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = lean_unsigned_to_nat(0u);
v___x_3198_ = lean_array_get_size(v_recArgInfos_3189_);
v___x_3199_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3186_, v_a_3196_, v_xs_3187_, v_value_3188_, v_recArgInfos_3189_, v___x_3197_, v___x_3198_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
return v___x_3199_;
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_value_3188_);
lean_dec_ref(v_xs_3187_);
lean_dec_ref(v_group_3186_);
v_a_3200_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3195_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3195_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3208_, lean_object* v_xs_3209_, lean_object* v_value_3210_, lean_object* v_recArgInfos_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Elab_Structural_argsInGroup(v_group_3208_, v_xs_3209_, v_value_3210_, v_recArgInfos_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec_ref(v_recArgInfos_3211_);
return v_res_3217_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_unsigned_to_nat(10u);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3221_, lean_object* v_i_3222_, lean_object* v_acc_3223_){
_start:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = lean_array_get_size(v_xss_3221_);
v___x_3225_ = lean_nat_dec_lt(v_i_3222_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_unsigned_to_nat(1u);
v___x_3227_ = lean_mk_empty_array_with_capacity(v___x_3226_);
v___x_3228_ = lean_array_push(v___x_3227_, v_acc_3223_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3229_ = lean_array_fget_borrowed(v_xss_3221_, v_i_3222_);
v___x_3230_ = lean_unsigned_to_nat(0u);
v___x_3231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3232_ = lean_array_get_size(v___x_3229_);
v___x_3233_ = lean_nat_dec_lt(v___x_3230_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_dec_ref(v_acc_3223_);
return v___x_3231_;
}
else
{
size_t v___x_3234_; size_t v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = ((size_t)0ULL);
v___x_3235_ = lean_usize_of_nat(v___x_3232_);
v___x_3236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3222_, v_acc_3223_, v_xss_3221_, v___x_3229_, v___x_3234_, v___x_3235_, v___x_3231_);
return v___x_3236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3237_, lean_object* v_acc_3238_, lean_object* v_xss_3239_, lean_object* v_as_3240_, size_t v_i_3241_, size_t v_stop_3242_, lean_object* v_b_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_eq(v_i_3241_, v_stop_3242_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; size_t v___x_3251_; size_t v___x_3252_; 
v___x_3245_ = lean_array_uget_borrowed(v_as_3240_, v_i_3241_);
v___x_3246_ = lean_unsigned_to_nat(1u);
v___x_3247_ = lean_nat_add(v_i_3237_, v___x_3246_);
lean_inc(v___x_3245_);
lean_inc_ref(v_acc_3238_);
v___x_3248_ = lean_array_push(v_acc_3238_, v___x_3245_);
v___x_3249_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3239_, v___x_3247_, v___x_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = l_Array_append___redArg(v_b_3243_, v___x_3249_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3241_, v___x_3251_);
v_i_3241_ = v___x_3252_;
v_b_3243_ = v___x_3250_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3238_);
return v_b_3243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3254_, lean_object* v_acc_3255_, lean_object* v_xss_3256_, lean_object* v_as_3257_, lean_object* v_i_3258_, lean_object* v_stop_3259_, lean_object* v_b_3260_){
_start:
{
size_t v_i_boxed_3261_; size_t v_stop_boxed_3262_; lean_object* v_res_3263_; 
v_i_boxed_3261_ = lean_unbox_usize(v_i_3258_);
lean_dec(v_i_3258_);
v_stop_boxed_3262_ = lean_unbox_usize(v_stop_3259_);
lean_dec(v_stop_3259_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3254_, v_acc_3255_, v_xss_3256_, v_as_3257_, v_i_boxed_3261_, v_stop_boxed_3262_, v_b_3260_);
lean_dec_ref(v_as_3257_);
lean_dec_ref(v_xss_3256_);
lean_dec(v_i_3254_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3264_, lean_object* v_i_3265_, lean_object* v_acc_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3264_, v_i_3265_, v_acc_3266_);
lean_dec(v_i_3265_);
lean_dec_ref(v_xss_3264_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3268_, lean_object* v_xss_3269_, lean_object* v_i_3270_, lean_object* v_acc_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3269_, v_i_3270_, v_acc_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_xss_3274_, lean_object* v_i_3275_, lean_object* v_acc_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3273_, v_xss_3274_, v_i_3275_, v_acc_3276_);
lean_dec(v_i_3275_);
lean_dec_ref(v_xss_3274_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3278_, lean_object* v_i_3279_, lean_object* v_acc_3280_, lean_object* v_xss_3281_, lean_object* v_as_3282_, size_t v_i_3283_, size_t v_stop_3284_, lean_object* v_b_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3279_, v_acc_3280_, v_xss_3281_, v_as_3282_, v_i_3283_, v_stop_3284_, v_b_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_i_3288_, lean_object* v_acc_3289_, lean_object* v_xss_3290_, lean_object* v_as_3291_, lean_object* v_i_3292_, lean_object* v_stop_3293_, lean_object* v_b_3294_){
_start:
{
size_t v_i_boxed_3295_; size_t v_stop_boxed_3296_; lean_object* v_res_3297_; 
v_i_boxed_3295_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_stop_boxed_3296_ = lean_unbox_usize(v_stop_3293_);
lean_dec(v_stop_3293_);
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3287_, v_i_3288_, v_acc_3289_, v_xss_3290_, v_as_3291_, v_i_boxed_3295_, v_stop_boxed_3296_, v_b_3294_);
lean_dec_ref(v_as_3291_);
lean_dec_ref(v_xss_3290_);
lean_dec(v_i_3288_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3298_, size_t v_i_3299_, size_t v_stop_3300_, lean_object* v_b_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_usize_dec_eq(v_i_3299_, v_stop_3300_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; size_t v___x_3306_; size_t v___x_3307_; 
v___x_3303_ = lean_array_uget_borrowed(v_as_3298_, v_i_3299_);
v___x_3304_ = lean_array_get_size(v___x_3303_);
v___x_3305_ = lean_nat_mul(v_b_3301_, v___x_3304_);
lean_dec(v_b_3301_);
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3299_, v___x_3306_);
v_i_3299_ = v___x_3307_;
v_b_3301_ = v___x_3305_;
goto _start;
}
else
{
return v_b_3301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3309_, lean_object* v_i_3310_, lean_object* v_stop_3311_, lean_object* v_b_3312_){
_start:
{
size_t v_i_boxed_3313_; size_t v_stop_boxed_3314_; lean_object* v_res_3315_; 
v_i_boxed_3313_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_stop_boxed_3314_ = lean_unbox_usize(v_stop_3311_);
lean_dec(v_stop_3311_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3309_, v_i_boxed_3313_, v_stop_boxed_3314_, v_b_3312_);
lean_dec_ref(v_as_3309_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3316_){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___y_3321_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3317_ = lean_unsigned_to_nat(10u);
v___x_3318_ = lean_unsigned_to_nat(1u);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3327_ = lean_array_get_size(v_xss_3316_);
v___x_3328_ = lean_nat_dec_lt(v___x_3319_, v___x_3327_);
if (v___x_3328_ == 0)
{
v___y_3321_ = v___x_3318_;
goto v___jp_3320_;
}
else
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_nat_dec_le(v___x_3327_, v___x_3327_);
if (v___x_3329_ == 0)
{
if (v___x_3328_ == 0)
{
v___y_3321_ = v___x_3318_;
goto v___jp_3320_;
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3327_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3316_, v___x_3330_, v___x_3331_, v___x_3318_);
v___y_3321_ = v___x_3332_;
goto v___jp_3320_;
}
}
else
{
size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = lean_usize_of_nat(v___x_3327_);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3316_, v___x_3333_, v___x_3334_, v___x_3318_);
v___y_3321_ = v___x_3335_;
goto v___jp_3320_;
}
}
v___jp_3320_:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_nat_dec_lt(v___x_3317_, v___y_3321_);
lean_dec(v___y_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3324_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3316_, v___x_3319_, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
return v___x_3326_;
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
lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_a_3509_ = lean_array_uget_borrowed(v_as_3409_, v_i_3411_);
v___x_3510_ = lean_array_fget_borrowed(v_array_3485_, v_start_3486_);
lean_inc(v___x_3510_);
lean_inc_ref(v_xs_3408_);
lean_inc(v_a_3509_);
v___x_3511_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3509_, v___x_3463_, v_xs_3408_, v___x_3510_, v___x_3488_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v_fst_3513_; lean_object* v_snd_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3539_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v_fst_3513_ = lean_ctor_get(v_a_3512_, 0);
v_snd_3514_ = lean_ctor_get(v_a_3512_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3512_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3516_ = v_a_3512_;
v_isShared_3517_ = v_isSharedCheck_3539_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_snd_3514_);
lean_inc(v_fst_3513_);
lean_dec(v_a_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3539_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = lean_nat_add(v_start_3486_, v___x_3464_);
lean_dec(v_start_3486_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3518_);
v___x_3520_ = v___x_3507_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_array_3485_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_stop_3487_);
v___x_3520_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_fst_3424_);
lean_ctor_set(v___x_3521_, 1, v_snd_3514_);
v___x_3522_ = lean_array_push(v_fst_3428_, v_fst_3513_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3467_);
lean_ctor_set(v___x_3516_, 0, v___x_3491_);
v___x_3524_ = v___x_3516_;
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
lean_ctor_set(v___x_3438_, 0, v___x_3520_);
v___x_3526_ = v___x_3438_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3520_);
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
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_3507_);
lean_dec_ref(v___x_3491_);
lean_dec(v_stop_3487_);
lean_dec(v_start_3486_);
lean_dec_ref(v_array_3485_);
lean_dec_ref(v___x_3467_);
lean_del_object(v___x_3438_);
lean_del_object(v___x_3434_);
lean_del_object(v___x_3430_);
lean_dec(v_fst_3428_);
lean_dec(v_fst_3424_);
lean_dec_ref(v_xs_3408_);
v_a_3540_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3511_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3511_);
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
lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_a_3665_ = lean_array_uget_borrowed(v_as_3638_, v_i_3640_);
v___x_3666_ = lean_array_fget_borrowed(v_array_3654_, v_start_3655_);
lean_inc(v_a_3665_);
lean_inc_ref(v_xs_3637_);
lean_inc_ref(v_a_3636_);
v___x_3667_ = l_Lean_Elab_Structural_argsInGroup(v_a_3636_, v_xs_3637_, v_a_3665_, v___x_3666_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_nat_add(v_start_3655_, v___x_3669_);
lean_dec(v_start_3655_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v___x_3670_);
v___x_3672_ = v___x_3663_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_array_3654_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_stop_3656_);
v___x_3672_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = lean_array_push(v_fst_3650_, v_a_3668_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v___x_3672_);
lean_ctor_set(v___x_3652_, 0, v___x_3673_);
v___x_3675_ = v___x_3652_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3672_);
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
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3663_);
lean_dec(v_stop_3656_);
lean_dec(v_start_3655_);
lean_dec_ref(v_array_3654_);
lean_del_object(v___x_3652_);
lean_dec(v_fst_3650_);
lean_dec_ref(v_xs_3637_);
lean_dec_ref(v_a_3636_);
v_a_3681_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3667_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3667_);
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
lean_object* v___x_3748_; lean_object* v_recArgInfoss_3749_; lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; size_t v_sz_3754_; size_t v___x_3755_; lean_object* v___x_3756_; 
v___x_3748_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3750_ = lean_array_uget_borrowed(v_as_3732_, v_i_3734_);
v___x_3751_ = lean_array_get_size(v___x_3728_);
lean_inc_ref(v___x_3728_);
v___x_3752_ = l_Array_toSubarray___redArg(v___x_3728_, v___x_3748_, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v_recArgInfoss_3749_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v_sz_3754_ = lean_array_size(v_values_3729_);
v___x_3755_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3730_);
lean_inc(v_a_3750_);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3750_, v_xs_3730_, v_values_3729_, v_sz_3754_, v___x_3755_, v___x_3753_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v_fst_3758_; lean_object* v_snd_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3817_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v_fst_3758_ = lean_ctor_get(v_b_3735_, 0);
v_snd_3759_ = lean_ctor_get(v_b_3735_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_b_3735_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3761_ = v_b_3735_;
v_isShared_3762_ = v_isSharedCheck_3817_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_snd_3759_);
lean_inc(v_fst_3758_);
lean_dec(v_b_3735_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3817_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v_fst_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3815_; 
v_fst_3763_ = lean_ctor_get(v_a_3757_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_a_3757_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_a_3757_, 1);
lean_dec(v_unused_3816_);
v___x_3765_ = v_a_3757_;
v_isShared_3766_ = v_isSharedCheck_3815_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_fst_3763_);
lean_dec(v_a_3757_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3815_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3763_, v___x_3748_);
if (lean_obj_tag(v___x_3767_) == 1)
{
lean_object* v_val_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_dec(v_fst_3763_);
v_val_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3750_);
v___x_3771_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3750_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 7);
lean_ctor_set(v___x_3761_, 1, v___x_3771_);
lean_ctor_set(v___x_3761_, 0, v___x_3770_);
v___x_3773_ = v___x_3761_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_array_get_borrowed(v___x_3769_, v_fnNames_3731_, v_val_3768_);
lean_dec(v_val_3768_);
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
lean_ctor_set(v___x_3781_, 0, v_fst_3758_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v_snd_3759_);
lean_ctor_set(v___x_3765_, 0, v___x_3781_);
v___x_3783_ = v___x_3765_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3759_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v_a_3742_ = v___x_3783_;
goto v___jp_3741_;
}
}
}
else
{
lean_object* v___x_3786_; 
lean_dec(v___x_3767_);
v___x_3786_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3763_);
lean_dec(v_fst_3763_);
if (lean_obj_tag(v___x_3786_) == 1)
{
lean_object* v_val_3787_; size_t v_sz_3788_; lean_object* v___x_3789_; 
lean_del_object(v___x_3761_);
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_val_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v_sz_3788_ = lean_array_size(v_val_3787_);
lean_inc(v_a_3750_);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3750_, v_val_3787_, v_sz_3788_, v___x_3755_, v_snd_3759_);
lean_dec(v_val_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v_a_3790_);
lean_ctor_set(v___x_3765_, 0, v_fst_3758_);
v___x_3792_ = v___x_3765_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fst_3758_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_a_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
v_a_3742_ = v___x_3792_;
goto v___jp_3741_;
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3765_);
lean_dec(v_fst_3758_);
lean_dec_ref(v_xs_3730_);
lean_dec_ref(v___x_3728_);
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
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
lean_dec(v___x_3786_);
v___x_3802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3750_);
v___x_3803_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3750_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 7);
lean_ctor_set(v___x_3761_, 1, v___x_3803_);
lean_ctor_set(v___x_3761_, 0, v___x_3802_);
v___x_3805_ = v___x_3761_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_fst_3758_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v_snd_3759_);
lean_ctor_set(v___x_3765_, 0, v___x_3810_);
v___x_3812_ = v___x_3765_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_snd_3759_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
v_a_3742_ = v___x_3812_;
goto v___jp_3741_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v_b_3735_);
lean_dec_ref(v_xs_3730_);
lean_dec_ref(v___x_3728_);
v_a_3818_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3756_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3756_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3826_, lean_object* v_values_3827_, lean_object* v_xs_3828_, lean_object* v_fnNames_3829_, lean_object* v_as_3830_, lean_object* v_sz_3831_, lean_object* v_i_3832_, lean_object* v_b_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
size_t v_sz_boxed_3839_; size_t v_i_boxed_3840_; lean_object* v_res_3841_; 
v_sz_boxed_3839_ = lean_unbox_usize(v_sz_3831_);
lean_dec(v_sz_3831_);
v_i_boxed_3840_ = lean_unbox_usize(v_i_3832_);
lean_dec(v_i_3832_);
v_res_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3826_, v_values_3827_, v_xs_3828_, v_fnNames_3829_, v_as_3830_, v_sz_boxed_3839_, v_i_boxed_3840_, v_b_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v_as_3830_);
lean_dec_ref(v_fnNames_3829_);
lean_dec_ref(v_values_3827_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3842_, lean_object* v___x_3843_, lean_object* v_values_3844_, lean_object* v_fnNames_3845_, lean_object* v_as_3846_, size_t v_sz_3847_, size_t v_i_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_a_3856_; uint8_t v___x_3860_; 
v___x_3860_ = lean_usize_dec_lt(v_i_3848_, v_sz_3847_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v___x_3843_);
lean_dec_ref(v_xs_3842_);
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_b_3849_);
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; lean_object* v_recArgInfoss_3863_; lean_object* v_a_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; size_t v_sz_3868_; size_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3862_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3864_ = lean_array_uget_borrowed(v_as_3846_, v_i_3848_);
v___x_3865_ = lean_array_get_size(v___x_3843_);
lean_inc_ref(v___x_3843_);
v___x_3866_ = l_Array_toSubarray___redArg(v___x_3843_, v___x_3862_, v___x_3865_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_recArgInfoss_3863_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v_sz_3868_ = lean_array_size(v_values_3844_);
v___x_3869_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3842_);
lean_inc(v_a_3864_);
v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3864_, v_xs_3842_, v_values_3844_, v_sz_3868_, v___x_3869_, v___x_3867_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_fst_3872_; lean_object* v_snd_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3931_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_fst_3872_ = lean_ctor_get(v_b_3849_, 0);
v_snd_3873_ = lean_ctor_get(v_b_3849_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_b_3849_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3875_ = v_b_3849_;
v_isShared_3876_ = v_isSharedCheck_3931_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_snd_3873_);
lean_inc(v_fst_3872_);
lean_dec(v_b_3849_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3931_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v_fst_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3929_; 
v_fst_3877_ = lean_ctor_get(v_a_3871_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_a_3871_, 1);
lean_dec(v_unused_3930_);
v___x_3879_ = v_a_3871_;
v_isShared_3880_ = v_isSharedCheck_3929_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_fst_3877_);
lean_dec(v_a_3871_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3929_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3877_, v___x_3862_);
if (lean_obj_tag(v___x_3881_) == 1)
{
lean_object* v_val_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_dec(v_fst_3877_);
v_val_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3864_);
v___x_3885_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3864_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 7);
lean_ctor_set(v___x_3875_, 1, v___x_3885_);
lean_ctor_set(v___x_3875_, 0, v___x_3884_);
v___x_3887_ = v___x_3875_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = lean_array_get_borrowed(v___x_3883_, v_fnNames_3845_, v_val_3882_);
lean_dec(v_val_3882_);
lean_inc(v___x_3890_);
v___x_3891_ = l_Lean_MessageData_ofName(v___x_3890_);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3889_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v_fst_3872_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_snd_3873_);
lean_ctor_set(v___x_3879_, 0, v___x_3895_);
v___x_3897_ = v___x_3879_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_snd_3873_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
v_a_3856_ = v___x_3897_;
goto v___jp_3855_;
}
}
}
else
{
lean_object* v___x_3900_; 
lean_dec(v___x_3881_);
v___x_3900_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3877_);
lean_dec(v_fst_3877_);
if (lean_obj_tag(v___x_3900_) == 1)
{
lean_object* v_val_3901_; size_t v_sz_3902_; lean_object* v___x_3903_; 
lean_del_object(v___x_3875_);
v_val_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v_sz_3902_ = lean_array_size(v_val_3901_);
lean_inc(v_a_3864_);
v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3864_, v_val_3901_, v_sz_3902_, v___x_3869_, v_snd_3873_);
lean_dec(v_val_3901_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_a_3904_);
lean_ctor_set(v___x_3879_, 0, v_fst_3872_);
v___x_3906_ = v___x_3879_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_fst_3872_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_a_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
v_a_3856_ = v___x_3906_;
goto v___jp_3855_;
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_del_object(v___x_3879_);
lean_dec(v_fst_3872_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v_xs_3842_);
v_a_3908_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3903_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3903_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec(v___x_3900_);
v___x_3916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3864_);
v___x_3917_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3864_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 7);
lean_ctor_set(v___x_3875_, 1, v___x_3917_);
lean_ctor_set(v___x_3875_, 0, v___x_3916_);
v___x_3919_ = v___x_3875_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3922_, 0, v_fst_3872_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_snd_3873_);
lean_ctor_set(v___x_3879_, 0, v___x_3924_);
v___x_3926_ = v___x_3879_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_snd_3873_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v_a_3856_ = v___x_3926_;
goto v___jp_3855_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_b_3849_);
lean_dec_ref(v___x_3843_);
lean_dec_ref(v_xs_3842_);
v_a_3932_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3870_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3870_);
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
v___jp_3855_:
{
size_t v___x_3857_; size_t v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = ((size_t)1ULL);
v___x_3858_ = lean_usize_add(v_i_3848_, v___x_3857_);
v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3843_, v_values_3844_, v_xs_3842_, v_fnNames_3845_, v_as_3846_, v_sz_3847_, v___x_3858_, v_a_3856_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3940_, lean_object* v___x_3941_, lean_object* v_values_3942_, lean_object* v_fnNames_3943_, lean_object* v_as_3944_, lean_object* v_sz_3945_, lean_object* v_i_3946_, lean_object* v_b_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3945_);
lean_dec(v_sz_3945_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3946_);
lean_dec(v_i_3946_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3940_, v___x_3941_, v_values_3942_, v_fnNames_3943_, v_as_3944_, v_sz_boxed_3953_, v_i_boxed_3954_, v_b_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v_as_3944_);
lean_dec_ref(v_fnNames_3943_);
lean_dec_ref(v_values_3942_);
return v_res_3955_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3960_ = l_Lean_MessageData_ofFormat(v___x_3959_);
return v___x_3960_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3963_ = l_Lean_stringToMessageData(v___x_3962_);
return v___x_3963_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
return v___x_3968_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_box(1);
v___x_3970_ = l_Lean_MessageData_ofFormat(v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3971_, lean_object* v_fixedParamPerms_3972_, lean_object* v_xs_3973_, lean_object* v_values_3974_, lean_object* v_termMeasure_x3fs_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___x_3981_; lean_object* v_recArgInfoss_3982_; lean_object* v___x_3983_; lean_object* v_perms_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v_report_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; size_t v_sz_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
v___x_3981_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3983_ = lean_array_get_size(v_values_3974_);
v_perms_3984_ = lean_ctor_get(v_fixedParamPerms_3972_, 1);
lean_inc_ref(v_perms_3984_);
lean_dec_ref(v_fixedParamPerms_3972_);
lean_inc_ref(v_values_3974_);
v___x_3985_ = l_Array_toSubarray___redArg(v_values_3974_, v___x_3981_, v___x_3983_);
v___x_3986_ = lean_array_get_size(v_termMeasure_x3fs_3975_);
v_report_3987_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3988_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3975_, v___x_3981_, v___x_3986_);
v___x_3989_ = lean_array_get_size(v_perms_3984_);
v___x_3990_ = l_Array_toSubarray___redArg(v_perms_3984_, v___x_3981_, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3988_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3985_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_recArgInfoss_3982_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v_report_3987_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v_sz_3995_ = lean_array_size(v_fnNames_3971_);
v___x_3996_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3973_);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3973_, v_fnNames_3971_, v_sz_3995_, v___x_3996_, v___x_3994_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v_snd_3999_; lean_object* v_toCold_4000_; lean_object* v_options_4001_; lean_object* v_fst_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4140_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v_snd_3999_ = lean_ctor_get(v_a_3998_, 1);
lean_inc(v_snd_3999_);
v_toCold_4000_ = lean_ctor_get(v_a_3978_, 0);
v_options_4001_ = lean_ctor_get(v_toCold_4000_, 2);
v_fst_4002_ = lean_ctor_get(v_a_3998_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_a_3998_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v_a_3998_, 1);
lean_dec(v_unused_4141_);
v___x_4004_ = v_a_3998_;
v_isShared_4005_ = v_isSharedCheck_4140_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_fst_4002_);
lean_dec(v_a_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4140_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v_fst_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4138_; 
v_fst_4006_ = lean_ctor_get(v_snd_3999_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_snd_3999_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_snd_3999_, 1);
lean_dec(v_unused_4139_);
v___x_4008_ = v_snd_3999_;
v_isShared_4009_ = v_isSharedCheck_4138_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_fst_4006_);
lean_dec(v_snd_3999_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4138_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_inheritedTraceOptions_4010_; uint8_t v_hasTrace_4011_; size_t v_sz_4012_; lean_object* v___x_4013_; lean_object* v___y_4015_; lean_object* v_report_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___x_4063_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; 
v_inheritedTraceOptions_4010_ = lean_ctor_get(v_toCold_4000_, 11);
v_hasTrace_4011_ = lean_ctor_get_uint8(v_options_4001_, sizeof(void*)*1);
v_sz_4012_ = lean_array_size(v_fst_4006_);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4012_, v___x_3996_, v_fst_4006_);
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4011_ == 0)
{
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4113_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4010_, v_options_4001_, v___x_4112_);
if (v___x_4113_ == 0)
{
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4114_; lean_object* v___y_4116_; lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4114_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4133_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4134_ = lean_array_get_size(v___x_4013_);
v___x_4135_ = lean_nat_dec_lt(v___x_3981_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4116_ = v___x_4133_;
goto v___jp_4115_;
}
else
{
size_t v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_usize_of_nat(v___x_4134_);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4013_, v___x_3996_, v___x_4136_, v___x_4133_);
v___y_4116_ = v___x_4137_;
goto v___jp_4115_;
}
v___jp_4115_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4117_ = lean_array_to_list(v___y_4116_);
v___x_4118_ = lean_box(0);
v___x_4119_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4117_, v___x_4118_);
v___x_4120_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4121_ = l_Lean_MessageData_joinSep(v___x_4119_, v___x_4120_);
v___x_4122_ = l_Lean_indentD(v___x_4121_);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4114_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4063_, v___x_4123_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_dec_ref_known(v___x_4124_, 1);
v___y_4103_ = v_a_3976_;
v___y_4104_ = v_a_3977_;
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
goto v___jp_4102_;
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v___x_4013_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4004_);
lean_dec(v_fst_4002_);
lean_dec_ref(v_values_3974_);
lean_dec_ref(v_xs_3973_);
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
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
}
v___jp_4014_:
{
lean_object* v___x_4022_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v_recArgInfoss_3982_);
lean_ctor_set(v___x_4008_, 0, v_report_4016_);
v___x_4022_ = v___x_4008_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_report_4016_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_recArgInfoss_3982_);
v___x_4022_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
size_t v_sz_4023_; lean_object* v___x_4024_; 
v_sz_4023_ = lean_array_size(v___y_4015_);
v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3973_, v___x_4013_, v_values_3974_, v_fnNames_3971_, v___y_4015_, v_sz_4023_, v___x_3996_, v___x_4022_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec_ref(v___y_4015_);
lean_dec_ref(v_values_3974_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4041_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4041_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4041_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v_fst_4029_; lean_object* v_snd_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4040_; 
v_fst_4029_ = lean_ctor_get(v_a_4025_, 0);
v_snd_4030_ = lean_ctor_get(v_a_4025_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_a_4025_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4032_ = v_a_4025_;
v_isShared_4033_ = v_isSharedCheck_4040_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_snd_4030_);
lean_inc(v_fst_4029_);
lean_dec(v_a_4025_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4040_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v_fst_4029_);
lean_ctor_set(v___x_4032_, 0, v_snd_4030_);
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_snd_4030_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_fst_4029_);
v___x_4035_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4035_);
v___x_4037_ = v___x_4027_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4024_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4024_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
v___jp_4051_:
{
lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4057_ = lean_array_get_size(v___y_4052_);
v___x_4058_ = lean_nat_dec_eq(v___x_4057_, v___x_3981_);
if (v___x_4058_ == 0)
{
lean_del_object(v___x_4004_);
v___y_4015_ = v___y_4052_;
v_report_4016_ = v_fst_4002_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4059_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 7);
lean_ctor_set(v___x_4004_, 1, v___x_4059_);
v___x_4061_ = v___x_4004_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_fst_4002_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
v___y_4015_ = v___y_4052_;
v_report_4016_ = v___x_4061_;
v___y_4017_ = v___y_4053_;
v___y_4018_ = v___y_4054_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
goto v___jp_4014_;
}
}
}
v___jp_4064_:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4069_, v___y_4066_, v___y_4068_, v___y_4067_, v___y_4065_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_toCold_4071_; lean_object* v_options_4072_; uint8_t v_hasTrace_4073_; 
v_toCold_4071_ = lean_ctor_get(v___y_4067_, 0);
v_options_4072_ = lean_ctor_get(v_toCold_4071_, 2);
v_hasTrace_4073_ = lean_ctor_get_uint8(v_options_4072_, sizeof(void*)*1);
if (v_hasTrace_4073_ == 0)
{
lean_object* v_a_4074_; 
v_a_4074_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4070_, 1);
v___y_4052_ = v_a_4074_;
v___y_4053_ = v___y_4066_;
v___y_4054_ = v___y_4068_;
v___y_4055_ = v___y_4067_;
v___y_4056_ = v___y_4065_;
goto v___jp_4051_;
}
else
{
lean_object* v_a_4075_; lean_object* v_inheritedTraceOptions_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_a_4075_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4070_, 1);
v_inheritedTraceOptions_4076_ = lean_ctor_get(v_toCold_4071_, 11);
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4076_, v_options_4072_, v___x_4077_);
if (v___x_4078_ == 0)
{
v___y_4052_ = v_a_4075_;
v___y_4053_ = v___y_4066_;
v___y_4054_ = v___y_4068_;
v___y_4055_ = v___y_4067_;
v___y_4056_ = v___y_4065_;
goto v___jp_4051_;
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
v___x_4085_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4063_, v___x_4084_, v___y_4066_, v___y_4068_, v___y_4067_, v___y_4065_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_dec_ref_known(v___x_4085_, 1);
v___y_4052_ = v_a_4075_;
v___y_4053_ = v___y_4066_;
v___y_4054_ = v___y_4068_;
v___y_4055_ = v___y_4067_;
v___y_4056_ = v___y_4065_;
goto v___jp_4051_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_a_4075_);
lean_dec_ref(v___x_4013_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4004_);
lean_dec(v_fst_4002_);
lean_dec_ref(v_values_3974_);
lean_dec_ref(v_xs_3973_);
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
lean_dec_ref(v___x_4013_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4004_);
lean_dec(v_fst_4002_);
lean_dec_ref(v_values_3974_);
lean_dec_ref(v_xs_3973_);
v_a_4094_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4070_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4070_);
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
v___x_4108_ = lean_array_get_size(v___x_4013_);
v___x_4109_ = lean_nat_dec_lt(v___x_3981_, v___x_4108_);
if (v___x_4109_ == 0)
{
v___y_4065_ = v___y_4106_;
v___y_4066_ = v___y_4103_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4104_;
v___y_4069_ = v___x_4107_;
goto v___jp_4064_;
}
else
{
size_t v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = lean_usize_of_nat(v___x_4108_);
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4013_, v___x_3996_, v___x_4110_, v___x_4107_);
v___y_4065_ = v___y_4106_;
v___y_4066_ = v___y_4103_;
v___y_4067_ = v___y_4105_;
v___y_4068_ = v___y_4104_;
v___y_4069_ = v___x_4111_;
goto v___jp_4064_;
}
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref(v_values_3974_);
lean_dec_ref(v_xs_3973_);
v_a_4142_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_3997_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_3997_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4150_, lean_object* v_fixedParamPerms_4151_, lean_object* v_xs_4152_, lean_object* v_values_4153_, lean_object* v_termMeasure_x3fs_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4150_, v_fixedParamPerms_4151_, v_xs_4152_, v_values_4153_, v_termMeasure_x3fs_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec_ref(v_fnNames_4150_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4161_, lean_object* v_as_4162_, size_t v_sz_4163_, size_t v_i_4164_, lean_object* v_b_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4161_, v_as_4162_, v_sz_4163_, v_i_4164_, v_b_4165_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4172_, lean_object* v_as_4173_, lean_object* v_sz_4174_, lean_object* v_i_4175_, lean_object* v_b_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
size_t v_sz_boxed_4182_; size_t v_i_boxed_4183_; lean_object* v_res_4184_; 
v_sz_boxed_4182_ = lean_unbox_usize(v_sz_4174_);
lean_dec(v_sz_4174_);
v_i_boxed_4183_ = lean_unbox_usize(v_i_4175_);
lean_dec(v_i_4175_);
v_res_4184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4172_, v_as_4173_, v_sz_boxed_4182_, v_i_boxed_4183_, v_b_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec_ref(v_as_4173_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4185_, uint8_t v_skipRealize_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v_env_4190_; uint8_t v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4189_ = lean_st_ref_get(v___y_4187_);
v_env_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc_ref(v_env_4190_);
lean_dec(v___x_4189_);
v___x_4191_ = l_Lean_Environment_contains(v_env_4190_, v_constName_4185_, v_skipRealize_4186_);
v___x_4192_ = lean_box(v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4194_, lean_object* v_skipRealize_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
uint8_t v_skipRealize_boxed_4198_; lean_object* v_res_4199_; 
v_skipRealize_boxed_4198_ = lean_unbox(v_skipRealize_4195_);
v_res_4199_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4194_, v_skipRealize_boxed_4198_, v___y_4196_);
lean_dec(v___y_4196_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4200_, uint8_t v_skipRealize_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4200_, v_skipRealize_4201_, v___y_4205_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4208_, lean_object* v_skipRealize_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v_skipRealize_boxed_4215_; lean_object* v_res_4216_; 
v_skipRealize_boxed_4215_ = lean_unbox(v_skipRealize_4209_);
v_res_4216_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4208_, v_skipRealize_boxed_4215_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_Meta_saveState___redArg(v___y_4219_, v___y_4221_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4225_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref_known(v___x_4223_, 1);
lean_inc(v___y_4221_);
lean_inc_ref(v___y_4220_);
lean_inc(v___y_4219_);
lean_inc_ref(v___y_4218_);
v___x_4225_ = lean_apply_5(v_x_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, lean_box(0));
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_dec(v_a_4224_);
return v___x_4225_;
}
else
{
lean_object* v_a_4226_; uint8_t v___y_4228_; uint8_t v___x_4246_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
v___x_4246_ = l_Lean_Exception_isInterrupt(v_a_4226_);
if (v___x_4246_ == 0)
{
uint8_t v___x_4247_; 
lean_inc(v_a_4226_);
v___x_4247_ = l_Lean_Exception_isRuntime(v_a_4226_);
v___y_4228_ = v___x_4247_;
goto v___jp_4227_;
}
else
{
v___y_4228_ = v___x_4246_;
goto v___jp_4227_;
}
v___jp_4227_:
{
if (v___y_4228_ == 0)
{
lean_object* v___x_4229_; 
lean_dec_ref_known(v___x_4225_, 1);
v___x_4229_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4224_, v___y_4219_, v___y_4221_);
lean_dec(v_a_4224_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4236_ == 0)
{
lean_object* v_unused_4237_; 
v_unused_4237_ = lean_ctor_get(v___x_4229_, 0);
lean_dec(v_unused_4237_);
v___x_4231_ = v___x_4229_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_dec(v___x_4229_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set_tag(v___x_4231_, 1);
lean_ctor_set(v___x_4231_, 0, v_a_4226_);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4226_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec(v_a_4226_);
v_a_4238_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4229_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4229_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_dec(v_a_4226_);
lean_dec(v_a_4224_);
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec_ref(v_x_4217_);
v_a_4248_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4223_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4223_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4271_, lean_object* v_x_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4271_, v_x_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4281_ = l_Lean_stringToMessageData(v___x_4280_);
return v___x_4281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4284_ = l_Lean_stringToMessageData(v___x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4285_, uint8_t v___x_4286_, lean_object* v_group_4287_, lean_object* v_k_4288_, lean_object* v_comb_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4285_, v___x_4286_, v___y_4293_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; uint8_t v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = lean_unbox(v_a_4296_);
lean_dec(v_a_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4299_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4287_);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4302_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v___x_4304_; 
lean_dec_ref_known(v___x_4303_, 1);
v___x_4304_ = lean_apply_6(v_k_4288_, v_comb_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, lean_box(0));
return v___x_4304_;
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v_comb_4289_);
lean_dec_ref(v_k_4288_);
v_a_4305_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4303_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4303_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
else
{
lean_object* v___x_4313_; 
lean_dec_ref(v_group_4287_);
v___x_4313_ = lean_apply_6(v_k_4288_, v_comb_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, lean_box(0));
return v___x_4313_;
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v_comb_4289_);
lean_dec_ref(v_k_4288_);
lean_dec_ref(v_group_4287_);
v_a_4314_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4295_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4295_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4322_, lean_object* v___x_4323_, lean_object* v_group_4324_, lean_object* v_k_4325_, lean_object* v_comb_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
uint8_t v___x_4304__boxed_4332_; lean_object* v_res_4333_; 
v___x_4304__boxed_4332_ = lean_unbox(v___x_4323_);
v_res_4333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4322_, v___x_4304__boxed_4332_, v_group_4324_, v_k_4325_, v_comb_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
return v_res_4333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4338_ = l_Lean_stringToMessageData(v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4339_, lean_object* v_fnNames_4340_, lean_object* v_xs_4341_, lean_object* v_values_4342_, lean_object* v_as_4343_, size_t v_sz_4344_, size_t v_i_4345_, lean_object* v_b_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
uint8_t v___x_4352_; 
v___x_4352_ = lean_usize_dec_lt(v_i_4345_, v_sz_4344_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
lean_dec_ref(v_values_4342_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v_k_4339_);
v___x_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4353_, 0, v_b_4346_);
return v___x_4353_;
}
else
{
lean_object* v_snd_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4424_; 
v_snd_4354_ = lean_ctor_get(v_b_4346_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_b_4346_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v_b_4346_, 0);
lean_dec(v_unused_4425_);
v___x_4356_ = v_b_4346_;
v_isShared_4357_ = v_isSharedCheck_4424_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_snd_4354_);
lean_dec(v_b_4346_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4424_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_a_4358_; lean_object* v_group_4359_; lean_object* v_comb_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4423_; 
v_a_4358_ = lean_array_uget(v_as_4343_, v_i_4345_);
v_group_4359_ = lean_ctor_get(v_a_4358_, 0);
v_comb_4360_ = lean_ctor_get(v_a_4358_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v_a_4358_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4362_ = v_a_4358_;
v_isShared_4363_ = v_isSharedCheck_4423_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_comb_4360_);
lean_inc(v_group_4359_);
lean_dec(v_a_4358_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4423_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_toIndGroupInfo_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; 
v_toIndGroupInfo_4364_ = lean_ctor_get(v_group_4359_, 0);
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4364_, v___x_4365_);
v___x_4367_ = lean_box(v___x_4352_);
lean_inc_ref(v_comb_4360_);
lean_inc_ref(v_k_4339_);
v___f_4368_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4368_, 0, v___x_4366_);
lean_closure_set(v___f_4368_, 1, v___x_4367_);
lean_closure_set(v___f_4368_, 2, v_group_4359_);
lean_closure_set(v___f_4368_, 3, v_k_4339_);
lean_closure_set(v___f_4368_, 4, v_comb_4360_);
v___x_4369_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4368_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4381_; 
lean_del_object(v___x_4362_);
lean_dec_ref(v_comb_4360_);
lean_dec_ref(v_values_4342_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v_k_4339_);
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4381_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4381_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4374_; lean_object* v___x_4376_; 
v___x_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_a_4370_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4374_);
v___x_4376_ = v___x_4356_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4374_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_snd_4354_);
v___x_4376_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
lean_object* v___x_4378_; 
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4376_);
v___x_4378_ = v___x_4372_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4422_; 
v_a_4382_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4384_ = v___x_4369_;
v_isShared_4385_ = v_isSharedCheck_4422_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4369_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4422_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; uint8_t v___y_4388_; uint8_t v___x_4420_; 
v___x_4386_ = lean_box(0);
v___x_4420_ = l_Lean_Exception_isInterrupt(v_a_4382_);
if (v___x_4420_ == 0)
{
uint8_t v___x_4421_; 
lean_inc(v_a_4382_);
v___x_4421_ = l_Lean_Exception_isRuntime(v_a_4382_);
v___y_4388_ = v___x_4421_;
goto v___jp_4387_;
}
else
{
v___y_4388_ = v___x_4420_;
goto v___jp_4387_;
}
v___jp_4387_:
{
if (v___y_4388_ == 0)
{
lean_object* v___x_4389_; 
lean_del_object(v___x_4384_);
lean_inc_ref(v_values_4342_);
lean_inc_ref(v_xs_4341_);
v___x_4389_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4340_, v_xs_4341_, v_values_4342_, v_comb_4360_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref_known(v___x_4389_, 1);
v___x_4391_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4363_ == 0)
{
lean_ctor_set_tag(v___x_4362_, 7);
lean_ctor_set(v___x_4362_, 1, v_a_4390_);
lean_ctor_set(v___x_4362_, 0, v___x_4391_);
v___x_4393_ = v___x_4362_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_a_4390_);
v___x_4393_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4394_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_Exception_toMessageData(v_a_4382_);
v___x_4397_ = l_Lean_indentD(v___x_4396_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4395_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v_snd_4354_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v___x_4401_);
lean_ctor_set(v___x_4356_, 0, v___x_4386_);
v___x_4403_ = v___x_4356_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
size_t v___x_4404_; size_t v___x_4405_; 
v___x_4404_ = ((size_t)1ULL);
v___x_4405_ = lean_usize_add(v_i_4345_, v___x_4404_);
v_i_4345_ = v___x_4405_;
v_b_4346_ = v___x_4403_;
goto _start;
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_a_4382_);
lean_del_object(v___x_4362_);
lean_del_object(v___x_4356_);
lean_dec(v_snd_4354_);
lean_dec_ref(v_values_4342_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v_k_4339_);
v_a_4409_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4389_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4389_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
else
{
lean_object* v___x_4418_; 
lean_del_object(v___x_4362_);
lean_dec_ref(v_comb_4360_);
lean_del_object(v___x_4356_);
lean_dec(v_snd_4354_);
lean_dec_ref(v_values_4342_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v_k_4339_);
if (v_isShared_4385_ == 0)
{
v___x_4418_ = v___x_4384_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4382_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4426_, lean_object* v_fnNames_4427_, lean_object* v_xs_4428_, lean_object* v_values_4429_, lean_object* v_as_4430_, lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_sz_boxed_4439_; size_t v_i_boxed_4440_; lean_object* v_res_4441_; 
v_sz_boxed_4439_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4440_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4426_, v_fnNames_4427_, v_xs_4428_, v_values_4429_, v_as_4430_, v_sz_boxed_4439_, v_i_boxed_4440_, v_b_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec_ref(v_as_4430_);
lean_dec_ref(v_fnNames_4427_);
return v_res_4441_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4444_ = l_Lean_stringToMessageData(v___x_4443_);
return v___x_4444_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4447_ = l_Lean_stringToMessageData(v___x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4448_, lean_object* v_xs_4449_, lean_object* v_values_4450_, lean_object* v_candidates_4451_, lean_object* v_k_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v_candidates_4458_; lean_object* v_report_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4519_; 
v_candidates_4458_ = lean_ctor_get(v_candidates_4451_, 0);
v_report_4459_ = lean_ctor_get(v_candidates_4451_, 1);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_candidates_4451_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4461_ = v_candidates_4451_;
v_isShared_4462_ = v_isSharedCheck_4519_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_report_4459_);
lean_inc(v_candidates_4458_);
lean_dec(v_candidates_4451_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4519_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = lean_box(0);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4463_);
v___x_4465_ = v___x_4461_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_report_4459_);
v___x_4465_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
size_t v_sz_4466_; size_t v___x_4467_; lean_object* v___x_4468_; 
v_sz_4466_ = lean_array_size(v_candidates_4458_);
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4452_, v_fnNames_4448_, v_xs_4449_, v_values_4450_, v_candidates_4458_, v_sz_4466_, v___x_4467_, v___x_4465_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec_ref(v_candidates_4458_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4509_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4509_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4509_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v_fst_4473_; 
v_fst_4473_ = lean_ctor_get(v_a_4469_, 0);
if (lean_obj_tag(v_fst_4473_) == 0)
{
lean_object* v_toCold_4474_; lean_object* v_options_4475_; lean_object* v_snd_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4503_; 
lean_del_object(v___x_4471_);
v_toCold_4474_ = lean_ctor_get(v_a_4455_, 0);
v_options_4475_ = lean_ctor_get(v_toCold_4474_, 2);
v_snd_4476_ = lean_ctor_get(v_a_4469_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_a_4469_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v_a_4469_, 0);
lean_dec(v_unused_4504_);
v___x_4478_ = v_a_4469_;
v_isShared_4479_ = v_isSharedCheck_4503_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_snd_4476_);
lean_dec(v_a_4469_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4503_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v_inheritedTraceOptions_4480_; uint8_t v_hasTrace_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
v_inheritedTraceOptions_4480_ = lean_ctor_get(v_toCold_4474_, 11);
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
v___x_4485_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
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
v___x_4489_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
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
v___x_4492_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4486_, v___x_4491_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v___x_4493_; 
lean_dec_ref_known(v___x_4492_, 1);
v___x_4493_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4484_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
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
lean_inc_ref(v_fst_4473_);
lean_dec(v_a_4469_);
v_val_4505_ = lean_ctor_get(v_fst_4473_, 0);
lean_inc(v_val_4505_);
lean_dec_ref_known(v_fst_4473_, 1);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v_val_4505_);
v___x_4507_ = v___x_4471_;
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
v_a_4510_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4468_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4468_);
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
