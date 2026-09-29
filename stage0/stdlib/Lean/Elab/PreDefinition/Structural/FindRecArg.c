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
lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v_a_245_ = lean_array_uget_borrowed(v_as_191_, v_i_193_);
v___x_246_ = lean_array_fget(v_array_226_, v_start_227_);
v___x_247_ = lean_nat_add(v_start_227_, v___x_230_);
lean_dec(v_start_227_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_array_226_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_stop_228_);
v___x_249_ = v_reuseFailAlloc_274_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
lean_inc_ref(v_xs_190_);
v___x_250_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_190_, v___x_246_, v___x_229_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v_a_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_inc(v_a_245_);
v___x_254_ = l_Lean_MessageData_ofName(v_a_245_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_array_push(v_fst_204_, v___x_255_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_233_);
lean_ctor_set(v___x_210_, 0, v___x_249_);
v___x_258_ = v___x_210_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_249_);
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
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v___x_249_);
lean_dec_ref(v___x_233_);
lean_del_object(v___x_210_);
lean_del_object(v___x_206_);
lean_dec(v_fst_204_);
lean_dec_ref(v_xs_190_);
v_a_266_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_250_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_250_);
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
lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___x_481_; uint8_t v_fst_483_; lean_object* v_mctx_484_; lean_object* v___y_502_; lean_object* v_mctx_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___f_479_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0));
v___f_480_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_480_, 0, v_fvarId_476_);
v___x_481_ = lean_st_ref_get(v___y_477_);
v_mctx_507_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref_n(v_mctx_507_, 2);
lean_dec(v___x_481_);
v___x_508_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_mctx_507_);
v___x_510_ = l_Lean_Expr_hasFVar(v_e_475_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_Expr_hasMVar(v_e_475_);
if (v___x_511_ == 0)
{
lean_dec_ref_known(v___x_509_, 2);
lean_dec_ref(v___f_480_);
lean_dec_ref(v_e_475_);
v_fst_483_ = v___x_511_;
v_mctx_484_ = v_mctx_507_;
goto v___jp_482_;
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_mctx_507_);
v___x_512_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_480_, v___f_479_, v_e_475_, v___x_509_);
v___y_502_ = v___x_512_;
goto v___jp_501_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_mctx_507_);
v___x_513_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_480_, v___f_479_, v_e_475_, v___x_509_);
v___y_502_ = v___x_513_;
goto v___jp_501_;
}
v___jp_482_:
{
lean_object* v___x_485_; lean_object* v_cache_486_; lean_object* v_zetaDeltaFVarIds_487_; lean_object* v_postponed_488_; lean_object* v_diag_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_499_; 
v___x_485_ = lean_st_ref_take(v___y_477_);
v_cache_486_ = lean_ctor_get(v___x_485_, 1);
v_zetaDeltaFVarIds_487_ = lean_ctor_get(v___x_485_, 2);
v_postponed_488_ = lean_ctor_get(v___x_485_, 3);
v_diag_489_ = lean_ctor_get(v___x_485_, 4);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_485_, 0);
lean_dec(v_unused_500_);
v___x_491_ = v___x_485_;
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_diag_489_);
lean_inc(v_postponed_488_);
lean_inc(v_zetaDeltaFVarIds_487_);
lean_inc(v_cache_486_);
lean_dec(v___x_485_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_mctx_484_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_mctx_484_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_zetaDeltaFVarIds_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_postponed_488_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_diag_489_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_st_ref_put(v___y_477_, v___x_494_);
v___x_496_ = lean_box(v_fst_483_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
v___jp_501_:
{
lean_object* v_snd_503_; lean_object* v_fst_504_; lean_object* v_mctx_505_; uint8_t v___x_506_; 
v_snd_503_ = lean_ctor_get(v___y_502_, 1);
lean_inc(v_snd_503_);
v_fst_504_ = lean_ctor_get(v___y_502_, 0);
lean_inc(v_fst_504_);
lean_dec_ref(v___y_502_);
v_mctx_505_ = lean_ctor_get(v_snd_503_, 1);
lean_inc_ref(v_mctx_505_);
lean_dec(v_snd_503_);
v___x_506_ = lean_unbox(v_fst_504_);
lean_dec(v_fst_504_);
v_fst_483_ = v___x_506_;
v_mctx_484_ = v_mctx_505_;
goto v___jp_482_;
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
lean_object* v_a_582_; uint8_t v___x_586_; 
v___x_586_ = lean_usize_dec_lt(v_i_574_, v_sz_573_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_a_571_);
lean_dec_ref(v_a_569_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_b_575_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec_ref(v_b_575_);
v___x_588_ = lean_box(0);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_590_ = lean_array_uget_borrowed(v_as_572_, v_i_574_);
v___x_591_ = l_Lean_Expr_fvarId_x21(v_a_590_);
lean_inc_ref(v_a_569_);
v___x_592_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_569_, v___x_591_, v___y_577_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_606_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_606_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_606_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_606_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; 
v___x_597_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_570_, v_a_590_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_598_ == 0)
{
lean_del_object(v___x_595_);
v_a_582_ = v___x_589_;
goto v___jp_581_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref(v_a_569_);
lean_inc(v_a_590_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_a_571_);
lean_ctor_set(v___x_599_, 1, v_a_590_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_588_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_602_);
v___x_604_ = v___x_595_;
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
lean_del_object(v___x_595_);
lean_dec(v_a_593_);
v_a_582_ = v___x_589_;
goto v___jp_581_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_a_571_);
lean_dec_ref(v_a_569_);
v_a_607_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_592_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_592_);
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
v___jp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_574_, v___x_583_);
lean_inc_ref(v_a_582_);
v_i_574_ = v___x_584_;
v_b_575_ = v_a_582_;
goto _start;
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
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_a_645_; lean_object* v___x_646_; 
lean_dec_ref(v_b_635_);
v___x_643_ = lean_box(0);
v___x_644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_645_ = lean_array_uget_borrowed(v_as_632_, v_i_634_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v_a_645_);
v___x_646_ = lean_infer_type(v_a_645_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v_sz_648_ = lean_array_size(v_ys_630_);
v___x_649_ = ((size_t)0ULL);
lean_inc(v_a_645_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_647_, v_indices_631_, v_a_645_, v_ys_630_, v_sz_648_, v___x_649_, v___x_644_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
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
v_b_635_ = v___x_644_;
goto _start;
}
else
{
lean_object* v___x_663_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_643_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_643_);
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
v_a_671_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_646_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_646_);
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
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_709_; 
lean_dec_ref(v_b_698_);
v___x_706_ = lean_box(0);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_708_ = lean_array_uget_borrowed(v_as_695_, v_i_697_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v_a_708_);
v___x_709_ = lean_infer_type(v_a_708_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; size_t v_sz_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_sz_711_ = lean_array_size(v_ys_694_);
v___x_712_ = ((size_t)0ULL);
lean_inc(v_a_708_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_710_, v_indices_693_, v_a_708_, v_ys_694_, v_sz_711_, v___x_712_, v___x_707_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
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
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_694_, v_indices_693_, v_as_695_, v_sz_696_, v___x_723_, v___x_707_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_724_;
}
else
{
lean_object* v___x_726_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_706_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_706_);
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
v_a_734_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_709_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_709_);
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
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_b_801_);
v___x_806_ = lean_box(0);
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0));
v_a_808_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
v___x_809_ = l_Lean_Expr_fvarId_x21(v_a_808_);
lean_inc_ref(v_a_797_);
v___x_810_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_797_, v___x_809_, v___y_802_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_826_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_826_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_815_ == 0)
{
size_t v___x_816_; size_t v___x_817_; 
lean_del_object(v___x_813_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_800_, v___x_816_);
v_i_800_ = v___x_817_;
v_b_801_ = v___x_807_;
goto _start;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_inc(v_a_808_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_a_797_);
lean_ctor_set(v___x_819_, 1, v_a_808_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_806_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_822_);
v___x_824_ = v___x_813_;
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
v_a_827_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_810_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_810_);
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
lean_object* v___f_971_; lean_object* v___x_4718__overap_972_; lean_object* v___x_973_; 
v___f_971_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4718__overap_972_ = lean_panic_fn_borrowed(v___f_971_, v_msg_965_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
v___x_973_ = lean_apply_5(v___x_4718__overap_972_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
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
v___x_1227_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1219_);
if (v___x_1227_ == 0)
{
lean_object* v_name_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_name_1228_ = lean_ctor_get(v___y_1220_, 0);
lean_inc(v_name_1228_);
lean_dec_ref(v___y_1220_);
v___x_1229_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1230_ = l_Lean_MessageData_ofName(v_name_1228_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_indentExpr(v___y_1226_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1235_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1200_, v_xs_1201_);
v___x_1238_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1237_, v___y_1219_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
if (lean_obj_tag(v_a_1239_) == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1237_, v___y_1224_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
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
lean_dec_ref(v___y_1226_);
v_name_1245_ = lean_ctor_get(v___y_1220_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___y_1220_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; lean_object* v_unused_1267_; 
v_unused_1266_ = lean_ctor_get(v___y_1220_, 2);
lean_dec(v_unused_1266_);
v_unused_1267_ = lean_ctor_get(v___y_1220_, 1);
lean_dec(v_unused_1267_);
v___x_1247_ = v___y_1220_;
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_name_1245_);
lean_dec(v___y_1220_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_array_mk(v___y_1216_);
v___x_1250_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1249_, v_name_1245_);
lean_dec(v_name_1245_);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_val_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_sz_1252_ = lean_array_size(v___y_1219_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1201_, v_sz_1252_, v___x_1253_, v___y_1219_);
v___x_1255_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1223_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 2, v___y_1224_);
lean_ctor_set(v___x_1247_, 1, v___y_1222_);
lean_ctor_set(v___x_1247_, 0, v___x_1255_);
v___x_1257_ = v___x_1247_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___y_1222_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___y_1224_);
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
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1219_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v___x_1263_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1264_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1263_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
return v___x_1264_;
}
}
}
else
{
lean_object* v_val_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1243_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
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
v___x_1275_ = l_Lean_indentExpr(v___y_1226_);
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
v___x_1288_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1287_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
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
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
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
v_name_1306_ = lean_ctor_get(v___y_1220_, 0);
lean_inc(v_name_1306_);
lean_dec_ref(v___y_1220_);
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
v___x_1313_ = l_Lean_indentExpr(v___y_1226_);
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
v___x_1323_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1322_, v___y_1217_, v___y_1221_, v___y_1225_, v___y_1218_);
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v___x_1237_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
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
v___x_1351_ = l_Array_toSubarray___redArg(v___y_1344_, v_lower_1349_, v_upper_1350_);
v___x_1352_ = l_Subarray_copy___redArg(v___x_1351_);
v___x_1353_ = lean_array_get_size(v___x_1352_);
v___x_1354_ = lean_nat_dec_lt(v___y_1346_, v___x_1353_);
lean_dec(v___y_1346_);
if (v___x_1354_ == 0)
{
v___y_1216_ = v___y_1341_;
v___y_1217_ = v___y_1342_;
v___y_1218_ = v___y_1337_;
v___y_1219_ = v___x_1352_;
v___y_1220_ = v___y_1343_;
v___y_1221_ = v___y_1338_;
v___y_1222_ = v___y_1345_;
v___y_1223_ = v___y_1339_;
v___y_1224_ = v___y_1340_;
v___y_1225_ = v___y_1347_;
v___y_1226_ = v___y_1348_;
goto v___jp_1215_;
}
else
{
if (v___x_1354_ == 0)
{
v___y_1216_ = v___y_1341_;
v___y_1217_ = v___y_1342_;
v___y_1218_ = v___y_1337_;
v___y_1219_ = v___x_1352_;
v___y_1220_ = v___y_1343_;
v___y_1221_ = v___y_1338_;
v___y_1222_ = v___y_1345_;
v___y_1223_ = v___y_1339_;
v___y_1224_ = v___y_1340_;
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
v___y_1216_ = v___y_1341_;
v___y_1217_ = v___y_1342_;
v___y_1218_ = v___y_1337_;
v___y_1219_ = v___x_1352_;
v___y_1220_ = v___y_1343_;
v___y_1221_ = v___y_1338_;
v___y_1222_ = v___y_1345_;
v___y_1223_ = v___y_1339_;
v___y_1224_ = v___y_1340_;
v___y_1225_ = v___y_1347_;
v___y_1226_ = v___y_1348_;
goto v___jp_1215_;
}
else
{
lean_object* v_name_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v___x_1352_);
lean_dec(v___y_1345_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v_i_1202_);
lean_dec_ref(v_fixedParamPerm_1200_);
lean_dec(v_fnName_1199_);
v_name_1358_ = lean_ctor_get(v___y_1343_, 0);
lean_inc(v_name_1358_);
lean_dec_ref(v___y_1343_);
v___x_1359_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1360_ = l_Lean_MessageData_ofName(v_name_1358_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_indentExpr(v___y_1348_);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1365_, v___y_1342_, v___y_1338_, v___y_1347_, v___y_1337_);
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
v___y_1337_ = v___y_1372_;
v___y_1338_ = v___y_1370_;
v___y_1339_ = v_val_1384_;
v___y_1340_ = v___x_1396_;
v___y_1341_ = v_all_1387_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v_toConstantVal_1385_;
v___y_1344_ = v___x_1393_;
v___y_1345_ = v_us_1378_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v_a_1375_;
v_lower_1349_ = v_numParams_1386_;
v_upper_1350_ = v___x_1397_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v___y_1372_;
v___y_1338_ = v___y_1370_;
v___y_1339_ = v_val_1384_;
v___y_1340_ = v___x_1396_;
v___y_1341_ = v_all_1387_;
v___y_1342_ = v___y_1369_;
v___y_1343_ = v_toConstantVal_1385_;
v___y_1344_ = v___x_1393_;
v___y_1345_ = v_us_1378_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v_a_1375_;
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
lean_object* v_ref_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1684_; 
v_ref_1637_ = lean_ctor_get(v___y_1634_, 2);
v___x_1638_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1684_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1684_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v_traceState_1644_; lean_object* v_env_1645_; lean_object* v_nextMacroScope_1646_; lean_object* v_ngen_1647_; lean_object* v_auxDeclNGen_1648_; lean_object* v_cache_1649_; lean_object* v_recordedDeps_1650_; lean_object* v_messages_1651_; lean_object* v_infoState_1652_; lean_object* v_snapshotTasks_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1683_; 
v___x_1643_ = lean_st_ref_take(v___y_1635_);
v_traceState_1644_ = lean_ctor_get(v___x_1643_, 4);
v_env_1645_ = lean_ctor_get(v___x_1643_, 0);
v_nextMacroScope_1646_ = lean_ctor_get(v___x_1643_, 1);
v_ngen_1647_ = lean_ctor_get(v___x_1643_, 2);
v_auxDeclNGen_1648_ = lean_ctor_get(v___x_1643_, 3);
v_cache_1649_ = lean_ctor_get(v___x_1643_, 5);
v_recordedDeps_1650_ = lean_ctor_get(v___x_1643_, 6);
v_messages_1651_ = lean_ctor_get(v___x_1643_, 7);
v_infoState_1652_ = lean_ctor_get(v___x_1643_, 8);
v_snapshotTasks_1653_ = lean_ctor_get(v___x_1643_, 9);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1655_ = v___x_1643_;
v_isShared_1656_ = v_isSharedCheck_1683_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snapshotTasks_1653_);
lean_inc(v_infoState_1652_);
lean_inc(v_messages_1651_);
lean_inc(v_recordedDeps_1650_);
lean_inc(v_cache_1649_);
lean_inc(v_traceState_1644_);
lean_inc(v_auxDeclNGen_1648_);
lean_inc(v_ngen_1647_);
lean_inc(v_nextMacroScope_1646_);
lean_inc(v_env_1645_);
lean_dec(v___x_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1683_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
uint64_t v_tid_1657_; lean_object* v_traces_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1682_; 
v_tid_1657_ = lean_ctor_get_uint64(v_traceState_1644_, sizeof(void*)*1);
v_traces_1658_ = lean_ctor_get(v_traceState_1644_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_traceState_1644_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1660_ = v_traceState_1644_;
v_isShared_1661_ = v_isSharedCheck_1682_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_traces_1658_);
lean_dec(v_traceState_1644_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1682_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; double v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1665_ = 0;
v___x_1666_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1667_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1667_, 0, v_cls_1630_);
lean_ctor_set(v___x_1667_, 1, v___x_1663_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
lean_ctor_set_float(v___x_1667_, sizeof(void*)*3, v___x_1664_);
lean_ctor_set_float(v___x_1667_, sizeof(void*)*3 + 8, v___x_1664_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*3 + 16, v___x_1665_);
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1669_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v_a_1639_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_inc(v_ref_1637_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_ref_1637_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = l_Lean_PersistentArray_push___redArg(v_traces_1658_, v___x_1670_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1671_);
v___x_1673_ = v___x_1660_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1671_);
lean_ctor_set_uint64(v_reuseFailAlloc_1681_, sizeof(void*)*1, v_tid_1657_);
v___x_1673_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 4, v___x_1673_);
v___x_1675_ = v___x_1655_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_env_1645_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_nextMacroScope_1646_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_ngen_1647_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_auxDeclNGen_1648_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1680_, 5, v_cache_1649_);
lean_ctor_set(v_reuseFailAlloc_1680_, 6, v_recordedDeps_1650_);
lean_ctor_set(v_reuseFailAlloc_1680_, 7, v_messages_1651_);
lean_ctor_set(v_reuseFailAlloc_1680_, 8, v_infoState_1652_);
lean_ctor_set(v_reuseFailAlloc_1680_, 9, v_snapshotTasks_1653_);
v___x_1675_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_st_ref_put(v___y_1635_, v___x_1675_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1662_);
v___x_1678_ = v___x_1641_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1662_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1685_, lean_object* v_msg_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1685_, v_msg_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1692_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___f_1697_; 
v___x_1696_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1697_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1697_, 0, v___x_1696_);
return v___f_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1702_; lean_object* v_recArgInfos_1703_; lean_object* v___x_1704_; 
v_report_1702_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1703_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_recArgInfos_1703_);
lean_ctor_set(v___x_1704_, 1, v_report_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1717_ = l_Lean_Name_append(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1721_, lean_object* v_fixedParamPerm_1722_, lean_object* v_xs_1723_, lean_object* v_fnName_1724_, lean_object* v_ys_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1721_) == 1)
{
lean_object* v_val_1732_; lean_object* v_ref_1733_; lean_object* v_toCold_1734_; lean_object* v_currRecDepth_1735_; lean_object* v_ref_1736_; uint16_t v_optionFlags_1737_; uint8_t v_suppressElabErrors_1738_; uint8_t v_isRecordingDeps_1739_; lean_object* v___f_1740_; lean_object* v_args_1741_; lean_object* v___f_1742_; lean_object* v_ref_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_val_1732_ = lean_ctor_get(v_termMeasure_x3f_1721_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v_termMeasure_x3f_1721_, 1);
v_ref_1733_ = lean_ctor_get(v_val_1732_, 0);
lean_inc(v_ref_1733_);
v_toCold_1734_ = lean_ctor_get(v___y_1729_, 0);
v_currRecDepth_1735_ = lean_ctor_get(v___y_1729_, 1);
v_ref_1736_ = lean_ctor_get(v___y_1729_, 2);
v_optionFlags_1737_ = lean_ctor_get_uint16(v___y_1729_, sizeof(void*)*3);
v_suppressElabErrors_1738_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1739_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 3);
v___f_1740_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1722_);
v_args_1741_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1722_, v_xs_1723_, v_ys_1725_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1742_, 0, v_val_1732_);
lean_closure_set(v___f_1742_, 1, v_fnName_1724_);
lean_closure_set(v___f_1742_, 2, v_fixedParamPerm_1722_);
lean_closure_set(v___f_1742_, 3, v_args_1741_);
v_ref_1743_ = l_Lean_replaceRef(v_ref_1733_, v_ref_1736_);
lean_dec(v_ref_1733_);
lean_inc(v_currRecDepth_1735_);
lean_inc_ref(v_toCold_1734_);
v___x_1744_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1744_, 0, v_toCold_1734_);
lean_ctor_set(v___x_1744_, 1, v_currRecDepth_1735_);
lean_ctor_set(v___x_1744_, 2, v_ref_1743_);
lean_ctor_set_uint16(v___x_1744_, sizeof(void*)*3, v_optionFlags_1737_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*3 + 2, v_suppressElabErrors_1738_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*3 + 3, v_isRecordingDeps_1739_);
v___x_1745_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1742_, v___f_1740_, v___y_1727_, v___y_1728_, v___x_1744_, v___y_1730_);
lean_dec_ref_known(v___x_1744_, 3);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1758_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_mk_empty_array_with_capacity(v___x_1750_);
v___x_1752_ = lean_array_push(v___x_1751_, v_a_1746_);
v___x_1753_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1756_ = v___x_1748_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1745_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1745_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_args_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_termMeasure_x3f_1721_);
lean_inc_ref(v_fixedParamPerm_1722_);
v_args_1767_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1722_, v_xs_1723_, v_ys_1725_);
v___x_1768_ = lean_array_get_size(v_args_1767_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1768_, v_fnName_1724_, v_fixedParamPerm_1722_, v_args_1767_, v___x_1769_, v___x_1770_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec_ref(v_args_1767_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1807_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1806_; 
v_fst_1776_ = lean_ctor_get(v_a_1772_, 0);
v_snd_1777_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1779_ = v_a_1772_;
v_isShared_1780_ = v_isSharedCheck_1806_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_inc(v_fst_1776_);
lean_dec(v_a_1772_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1806_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_toCold_1788_; lean_object* v_options_1789_; uint8_t v_hasTrace_1790_; 
v_toCold_1788_ = lean_ctor_get(v___y_1729_, 0);
v_options_1789_ = lean_ctor_get(v_toCold_1788_, 2);
v_hasTrace_1790_ = lean_ctor_get_uint8(v_options_1789_, sizeof(void*)*1);
if (v_hasTrace_1790_ == 0)
{
goto v___jp_1781_;
}
else
{
lean_object* v_inheritedTraceOptions_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_inheritedTraceOptions_1791_ = lean_ctor_get(v_toCold_1788_, 11);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1793_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1794_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1791_, v_options_1789_, v___x_1793_);
if (v___x_1794_ == 0)
{
goto v___jp_1781_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1777_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_snd_1777_);
v___x_1797_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1792_, v___x_1796_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
goto v___jp_1781_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
lean_dec(v_fst_1776_);
lean_del_object(v___x_1774_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
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
}
v___jp_1781_:
{
lean_object* v___x_1783_; 
if (v_isShared_1780_ == 0)
{
v___x_1783_ = v___x_1779_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_fst_1776_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_snd_1777_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1783_);
v___x_1785_ = v___x_1774_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1808_, lean_object* v_fixedParamPerm_1809_, lean_object* v_xs_1810_, lean_object* v_fnName_1811_, lean_object* v_ys_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1808_, v_fixedParamPerm_1809_, v_xs_1810_, v_fnName_1811_, v_ys_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec_ref(v_x_1813_);
lean_dec_ref(v_xs_1810_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1820_, lean_object* v_fixedParamPerm_1821_, lean_object* v_xs_1822_, lean_object* v_value_1823_, lean_object* v_termMeasure_x3f_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___f_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1830_, 0, v_termMeasure_x3f_1824_);
lean_closure_set(v___f_1830_, 1, v_fixedParamPerm_1821_);
lean_closure_set(v___f_1830_, 2, v_xs_1822_);
lean_closure_set(v___f_1830_, 3, v_fnName_1820_);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1823_, v___f_1830_, v___x_1831_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1833_, lean_object* v_fixedParamPerm_1834_, lean_object* v_xs_1835_, lean_object* v_value_1836_, lean_object* v_termMeasure_x3f_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1833_, v_fixedParamPerm_1834_, v_xs_1835_, v_value_1836_, v_termMeasure_x3f_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1844_, lean_object* v_fnName_1845_, lean_object* v_fixedParamPerm_1846_, lean_object* v_args_1847_, lean_object* v_inst_1848_, lean_object* v_R_1849_, lean_object* v_a_1850_, lean_object* v_b_1851_, lean_object* v_c_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1844_, v_fnName_1845_, v_fixedParamPerm_1846_, v_args_1847_, v_a_1850_, v_b_1851_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1859_, lean_object* v_fnName_1860_, lean_object* v_fixedParamPerm_1861_, lean_object* v_args_1862_, lean_object* v_inst_1863_, lean_object* v_R_1864_, lean_object* v_a_1865_, lean_object* v_b_1866_, lean_object* v_c_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1859_, v_fnName_1860_, v_fixedParamPerm_1861_, v_args_1862_, v_inst_1863_, v_R_1864_, v_a_1865_, v_b_1866_, v_c_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v_args_1862_);
lean_dec(v_upperBound_1859_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
return v_x_1874_;
}
else
{
lean_object* v_key_1876_; lean_object* v_value_1877_; lean_object* v_tail_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1901_; 
v_key_1876_ = lean_ctor_get(v_x_1875_, 0);
v_value_1877_ = lean_ctor_get(v_x_1875_, 1);
v_tail_1878_ = lean_ctor_get(v_x_1875_, 2);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1880_ = v_x_1875_;
v_isShared_1881_ = v_isSharedCheck_1901_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_tail_1878_);
lean_inc(v_value_1877_);
lean_inc(v_key_1876_);
lean_dec(v_x_1875_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1901_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; uint64_t v___x_1885_; uint64_t v_fold_1886_; uint64_t v___x_1887_; uint64_t v___x_1888_; uint64_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1882_ = lean_array_get_size(v_x_1874_);
v___x_1883_ = lean_uint64_of_nat(v_key_1876_);
v___x_1884_ = 32ULL;
v___x_1885_ = lean_uint64_shift_right(v___x_1883_, v___x_1884_);
v_fold_1886_ = lean_uint64_xor(v___x_1883_, v___x_1885_);
v___x_1887_ = 16ULL;
v___x_1888_ = lean_uint64_shift_right(v_fold_1886_, v___x_1887_);
v___x_1889_ = lean_uint64_xor(v_fold_1886_, v___x_1888_);
v___x_1890_ = lean_uint64_to_usize(v___x_1889_);
v___x_1891_ = lean_usize_of_nat(v___x_1882_);
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_sub(v___x_1891_, v___x_1892_);
v___x_1894_ = lean_usize_land(v___x_1890_, v___x_1893_);
v___x_1895_ = lean_array_uget_borrowed(v_x_1874_, v___x_1894_);
lean_inc(v___x_1895_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 2, v___x_1895_);
v___x_1897_ = v___x_1880_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_key_1876_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_value_1877_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_array_uset(v_x_1874_, v___x_1894_, v___x_1897_);
v_x_1874_ = v___x_1898_;
v_x_1875_ = v_tail_1878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1902_, lean_object* v_source_1903_, lean_object* v_target_1904_){
_start:
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_array_get_size(v_source_1903_);
v___x_1906_ = lean_nat_dec_lt(v_i_1902_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_dec_ref(v_source_1903_);
lean_dec(v_i_1902_);
return v_target_1904_;
}
else
{
lean_object* v_es_1907_; lean_object* v___x_1908_; lean_object* v_source_1909_; lean_object* v_target_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_es_1907_ = lean_array_fget(v_source_1903_, v_i_1902_);
v___x_1908_ = lean_box(0);
v_source_1909_ = lean_array_fset(v_source_1903_, v_i_1902_, v___x_1908_);
v_target_1910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1904_, v_es_1907_);
v___x_1911_ = lean_unsigned_to_nat(1u);
v___x_1912_ = lean_nat_add(v_i_1902_, v___x_1911_);
lean_dec(v_i_1902_);
v_i_1902_ = v___x_1912_;
v_source_1903_ = v_source_1909_;
v_target_1904_ = v_target_1910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_nbuckets_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1915_ = lean_array_get_size(v_data_1914_);
v___x_1916_ = lean_unsigned_to_nat(2u);
v_nbuckets_1917_ = lean_nat_mul(v___x_1915_, v___x_1916_);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_mk_array(v_nbuckets_1917_, v___x_1919_);
v___x_1921_ = lean_array_propagate_mark(v_data_1914_, v___x_1920_);
v___x_1922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1918_, v_data_1914_, v___x_1921_);
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
uint8_t v_____do__lift_159__boxed_2141_; lean_object* v_res_2142_; 
v_____do__lift_159__boxed_2141_ = lean_unbox(v_____do__lift_2140_);
v_res_2142_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2137_, v_a_2138_, v_toPure_2139_, v_____do__lift_159__boxed_2141_);
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
uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = 1;
v___x_2233_ = lean_array_uget_borrowed(v_as_2223_, v_i_2224_);
lean_inc_ref(v_eq_2221_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v_a_2222_);
lean_inc(v___x_2233_);
v___x_2234_ = lean_apply_7(v_eq_2221_, v___x_2233_, v_a_2222_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, lean_box(0));
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2247_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2247_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2247_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_unbox(v_a_2235_);
lean_dec(v_a_2235_);
if (v___x_2239_ == 0)
{
size_t v___x_2240_; size_t v___x_2241_; 
lean_del_object(v___x_2237_);
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2224_, v___x_2240_);
v_i_2224_ = v___x_2241_;
goto _start;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
v___x_2243_ = lean_box(v___x_2232_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2243_);
v___x_2245_ = v___x_2237_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
return v___x_2234_;
}
}
else
{
uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v_a_2222_);
lean_dec_ref(v_eq_2221_);
v___x_2248_ = 0;
v___x_2249_ = lean_box(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2251_, lean_object* v_a_2252_, lean_object* v_as_2253_, lean_object* v_i_2254_, lean_object* v_stop_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
size_t v_i_boxed_2261_; size_t v_stop_boxed_2262_; lean_object* v_res_2263_; 
v_i_boxed_2261_ = lean_unbox_usize(v_i_2254_);
lean_dec(v_i_2254_);
v_stop_boxed_2262_ = lean_unbox_usize(v_stop_2255_);
lean_dec(v_stop_2255_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2251_, v_a_2252_, v_as_2253_, v_i_boxed_2261_, v_stop_boxed_2262_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_as_2253_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2264_, lean_object* v_a_2265_, uint8_t v_____do__lift_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
if (v_____do__lift_2266_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_array_push(v_b_2264_, v_a_2265_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec(v_a_2265_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_b_2264_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2277_, lean_object* v_a_2278_, lean_object* v_____do__lift_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v_____do__lift_1273__boxed_2285_; lean_object* v_res_2286_; 
v_____do__lift_1273__boxed_2285_ = lean_unbox(v_____do__lift_2279_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2277_, v_a_2278_, v_____do__lift_1273__boxed_2285_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2287_, lean_object* v_as_2288_, size_t v_sz_2289_, size_t v_i_2290_, lean_object* v_b_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_a_2298_; lean_object* v___y_2303_; uint8_t v___x_2322_; 
v___x_2322_ = lean_usize_dec_lt(v_i_2290_, v_sz_2289_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v_eq_2287_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_b_2291_);
return v___x_2323_;
}
else
{
lean_object* v___x_2324_; lean_object* v_a_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v_a_2325_ = lean_array_uget_borrowed(v_as_2288_, v_i_2290_);
v___x_2326_ = lean_array_get_size(v_b_2291_);
v___x_2327_ = lean_nat_dec_lt(v___x_2324_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_inc(v_a_2325_);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2291_, v_a_2325_, v___x_2327_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
v___y_2303_ = v___x_2328_;
goto v___jp_2302_;
}
else
{
if (v___x_2327_ == 0)
{
lean_object* v___x_2329_; 
lean_inc(v_a_2325_);
v___x_2329_ = lean_array_push(v_b_2291_, v_a_2325_);
v_a_2298_ = v___x_2329_;
goto v___jp_2297_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2326_);
lean_inc(v_a_2325_);
lean_inc_ref(v_eq_2287_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2287_, v_a_2325_, v_b_2291_, v___x_2330_, v___x_2331_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
lean_inc(v_a_2325_);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2291_, v_a_2325_, v___x_2334_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
v___y_2303_ = v___x_2335_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_b_2291_);
lean_dec_ref(v_eq_2287_);
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
}
v___jp_2297_:
{
size_t v___x_2299_; size_t v___x_2300_; 
v___x_2299_ = ((size_t)1ULL);
v___x_2300_ = lean_usize_add(v_i_2290_, v___x_2299_);
v_i_2290_ = v___x_2300_;
v_b_2291_ = v_a_2298_;
goto _start;
}
v___jp_2302_:
{
if (lean_obj_tag(v___y_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2313_; 
v_a_2304_ = lean_ctor_get(v___y_2303_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___y_2303_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2306_ = v___y_2303_;
v_isShared_2307_ = v_isSharedCheck_2313_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___y_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2313_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
if (lean_obj_tag(v_a_2304_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; 
lean_dec_ref(v_eq_2287_);
v_a_2308_ = lean_ctor_get(v_a_2304_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v_a_2304_, 1);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_a_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v_a_2312_; 
lean_del_object(v___x_2306_);
v_a_2312_ = lean_ctor_get(v_a_2304_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v_a_2304_, 1);
v_a_2298_ = v_a_2312_;
goto v___jp_2297_;
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_eq_2287_);
v_a_2314_ = lean_ctor_get(v___y_2303_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___y_2303_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___y_2303_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___y_2303_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
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
uint8_t v___x_3333_; 
v___x_3333_ = lean_nat_dec_le(v___x_3331_, v___x_3331_);
if (v___x_3333_ == 0)
{
if (v___x_3332_ == 0)
{
v___y_3325_ = v___x_3322_;
goto v___jp_3324_;
}
else
{
size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = ((size_t)0ULL);
v___x_3335_ = lean_usize_of_nat(v___x_3331_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3320_, v___x_3334_, v___x_3335_, v___x_3322_);
v___y_3325_ = v___x_3336_;
goto v___jp_3324_;
}
}
else
{
size_t v___x_3337_; size_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = ((size_t)0ULL);
v___x_3338_ = lean_usize_of_nat(v___x_3331_);
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3320_, v___x_3337_, v___x_3338_, v___x_3322_);
v___y_3325_ = v___x_3339_;
goto v___jp_3324_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3340_);
lean_dec_ref(v_xss_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3342_, lean_object* v_xss_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3345_, lean_object* v_xss_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3345_, v_xss_3346_);
lean_dec_ref(v_xss_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3348_, lean_object* v_as_3349_, size_t v_i_3350_, size_t v_stop_3351_, lean_object* v_b_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3349_, v_i_3350_, v_stop_3351_, v_b_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3354_, lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_stop_3357_, lean_object* v_b_3358_){
_start:
{
size_t v_i_boxed_3359_; size_t v_stop_boxed_3360_; lean_object* v_res_3361_; 
v_i_boxed_3359_ = lean_unbox_usize(v_i_3356_);
lean_dec(v_i_3356_);
v_stop_boxed_3360_ = lean_unbox_usize(v_stop_3357_);
lean_dec(v_stop_3357_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3354_, v_as_3355_, v_i_boxed_3359_, v_stop_boxed_3360_, v_b_3358_);
lean_dec_ref(v_as_3355_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3362_, size_t v_i_3363_, size_t v_stop_3364_, lean_object* v_b_3365_){
_start:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_usize_dec_eq(v_i_3363_, v_stop_3364_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; size_t v___x_3369_; size_t v___x_3370_; 
v___x_3367_ = lean_array_uget_borrowed(v_as_3362_, v_i_3363_);
v___x_3368_ = l_Array_append___redArg(v_b_3365_, v___x_3367_);
v___x_3369_ = ((size_t)1ULL);
v___x_3370_ = lean_usize_add(v_i_3363_, v___x_3369_);
v_i_3363_ = v___x_3370_;
v_b_3365_ = v___x_3368_;
goto _start;
}
else
{
return v_b_3365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3372_, lean_object* v_i_3373_, lean_object* v_stop_3374_, lean_object* v_b_3375_){
_start:
{
size_t v_i_boxed_3376_; size_t v_stop_boxed_3377_; lean_object* v_res_3378_; 
v_i_boxed_3376_ = lean_unbox_usize(v_i_3373_);
lean_dec(v_i_3373_);
v_stop_boxed_3377_ = lean_unbox_usize(v_stop_3374_);
lean_dec(v_stop_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3372_, v_i_boxed_3376_, v_stop_boxed_3377_, v_b_3375_);
lean_dec_ref(v_as_3372_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
if (lean_obj_tag(v_a_3379_) == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = l_List_reverse___redArg(v_a_3380_);
return v___x_3381_;
}
else
{
lean_object* v_head_3382_; lean_object* v_tail_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3393_; 
v_head_3382_ = lean_ctor_get(v_a_3379_, 0);
v_tail_3383_ = lean_ctor_get(v_a_3379_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_a_3379_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3385_ = v_a_3379_;
v_isShared_3386_ = v_isSharedCheck_3393_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_tail_3383_);
lean_inc(v_head_3382_);
lean_dec(v_a_3379_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3393_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3387_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3382_);
v___x_3388_ = l_Lean_MessageData_ofFormat(v___x_3387_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 1, v_a_3380_);
lean_ctor_set(v___x_3385_, 0, v___x_3388_);
v___x_3390_ = v___x_3385_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_a_3380_);
v___x_3390_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
v_a_3379_ = v_tail_3383_;
v_a_3380_ = v___x_3390_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3394_, size_t v_i_3395_, lean_object* v_bs_3396_){
_start:
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_usize_dec_lt(v_i_3395_, v_sz_3394_);
if (v___x_3397_ == 0)
{
return v_bs_3396_;
}
else
{
lean_object* v_v_3398_; lean_object* v___x_3399_; lean_object* v_bs_x27_3400_; lean_object* v___x_3401_; size_t v___x_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v_v_3398_ = lean_array_uget(v_bs_3396_, v_i_3395_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v_bs_x27_3400_ = lean_array_uset(v_bs_3396_, v_i_3395_, v___x_3399_);
v___x_3401_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3398_);
lean_dec(v_v_3398_);
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3395_, v___x_3402_);
v___x_3404_ = lean_array_uset(v_bs_x27_3400_, v_i_3395_, v___x_3401_);
v_i_3395_ = v___x_3403_;
v_bs_3396_ = v___x_3404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3406_, lean_object* v_i_3407_, lean_object* v_bs_3408_){
_start:
{
size_t v_sz_boxed_3409_; size_t v_i_boxed_3410_; lean_object* v_res_3411_; 
v_sz_boxed_3409_ = lean_unbox_usize(v_sz_3406_);
lean_dec(v_sz_3406_);
v_i_boxed_3410_ = lean_unbox_usize(v_i_3407_);
lean_dec(v_i_3407_);
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3409_, v_i_boxed_3410_, v_bs_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3412_, lean_object* v_as_3413_, size_t v_sz_3414_, size_t v_i_3415_, lean_object* v_b_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_usize_dec_lt(v_i_3415_, v_sz_3414_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_dec_ref(v_xs_3412_);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_b_3416_);
return v___x_3423_;
}
else
{
lean_object* v_snd_3424_; lean_object* v_snd_3425_; lean_object* v_snd_3426_; lean_object* v_snd_3427_; lean_object* v_fst_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3572_; 
v_snd_3424_ = lean_ctor_get(v_b_3416_, 1);
lean_inc(v_snd_3424_);
v_snd_3425_ = lean_ctor_get(v_snd_3424_, 1);
lean_inc(v_snd_3425_);
v_snd_3426_ = lean_ctor_get(v_snd_3425_, 1);
lean_inc(v_snd_3426_);
v_snd_3427_ = lean_ctor_get(v_snd_3426_, 1);
lean_inc(v_snd_3427_);
v_fst_3428_ = lean_ctor_get(v_b_3416_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_b_3416_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_b_3416_, 1);
lean_dec(v_unused_3573_);
v___x_3430_ = v_b_3416_;
v_isShared_3431_ = v_isSharedCheck_3572_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_fst_3428_);
lean_dec(v_b_3416_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3572_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_fst_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3570_; 
v_fst_3432_ = lean_ctor_get(v_snd_3424_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_snd_3424_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_snd_3424_, 1);
lean_dec(v_unused_3571_);
v___x_3434_ = v_snd_3424_;
v_isShared_3435_ = v_isSharedCheck_3570_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_fst_3432_);
lean_dec(v_snd_3424_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3570_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3568_; 
v_fst_3436_ = lean_ctor_get(v_snd_3425_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_snd_3425_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v_snd_3425_, 1);
lean_dec(v_unused_3569_);
v___x_3438_ = v_snd_3425_;
v_isShared_3439_ = v_isSharedCheck_3568_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_fst_3436_);
lean_dec(v_snd_3425_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3568_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3566_; 
v_fst_3440_ = lean_ctor_get(v_snd_3426_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_snd_3426_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_snd_3426_, 1);
lean_dec(v_unused_3567_);
v___x_3442_ = v_snd_3426_;
v_isShared_3443_ = v_isSharedCheck_3566_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_fst_3440_);
lean_dec(v_snd_3426_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3566_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_array_3444_; lean_object* v_start_3445_; lean_object* v_stop_3446_; uint8_t v___x_3447_; 
v_array_3444_ = lean_ctor_get(v_snd_3427_, 0);
v_start_3445_ = lean_ctor_get(v_snd_3427_, 1);
v_stop_3446_ = lean_ctor_get(v_snd_3427_, 2);
v___x_3447_ = lean_nat_dec_lt(v_start_3445_, v_stop_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3449_; 
lean_dec_ref(v_xs_3412_);
if (v_isShared_3443_ == 0)
{
v___x_3449_ = v___x_3442_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_snd_3427_);
v___x_3449_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3449_);
v___x_3451_ = v___x_3438_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3451_);
v___x_3453_ = v___x_3434_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3453_);
v___x_3455_ = v___x_3430_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
return v___x_3456_;
}
}
}
}
}
else
{
lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3562_; 
lean_inc(v_stop_3446_);
lean_inc(v_start_3445_);
lean_inc_ref(v_array_3444_);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_snd_3427_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; 
v_unused_3563_ = lean_ctor_get(v_snd_3427_, 2);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_snd_3427_, 1);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_snd_3427_, 0);
lean_dec(v_unused_3565_);
v___x_3462_ = v_snd_3427_;
v_isShared_3463_ = v_isSharedCheck_3562_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v_snd_3427_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3562_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_array_3464_; lean_object* v_start_3465_; lean_object* v_stop_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v_array_3464_ = lean_ctor_get(v_fst_3440_, 0);
v_start_3465_ = lean_ctor_get(v_fst_3440_, 1);
v_stop_3466_ = lean_ctor_get(v_fst_3440_, 2);
v___x_3467_ = lean_array_fget(v_array_3444_, v_start_3445_);
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_nat_add(v_start_3445_, v___x_3468_);
lean_dec(v_start_3445_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v___x_3469_);
v___x_3471_ = v___x_3462_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_array_3444_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_stop_3446_);
v___x_3471_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_nat_dec_lt(v_start_3465_, v_stop_3466_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3474_; 
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3412_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3471_);
v___x_3474_ = v___x_3442_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3471_);
v___x_3474_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3474_);
v___x_3476_ = v___x_3438_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3476_);
v___x_3478_ = v___x_3434_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3478_);
v___x_3480_ = v___x_3430_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
}
}
else
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3557_; 
lean_inc(v_stop_3466_);
lean_inc(v_start_3465_);
lean_inc_ref(v_array_3464_);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_fst_3440_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3558_ = lean_ctor_get(v_fst_3440_, 2);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_fst_3440_, 1);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_fst_3440_, 0);
lean_dec(v_unused_3560_);
v___x_3487_ = v_fst_3440_;
v_isShared_3488_ = v_isSharedCheck_3557_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v_fst_3440_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3557_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_array_3489_; lean_object* v_start_3490_; lean_object* v_stop_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v_array_3489_ = lean_ctor_get(v_fst_3436_, 0);
v_start_3490_ = lean_ctor_get(v_fst_3436_, 1);
v_stop_3491_ = lean_ctor_get(v_fst_3436_, 2);
v___x_3492_ = lean_array_fget(v_array_3464_, v_start_3465_);
v___x_3493_ = lean_nat_add(v_start_3465_, v___x_3468_);
lean_dec(v_start_3465_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3493_);
v___x_3495_ = v___x_3487_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_array_3464_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_stop_3466_);
v___x_3495_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_nat_dec_lt(v_start_3490_, v_stop_3491_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3498_; 
lean_dec(v___x_3492_);
lean_dec(v___x_3467_);
lean_dec_ref(v_xs_3412_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3471_);
lean_ctor_set(v___x_3442_, 0, v___x_3495_);
v___x_3498_ = v___x_3442_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3471_);
v___x_3498_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3498_);
v___x_3500_ = v___x_3438_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3500_);
v___x_3502_ = v___x_3434_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3502_);
v___x_3504_ = v___x_3430_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
}
}
}
else
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3552_; 
lean_inc(v_stop_3491_);
lean_inc(v_start_3490_);
lean_inc_ref(v_array_3489_);
lean_del_object(v___x_3430_);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_fst_3436_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3553_ = lean_ctor_get(v_fst_3436_, 2);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_fst_3436_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_fst_3436_, 0);
lean_dec(v_unused_3555_);
v___x_3511_ = v_fst_3436_;
v_isShared_3512_ = v_isSharedCheck_3552_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v_fst_3436_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3552_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_a_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v_a_3513_ = lean_array_uget_borrowed(v_as_3413_, v_i_3415_);
v___x_3514_ = lean_array_fget(v_array_3489_, v_start_3490_);
v___x_3515_ = lean_nat_add(v_start_3490_, v___x_3468_);
lean_dec(v_start_3490_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v___x_3515_);
v___x_3517_ = v___x_3511_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_array_3489_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_stop_3491_);
v___x_3517_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; 
lean_inc_ref(v_xs_3412_);
lean_inc(v_a_3513_);
v___x_3518_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3513_, v___x_3467_, v_xs_3412_, v___x_3514_, v___x_3492_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_fst_3520_; lean_object* v_snd_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3542_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_fst_3520_ = lean_ctor_get(v_a_3519_, 0);
v_snd_3521_ = lean_ctor_get(v_a_3519_, 1);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3523_ = v_a_3519_;
v_isShared_3524_ = v_isSharedCheck_3542_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_snd_3521_);
lean_inc(v_fst_3520_);
lean_dec(v_a_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3542_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_fst_3428_);
lean_ctor_set(v___x_3525_, 1, v_snd_3521_);
v___x_3526_ = lean_array_push(v_fst_3432_, v_fst_3520_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v___x_3471_);
lean_ctor_set(v___x_3523_, 0, v___x_3495_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3471_);
v___x_3528_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3528_);
lean_ctor_set(v___x_3442_, 0, v___x_3517_);
v___x_3530_ = v___x_3442_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3530_);
lean_ctor_set(v___x_3438_, 0, v___x_3526_);
v___x_3532_ = v___x_3438_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3534_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3532_);
lean_ctor_set(v___x_3434_, 0, v___x_3525_);
v___x_3534_ = v___x_3434_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
size_t v___x_3535_; size_t v___x_3536_; 
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_add(v_i_3415_, v___x_3535_);
v_i_3415_ = v___x_3536_;
v_b_3416_ = v___x_3534_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___x_3517_);
lean_dec_ref(v___x_3495_);
lean_dec_ref(v___x_3471_);
lean_del_object(v___x_3442_);
lean_del_object(v___x_3438_);
lean_del_object(v___x_3434_);
lean_dec(v_fst_3432_);
lean_dec(v_fst_3428_);
lean_dec_ref(v_xs_3412_);
v_a_3543_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3518_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3518_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3574_, lean_object* v_as_3575_, lean_object* v_sz_3576_, lean_object* v_i_3577_, lean_object* v_b_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
size_t v_sz_boxed_3584_; size_t v_i_boxed_3585_; lean_object* v_res_3586_; 
v_sz_boxed_3584_ = lean_unbox_usize(v_sz_3576_);
lean_dec(v_sz_3576_);
v_i_boxed_3585_ = lean_unbox_usize(v_i_3577_);
lean_dec(v_i_3577_);
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3574_, v_as_3575_, v_sz_boxed_3584_, v_i_boxed_3585_, v_b_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_as_3575_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
if (lean_obj_tag(v_a_3587_) == 0)
{
lean_object* v___x_3589_; 
v___x_3589_ = l_List_reverse___redArg(v_a_3588_);
return v___x_3589_;
}
else
{
lean_object* v_head_3590_; lean_object* v_tail_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3600_; 
v_head_3590_ = lean_ctor_get(v_a_3587_, 0);
v_tail_3591_ = lean_ctor_get(v_a_3587_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3593_ = v_a_3587_;
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_tail_3591_);
lean_inc(v_head_3590_);
lean_dec(v_a_3587_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3595_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3590_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 1, v_a_3588_);
lean_ctor_set(v___x_3593_, 0, v___x_3595_);
v___x_3597_ = v___x_3593_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_a_3588_);
v___x_3597_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
v_a_3587_ = v_tail_3591_;
v_a_3588_ = v___x_3597_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3601_, lean_object* v_j_3602_){
_start:
{
lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = lean_array_get_size(v_as_3601_);
v___x_3604_ = lean_nat_dec_lt(v_j_3602_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; 
lean_dec(v_j_3602_);
v___x_3605_ = lean_box(0);
return v___x_3605_;
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3606_ = lean_array_fget_borrowed(v_as_3601_, v_j_3602_);
v___x_3607_ = lean_array_get_size(v___x_3606_);
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = lean_nat_dec_eq(v___x_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_unsigned_to_nat(1u);
v___x_3611_ = lean_nat_add(v_j_3602_, v___x_3610_);
lean_dec(v_j_3602_);
v_j_3602_ = v___x_3611_;
goto _start;
}
else
{
lean_object* v___x_3613_; 
v___x_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3613_, 0, v_j_3602_);
return v___x_3613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3614_, lean_object* v_j_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3614_, v_j_3615_);
lean_dec_ref(v_as_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3617_, lean_object* v_as_3618_, size_t v_sz_3619_, size_t v_i_3620_, lean_object* v_b_3621_){
_start:
{
uint8_t v___x_3623_; 
v___x_3623_ = lean_usize_dec_lt(v_i_3620_, v_sz_3619_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref(v_a_3617_);
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v_b_3621_);
return v___x_3624_;
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; 
v_a_3625_ = lean_array_uget_borrowed(v_as_3618_, v_i_3620_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3617_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_a_3617_);
lean_ctor_set(v___x_3626_, 1, v_a_3625_);
v___x_3627_ = lean_array_push(v_b_3621_, v___x_3626_);
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3620_, v___x_3628_);
v_i_3620_ = v___x_3629_;
v_b_3621_ = v___x_3627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3631_, lean_object* v_as_3632_, lean_object* v_sz_3633_, lean_object* v_i_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3633_);
lean_dec(v_sz_3633_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3631_, v_as_3632_, v_sz_boxed_3637_, v_i_boxed_3638_, v_b_3635_);
lean_dec_ref(v_as_3632_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3640_, lean_object* v_xs_3641_, lean_object* v_as_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
uint8_t v___x_3651_; 
v___x_3651_ = lean_usize_dec_lt(v_i_3644_, v_sz_3643_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref(v_xs_3641_);
lean_dec_ref(v_a_3640_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_b_3645_);
return v___x_3652_;
}
else
{
lean_object* v_snd_3653_; lean_object* v_fst_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3697_; 
v_snd_3653_ = lean_ctor_get(v_b_3645_, 1);
v_fst_3654_ = lean_ctor_get(v_b_3645_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_b_3645_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3656_ = v_b_3645_;
v_isShared_3657_ = v_isSharedCheck_3697_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snd_3653_);
lean_inc(v_fst_3654_);
lean_dec(v_b_3645_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3697_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_array_3658_; lean_object* v_start_3659_; lean_object* v_stop_3660_; uint8_t v___x_3661_; 
v_array_3658_ = lean_ctor_get(v_snd_3653_, 0);
v_start_3659_ = lean_ctor_get(v_snd_3653_, 1);
v_stop_3660_ = lean_ctor_get(v_snd_3653_, 2);
v___x_3661_ = lean_nat_dec_lt(v_start_3659_, v_stop_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref(v_xs_3641_);
lean_dec_ref(v_a_3640_);
if (v_isShared_3657_ == 0)
{
v___x_3663_ = v___x_3656_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_fst_3654_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_snd_3653_);
v___x_3663_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
}
else
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3693_; 
lean_inc(v_stop_3660_);
lean_inc(v_start_3659_);
lean_inc_ref(v_array_3658_);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_snd_3653_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; 
v_unused_3694_ = lean_ctor_get(v_snd_3653_, 2);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_snd_3653_, 1);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_snd_3653_, 0);
lean_dec(v_unused_3696_);
v___x_3667_ = v_snd_3653_;
v_isShared_3668_ = v_isSharedCheck_3693_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v_snd_3653_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3693_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v_a_3669_ = lean_array_uget_borrowed(v_as_3642_, v_i_3644_);
v___x_3670_ = lean_array_fget(v_array_3658_, v_start_3659_);
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_nat_add(v_start_3659_, v___x_3671_);
lean_dec(v_start_3659_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 1, v___x_3672_);
v___x_3674_ = v___x_3667_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_array_3658_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_stop_3660_);
v___x_3674_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; 
lean_inc(v_a_3669_);
lean_inc_ref(v_xs_3641_);
lean_inc_ref(v_a_3640_);
v___x_3675_ = l_Lean_Elab_Structural_argsInGroup(v_a_3640_, v_xs_3641_, v_a_3669_, v___x_3670_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___x_3670_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v___x_3675_, 1);
v___x_3677_ = lean_array_push(v_fst_3654_, v_a_3676_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v___x_3674_);
lean_ctor_set(v___x_3656_, 0, v___x_3677_);
v___x_3679_ = v___x_3656_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___x_3674_);
v___x_3679_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
size_t v___x_3680_; size_t v___x_3681_; 
v___x_3680_ = ((size_t)1ULL);
v___x_3681_ = lean_usize_add(v_i_3644_, v___x_3680_);
v_i_3644_ = v___x_3681_;
v_b_3645_ = v___x_3679_;
goto _start;
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v___x_3674_);
lean_del_object(v___x_3656_);
lean_dec(v_fst_3654_);
lean_dec_ref(v_xs_3641_);
lean_dec_ref(v_a_3640_);
v_a_3684_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3675_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3675_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3698_, lean_object* v_xs_3699_, lean_object* v_as_3700_, lean_object* v_sz_3701_, lean_object* v_i_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
size_t v_sz_boxed_3709_; size_t v_i_boxed_3710_; lean_object* v_res_3711_; 
v_sz_boxed_3709_ = lean_unbox_usize(v_sz_3701_);
lean_dec(v_sz_3701_);
v_i_boxed_3710_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_res_3711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3698_, v_xs_3699_, v_as_3700_, v_sz_boxed_3709_, v_i_boxed_3710_, v_b_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_as_3700_);
return v_res_3711_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
return v___x_3716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
return v___x_3719_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
return v___x_3725_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3732_, lean_object* v_values_3733_, lean_object* v_xs_3734_, lean_object* v_fnNames_3735_, lean_object* v_as_3736_, size_t v_sz_3737_, size_t v_i_3738_, lean_object* v_b_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_a_3746_; uint8_t v___x_3750_; 
v___x_3750_ = lean_usize_dec_lt(v_i_3738_, v_sz_3737_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; 
lean_dec_ref(v_xs_3734_);
lean_dec_ref(v___x_3732_);
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v_b_3739_);
return v___x_3751_;
}
else
{
lean_object* v_fst_3752_; lean_object* v_snd_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3827_; 
v_fst_3752_ = lean_ctor_get(v_b_3739_, 0);
v_snd_3753_ = lean_ctor_get(v_b_3739_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_b_3739_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3755_ = v_b_3739_;
v_isShared_3756_ = v_isSharedCheck_3827_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_snd_3753_);
lean_inc(v_fst_3752_);
lean_dec(v_b_3739_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3827_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; lean_object* v_recArgInfoss_3758_; lean_object* v___x_3759_; lean_object* v_a_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3757_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3759_ = lean_box(0);
v_a_3760_ = lean_array_uget_borrowed(v_as_3736_, v_i_3738_);
v___x_3761_ = lean_array_get_size(v___x_3732_);
lean_inc_ref(v___x_3732_);
v___x_3762_ = l_Array_toSubarray___redArg(v___x_3732_, v___x_3757_, v___x_3761_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v___x_3762_);
lean_ctor_set(v___x_3755_, 0, v_recArgInfoss_3758_);
v___x_3764_ = v___x_3755_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_recArgInfoss_3758_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
size_t v_sz_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v_sz_3765_ = lean_array_size(v_values_3733_);
v___x_3766_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3734_);
lean_inc(v_a_3760_);
v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3760_, v_xs_3734_, v_values_3733_, v_sz_3765_, v___x_3766_, v___x_3764_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v_fst_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3816_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v_fst_3769_ = lean_ctor_get(v_a_3768_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3768_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v_a_3768_, 1);
lean_dec(v_unused_3817_);
v___x_3771_ = v_a_3768_;
v_isShared_3772_ = v_isSharedCheck_3816_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_fst_3769_);
lean_dec(v_a_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3816_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3769_, v___x_3757_);
if (lean_obj_tag(v___x_3773_) == 1)
{
lean_object* v_val_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
lean_dec(v_fst_3769_);
v_val_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_val_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3760_);
v___x_3776_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3760_);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_array_get_borrowed(v___x_3759_, v_fnNames_3735_, v_val_3774_);
lean_dec(v_val_3774_);
lean_inc(v___x_3780_);
v___x_3781_ = l_Lean_MessageData_ofName(v___x_3780_);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3779_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v_fst_3752_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_snd_3753_);
lean_ctor_set(v___x_3771_, 0, v___x_3785_);
v___x_3787_ = v___x_3771_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3785_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_snd_3753_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
v_a_3746_ = v___x_3787_;
goto v___jp_3745_;
}
}
else
{
lean_object* v___x_3789_; 
lean_dec(v___x_3773_);
v___x_3789_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3769_);
lean_dec(v_fst_3769_);
if (lean_obj_tag(v___x_3789_) == 1)
{
lean_object* v_val_3790_; size_t v_sz_3791_; lean_object* v___x_3792_; 
v_val_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v_sz_3791_ = lean_array_size(v_val_3790_);
lean_inc(v_a_3760_);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3760_, v_val_3790_, v_sz_3791_, v___x_3766_, v_snd_3753_);
lean_dec(v_val_3790_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_a_3793_);
lean_ctor_set(v___x_3771_, 0, v_fst_3752_);
v___x_3795_ = v___x_3771_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_fst_3752_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_a_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
v_a_3746_ = v___x_3795_;
goto v___jp_3745_;
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_del_object(v___x_3771_);
lean_dec(v_fst_3752_);
lean_dec_ref(v_xs_3734_);
lean_dec_ref(v___x_3732_);
v_a_3797_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3792_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3792_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
lean_dec(v___x_3789_);
v___x_3805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3760_);
v___x_3806_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3760_);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v_fst_3752_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_snd_3753_);
lean_ctor_set(v___x_3771_, 0, v___x_3812_);
v___x_3814_ = v___x_3771_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_snd_3753_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
v_a_3746_ = v___x_3814_;
goto v___jp_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_snd_3753_);
lean_dec(v_fst_3752_);
lean_dec_ref(v_xs_3734_);
lean_dec_ref(v___x_3732_);
v_a_3818_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3767_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3767_);
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
}
}
v___jp_3745_:
{
size_t v___x_3747_; size_t v___x_3748_; 
v___x_3747_ = ((size_t)1ULL);
v___x_3748_ = lean_usize_add(v_i_3738_, v___x_3747_);
v_i_3738_ = v___x_3748_;
v_b_3739_ = v_a_3746_;
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
lean_object* v_fst_3864_; lean_object* v_snd_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3939_; 
v_fst_3864_ = lean_ctor_get(v_b_3851_, 0);
v_snd_3865_ = lean_ctor_get(v_b_3851_, 1);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_b_3851_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3867_ = v_b_3851_;
v_isShared_3868_ = v_isSharedCheck_3939_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_snd_3865_);
lean_inc(v_fst_3864_);
lean_dec(v_b_3851_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3939_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v_recArgInfoss_3870_; lean_object* v___x_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3869_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3871_ = lean_box(0);
v_a_3872_ = lean_array_uget_borrowed(v_as_3848_, v_i_3850_);
v___x_3873_ = lean_array_get_size(v___x_3845_);
lean_inc_ref(v___x_3845_);
v___x_3874_ = l_Array_toSubarray___redArg(v___x_3845_, v___x_3869_, v___x_3873_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 1, v___x_3874_);
lean_ctor_set(v___x_3867_, 0, v_recArgInfoss_3870_);
v___x_3876_ = v___x_3867_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_recArgInfoss_3870_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
size_t v_sz_3877_; size_t v___x_3878_; lean_object* v___x_3879_; 
v_sz_3877_ = lean_array_size(v_values_3846_);
v___x_3878_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3844_);
lean_inc(v_a_3872_);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3872_, v_xs_3844_, v_values_3846_, v_sz_3877_, v___x_3878_, v___x_3876_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_fst_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3928_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v_fst_3881_ = lean_ctor_get(v_a_3880_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3880_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_a_3880_, 1);
lean_dec(v_unused_3929_);
v___x_3883_ = v_a_3880_;
v_isShared_3884_ = v_isSharedCheck_3928_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_fst_3881_);
lean_dec(v_a_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3928_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3881_, v___x_3869_);
if (lean_obj_tag(v___x_3885_) == 1)
{
lean_object* v_val_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
lean_dec(v_fst_3881_);
v_val_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_val_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3872_);
v___x_3888_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3872_);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_array_get_borrowed(v___x_3871_, v_fnNames_3847_, v_val_3886_);
lean_dec(v_val_3886_);
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
lean_ctor_set(v___x_3897_, 0, v_fst_3864_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v_snd_3865_);
lean_ctor_set(v___x_3883_, 0, v___x_3897_);
v___x_3899_ = v___x_3883_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_snd_3865_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
v_a_3858_ = v___x_3899_;
goto v___jp_3857_;
}
}
else
{
lean_object* v___x_3901_; 
lean_dec(v___x_3885_);
v___x_3901_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3881_);
lean_dec(v_fst_3881_);
if (lean_obj_tag(v___x_3901_) == 1)
{
lean_object* v_val_3902_; size_t v_sz_3903_; lean_object* v___x_3904_; 
v_val_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v_sz_3903_ = lean_array_size(v_val_3902_);
lean_inc(v_a_3872_);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3872_, v_val_3902_, v_sz_3903_, v___x_3878_, v_snd_3865_);
lean_dec(v_val_3902_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v_a_3905_);
lean_ctor_set(v___x_3883_, 0, v_fst_3864_);
v___x_3907_ = v___x_3883_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_fst_3864_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_a_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
v_a_3858_ = v___x_3907_;
goto v___jp_3857_;
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_del_object(v___x_3883_);
lean_dec(v_fst_3864_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_xs_3844_);
v_a_3909_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3904_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3904_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec(v___x_3901_);
v___x_3917_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3872_);
v___x_3918_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3872_);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3922_, 0, v_fst_3864_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v_snd_3865_);
lean_ctor_set(v___x_3883_, 0, v___x_3924_);
v___x_3926_ = v___x_3883_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_snd_3865_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v_a_3858_ = v___x_3926_;
goto v___jp_3857_;
}
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v_snd_3865_);
lean_dec(v_fst_3864_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_xs_3844_);
v_a_3930_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3879_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3879_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
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
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__2));
v___x_3962_ = l_Lean_MessageData_ofFormat(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__4));
v___x_3965_ = l_Lean_stringToMessageData(v___x_3964_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__7));
v___x_3970_ = l_Lean_stringToMessageData(v___x_3969_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9(void){
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
lean_object* v___x_3983_; lean_object* v_candidates_3984_; lean_object* v___x_3985_; lean_object* v_perms_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_report_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; size_t v_sz_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3983_ = lean_unsigned_to_nat(0u);
v_candidates_3984_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__0));
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
lean_ctor_set(v___x_3995_, 0, v_candidates_3984_);
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
lean_object* v_a_4000_; lean_object* v_snd_4001_; lean_object* v_toCold_4002_; lean_object* v_options_4003_; lean_object* v_fst_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4142_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_snd_4001_ = lean_ctor_get(v_a_4000_, 1);
lean_inc(v_snd_4001_);
v_toCold_4002_ = lean_ctor_get(v_a_3980_, 0);
v_options_4003_ = lean_ctor_get(v_toCold_4002_, 2);
v_fst_4004_ = lean_ctor_get(v_a_4000_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; 
v_unused_4143_ = lean_ctor_get(v_a_4000_, 1);
lean_dec(v_unused_4143_);
v___x_4006_ = v_a_4000_;
v_isShared_4007_ = v_isSharedCheck_4142_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_fst_4004_);
lean_dec(v_a_4000_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4142_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v_fst_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4140_; 
v_fst_4008_ = lean_ctor_get(v_snd_4001_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_snd_4001_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v_snd_4001_, 1);
lean_dec(v_unused_4141_);
v___x_4010_ = v_snd_4001_;
v_isShared_4011_ = v_isSharedCheck_4140_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_fst_4008_);
lean_dec(v_snd_4001_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4140_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v_inheritedTraceOptions_4012_; uint8_t v_hasTrace_4013_; size_t v_sz_4014_; lean_object* v___x_4015_; lean_object* v___y_4017_; lean_object* v_report_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___x_4065_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; 
v_inheritedTraceOptions_4012_ = lean_ctor_get(v_toCold_4002_, 11);
v_hasTrace_4013_ = lean_ctor_get_uint8(v_options_4003_, sizeof(void*)*1);
v_sz_4014_ = lean_array_size(v_fst_4008_);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4014_, v___x_3998_, v_fst_4008_);
v___x_4065_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4013_ == 0)
{
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4012_, v_options_4003_, v___x_4114_);
if (v___x_4115_ == 0)
{
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4116_; lean_object* v___y_4118_; lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v___x_4116_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4135_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4136_ = lean_array_get_size(v___x_4015_);
v___x_4137_ = lean_nat_dec_lt(v___x_3983_, v___x_4136_);
if (v___x_4137_ == 0)
{
v___y_4118_ = v___x_4135_;
goto v___jp_4117_;
}
else
{
size_t v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_usize_of_nat(v___x_4136_);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4015_, v___x_3998_, v___x_4138_, v___x_4135_);
v___y_4118_ = v___x_4139_;
goto v___jp_4117_;
}
v___jp_4117_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4119_ = lean_array_to_list(v___y_4118_);
v___x_4120_ = lean_box(0);
v___x_4121_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4119_, v___x_4120_);
v___x_4122_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__9, &l_Lean_Elab_Structural_findRecArgCandidates___closed__9_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__9);
v___x_4123_ = l_Lean_MessageData_joinSep(v___x_4121_, v___x_4122_);
v___x_4124_ = l_Lean_indentD(v___x_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4116_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4065_, v___x_4125_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_dec_ref_known(v___x_4126_, 1);
v___y_4105_ = v_a_3978_;
v___y_4106_ = v_a_3979_;
v___y_4107_ = v_a_3980_;
v___y_4108_ = v_a_3981_;
goto v___jp_4104_;
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v___x_4015_);
lean_del_object(v___x_4010_);
lean_del_object(v___x_4006_);
lean_dec(v_fst_4004_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
}
v___jp_4016_:
{
lean_object* v___x_4024_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 1, v_candidates_3984_);
lean_ctor_set(v___x_4010_, 0, v_report_4018_);
v___x_4024_ = v___x_4010_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_report_4018_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_candidates_3984_);
v___x_4024_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
size_t v_sz_4025_; lean_object* v___x_4026_; 
v_sz_4025_ = lean_array_size(v___y_4017_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3975_, v___x_4015_, v_values_3976_, v_fnNames_3973_, v___y_4017_, v_sz_4025_, v___x_3998_, v___x_4024_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec_ref(v___y_4017_);
lean_dec_ref(v_values_3976_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4043_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4043_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4043_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v_fst_4031_; lean_object* v_snd_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4042_; 
v_fst_4031_ = lean_ctor_get(v_a_4027_, 0);
v_snd_4032_ = lean_ctor_get(v_a_4027_, 1);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_4027_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4034_ = v_a_4027_;
v_isShared_4035_ = v_isSharedCheck_4042_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_snd_4032_);
lean_inc(v_fst_4031_);
lean_dec(v_a_4027_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4042_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v_fst_4031_);
lean_ctor_set(v___x_4034_, 0, v_snd_4032_);
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_snd_4032_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_fst_4031_);
v___x_4037_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4039_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4037_);
v___x_4039_ = v___x_4029_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4026_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4026_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
v___jp_4053_:
{
lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4059_ = lean_array_get_size(v___y_4054_);
v___x_4060_ = lean_nat_dec_eq(v___x_4059_, v___x_3983_);
if (v___x_4060_ == 0)
{
lean_del_object(v___x_4006_);
v___y_4017_ = v___y_4054_;
v_report_4018_ = v_fst_4004_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
v___y_4021_ = v___y_4057_;
v___y_4022_ = v___y_4058_;
goto v___jp_4016_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__3, &l_Lean_Elab_Structural_findRecArgCandidates___closed__3_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__3);
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 7);
lean_ctor_set(v___x_4006_, 1, v___x_4061_);
v___x_4063_ = v___x_4006_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_fst_4004_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
v___y_4017_ = v___y_4054_;
v_report_4018_ = v___x_4063_;
v___y_4019_ = v___y_4055_;
v___y_4020_ = v___y_4056_;
v___y_4021_ = v___y_4057_;
v___y_4022_ = v___y_4058_;
goto v___jp_4016_;
}
}
}
v___jp_4066_:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4071_, v___y_4069_, v___y_4068_, v___y_4067_, v___y_4070_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_toCold_4073_; lean_object* v_options_4074_; uint8_t v_hasTrace_4075_; 
v_toCold_4073_ = lean_ctor_get(v___y_4067_, 0);
v_options_4074_ = lean_ctor_get(v_toCold_4073_, 2);
v_hasTrace_4075_ = lean_ctor_get_uint8(v_options_4074_, sizeof(void*)*1);
if (v_hasTrace_4075_ == 0)
{
lean_object* v_a_4076_; 
v_a_4076_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4072_, 1);
v___y_4054_ = v_a_4076_;
v___y_4055_ = v___y_4069_;
v___y_4056_ = v___y_4068_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v___y_4070_;
goto v___jp_4053_;
}
else
{
lean_object* v_a_4077_; lean_object* v_inheritedTraceOptions_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v_a_4077_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4072_, 1);
v_inheritedTraceOptions_4078_ = lean_ctor_get(v_toCold_4073_, 11);
v___x_4079_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4078_, v_options_4074_, v___x_4079_);
if (v___x_4080_ == 0)
{
v___y_4054_ = v_a_4077_;
v___y_4055_ = v___y_4069_;
v___y_4056_ = v___y_4068_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v___y_4070_;
goto v___jp_4053_;
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4081_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__5, &l_Lean_Elab_Structural_findRecArgCandidates___closed__5_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__5);
lean_inc(v_a_4077_);
v___x_4082_ = lean_array_to_list(v_a_4077_);
v___x_4083_ = lean_box(0);
v___x_4084_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4082_, v___x_4083_);
v___x_4085_ = l_Lean_MessageData_ofList(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4081_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4065_, v___x_4086_, v___y_4069_, v___y_4068_, v___y_4067_, v___y_4070_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_dec_ref_known(v___x_4087_, 1);
v___y_4054_ = v_a_4077_;
v___y_4055_ = v___y_4069_;
v___y_4056_ = v___y_4068_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v___y_4070_;
goto v___jp_4053_;
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec(v_a_4077_);
lean_dec_ref(v___x_4015_);
lean_del_object(v___x_4010_);
lean_del_object(v___x_4006_);
lean_dec(v_fst_4004_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec_ref(v___x_4015_);
lean_del_object(v___x_4010_);
lean_del_object(v___x_4006_);
lean_dec(v_fst_4004_);
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4096_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4072_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4072_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
v___jp_4104_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_4110_ = lean_array_get_size(v___x_4015_);
v___x_4111_ = lean_nat_dec_lt(v___x_3983_, v___x_4110_);
if (v___x_4111_ == 0)
{
v___y_4067_ = v___y_4107_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4105_;
v___y_4070_ = v___y_4108_;
v___y_4071_ = v___x_4109_;
goto v___jp_4066_;
}
else
{
size_t v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_usize_of_nat(v___x_4110_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4015_, v___x_3998_, v___x_4112_, v___x_4109_);
v___y_4067_ = v___y_4107_;
v___y_4068_ = v___y_4106_;
v___y_4069_ = v___y_4105_;
v___y_4070_ = v___y_4108_;
v___y_4071_ = v___x_4113_;
goto v___jp_4066_;
}
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v_values_3976_);
lean_dec_ref(v_xs_3975_);
v_a_4144_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_3999_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_3999_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates___boxed(lean_object* v_fnNames_4152_, lean_object* v_fixedParamPerms_4153_, lean_object* v_xs_4154_, lean_object* v_values_4155_, lean_object* v_termMeasure_x3fs_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Elab_Structural_findRecArgCandidates(v_fnNames_4152_, v_fixedParamPerms_4153_, v_xs_4154_, v_values_4155_, v_termMeasure_x3fs_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec_ref(v_fnNames_4152_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(lean_object* v_a_4163_, lean_object* v_as_4164_, size_t v_sz_4165_, size_t v_i_4166_, lean_object* v_b_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_4163_, v_as_4164_, v_sz_4165_, v_i_4166_, v_b_4167_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(lean_object* v_a_4174_, lean_object* v_as_4175_, lean_object* v_sz_4176_, lean_object* v_i_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
size_t v_sz_boxed_4184_; size_t v_i_boxed_4185_; lean_object* v_res_4186_; 
v_sz_boxed_4184_ = lean_unbox_usize(v_sz_4176_);
lean_dec(v_sz_4176_);
v_i_boxed_4185_ = lean_unbox_usize(v_i_4177_);
lean_dec(v_i_4177_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_4174_, v_as_4175_, v_sz_boxed_4184_, v_i_boxed_4185_, v_b_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec_ref(v_as_4175_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(lean_object* v_constName_4187_, uint8_t v_skipRealize_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; lean_object* v_env_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4191_ = lean_st_ref_get(v___y_4189_);
v_env_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc_ref(v_env_4192_);
lean_dec(v___x_4191_);
v___x_4193_ = l_Lean_Environment_contains(v_env_4192_, v_constName_4187_, v_skipRealize_4188_);
v___x_4194_ = lean_box(v___x_4193_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(lean_object* v_constName_4196_, lean_object* v_skipRealize_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v_skipRealize_boxed_4200_; lean_object* v_res_4201_; 
v_skipRealize_boxed_4200_ = lean_unbox(v_skipRealize_4197_);
v_res_4201_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4196_, v_skipRealize_boxed_4200_, v___y_4198_);
lean_dec(v___y_4198_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(lean_object* v_constName_4202_, uint8_t v_skipRealize_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v_constName_4202_, v_skipRealize_4203_, v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(lean_object* v_constName_4210_, lean_object* v_skipRealize_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v_skipRealize_boxed_4217_; lean_object* v_res_4218_; 
v_skipRealize_boxed_4217_ = lean_unbox(v_skipRealize_4211_);
v_res_4218_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(v_constName_4210_, v_skipRealize_boxed_4217_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(lean_object* v_x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Meta_saveState___redArg(v___y_4221_, v___y_4223_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
lean_inc(v___y_4223_);
lean_inc_ref(v___y_4222_);
lean_inc(v___y_4221_);
lean_inc_ref(v___y_4220_);
v___x_4227_ = lean_apply_5(v_x_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, lean_box(0));
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_dec(v_a_4226_);
return v___x_4227_;
}
else
{
lean_object* v_a_4228_; uint8_t v___y_4230_; uint8_t v___x_4248_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
v___x_4248_ = l_Lean_Exception_isInterrupt(v_a_4228_);
if (v___x_4248_ == 0)
{
uint8_t v___x_4249_; 
lean_inc(v_a_4228_);
v___x_4249_ = l_Lean_Exception_isRuntime(v_a_4228_);
v___y_4230_ = v___x_4249_;
goto v___jp_4229_;
}
else
{
v___y_4230_ = v___x_4248_;
goto v___jp_4229_;
}
v___jp_4229_:
{
if (v___y_4230_ == 0)
{
lean_object* v___x_4231_; 
lean_dec_ref_known(v___x_4227_, 1);
v___x_4231_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4226_, v___y_4221_, v___y_4223_);
lean_dec(v_a_4226_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v___x_4231_, 0);
lean_dec(v_unused_4239_);
v___x_4233_ = v___x_4231_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v___x_4231_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 1);
lean_ctor_set(v___x_4233_, 0, v_a_4228_);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4228_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_a_4228_);
v_a_4240_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4231_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4231_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_dec(v_a_4228_);
lean_dec(v_a_4226_);
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec_ref(v_x_4219_);
v_a_4250_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4225_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4225_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4265_, lean_object* v_x_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4273_, v_x_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
return v_res_4280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
return v___x_4283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4286_ = l_Lean_stringToMessageData(v___x_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4287_, uint8_t v___x_4288_, lean_object* v_group_4289_, lean_object* v_k_4290_, lean_object* v_comb_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4287_, v___x_4288_, v___y_4295_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; uint8_t v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = lean_unbox(v_a_4298_);
lean_dec(v_a_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4301_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4289_);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4304_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4306_; 
lean_dec_ref_known(v___x_4305_, 1);
v___x_4306_ = lean_apply_6(v_k_4290_, v_comb_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, lean_box(0));
return v___x_4306_;
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v_comb_4291_);
lean_dec_ref(v_k_4290_);
v_a_4307_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4305_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4305_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v___x_4315_; 
lean_dec_ref(v_group_4289_);
v___x_4315_ = lean_apply_6(v_k_4290_, v_comb_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, lean_box(0));
return v___x_4315_;
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec_ref(v_comb_4291_);
lean_dec_ref(v_k_4290_);
lean_dec_ref(v_group_4289_);
v_a_4316_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4297_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4297_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4324_, lean_object* v___x_4325_, lean_object* v_group_4326_, lean_object* v_k_4327_, lean_object* v_comb_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
uint8_t v___x_4328__boxed_4334_; lean_object* v_res_4335_; 
v___x_4328__boxed_4334_ = lean_unbox(v___x_4325_);
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4324_, v___x_4328__boxed_4334_, v_group_4326_, v_k_4327_, v_comb_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v_res_4335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4338_ = l_Lean_stringToMessageData(v___x_4337_);
return v___x_4338_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4340_ = l_Lean_stringToMessageData(v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4341_, lean_object* v_fnNames_4342_, lean_object* v_xs_4343_, lean_object* v_values_4344_, lean_object* v_as_4345_, size_t v_sz_4346_, size_t v_i_4347_, lean_object* v_b_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
uint8_t v___x_4354_; 
v___x_4354_ = lean_usize_dec_lt(v_i_4347_, v_sz_4346_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
lean_dec_ref(v_values_4344_);
lean_dec_ref(v_xs_4343_);
lean_dec_ref(v_k_4341_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v_b_4348_);
return v___x_4355_;
}
else
{
lean_object* v_snd_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4426_; 
v_snd_4356_ = lean_ctor_get(v_b_4348_, 1);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_b_4348_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v_b_4348_, 0);
lean_dec(v_unused_4427_);
v___x_4358_ = v_b_4348_;
v_isShared_4359_ = v_isSharedCheck_4426_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_snd_4356_);
lean_dec(v_b_4348_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4426_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_a_4360_; lean_object* v_group_4361_; lean_object* v_comb_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4425_; 
v_a_4360_ = lean_array_uget(v_as_4345_, v_i_4347_);
v_group_4361_ = lean_ctor_get(v_a_4360_, 0);
v_comb_4362_ = lean_ctor_get(v_a_4360_, 1);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_a_4360_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4364_ = v_a_4360_;
v_isShared_4365_ = v_isSharedCheck_4425_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_comb_4362_);
lean_inc(v_group_4361_);
lean_dec(v_a_4360_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4425_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_toIndGroupInfo_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___f_4371_; lean_object* v___x_4372_; 
v_toIndGroupInfo_4366_ = lean_ctor_get(v_group_4361_, 0);
v___x_4367_ = lean_box(0);
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4366_, v___x_4368_);
v___x_4370_ = lean_box(v___x_4354_);
lean_inc_ref(v_comb_4362_);
lean_inc_ref(v_k_4341_);
v___f_4371_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4371_, 0, v___x_4369_);
lean_closure_set(v___f_4371_, 1, v___x_4370_);
lean_closure_set(v___f_4371_, 2, v_group_4361_);
lean_closure_set(v___f_4371_, 3, v_k_4341_);
lean_closure_set(v___f_4371_, 4, v_comb_4362_);
v___x_4372_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4371_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4384_; 
lean_del_object(v___x_4364_);
lean_dec_ref(v_comb_4362_);
lean_dec_ref(v_values_4344_);
lean_dec_ref(v_xs_4343_);
lean_dec_ref(v_k_4341_);
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4384_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4384_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4377_, 0, v_a_4373_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4377_);
v___x_4379_ = v___x_4358_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_snd_4356_);
v___x_4379_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4381_; 
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4379_);
v___x_4381_ = v___x_4375_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4424_; 
v_a_4385_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4387_ = v___x_4372_;
v_isShared_4388_ = v_isSharedCheck_4424_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4372_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4424_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___y_4390_; uint8_t v___x_4422_; 
v___x_4422_ = l_Lean_Exception_isInterrupt(v_a_4385_);
if (v___x_4422_ == 0)
{
uint8_t v___x_4423_; 
lean_inc(v_a_4385_);
v___x_4423_ = l_Lean_Exception_isRuntime(v_a_4385_);
v___y_4390_ = v___x_4423_;
goto v___jp_4389_;
}
else
{
v___y_4390_ = v___x_4422_;
goto v___jp_4389_;
}
v___jp_4389_:
{
if (v___y_4390_ == 0)
{
lean_object* v___x_4391_; 
lean_del_object(v___x_4387_);
lean_inc_ref(v_values_4344_);
lean_inc_ref(v_xs_4343_);
v___x_4391_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4342_, v_xs_4343_, v_values_4344_, v_comb_4362_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4365_ == 0)
{
lean_ctor_set_tag(v___x_4364_, 7);
lean_ctor_set(v___x_4364_, 1, v_a_4392_);
lean_ctor_set(v___x_4364_, 0, v___x_4393_);
v___x_4395_ = v___x_4364_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_a_4392_);
v___x_4395_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4396_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_Exception_toMessageData(v_a_4385_);
v___x_4399_ = l_Lean_indentD(v___x_4398_);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4397_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4400_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v_snd_4356_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v___x_4403_);
lean_ctor_set(v___x_4358_, 0, v___x_4367_);
v___x_4405_ = v___x_4358_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
size_t v___x_4406_; size_t v___x_4407_; 
v___x_4406_ = ((size_t)1ULL);
v___x_4407_ = lean_usize_add(v_i_4347_, v___x_4406_);
v_i_4347_ = v___x_4407_;
v_b_4348_ = v___x_4405_;
goto _start;
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4385_);
lean_del_object(v___x_4364_);
lean_del_object(v___x_4358_);
lean_dec(v_snd_4356_);
lean_dec_ref(v_values_4344_);
lean_dec_ref(v_xs_4343_);
lean_dec_ref(v_k_4341_);
v_a_4411_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4391_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4391_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
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
else
{
lean_object* v___x_4420_; 
lean_del_object(v___x_4364_);
lean_dec_ref(v_comb_4362_);
lean_del_object(v___x_4358_);
lean_dec(v_snd_4356_);
lean_dec_ref(v_values_4344_);
lean_dec_ref(v_xs_4343_);
lean_dec_ref(v_k_4341_);
if (v_isShared_4388_ == 0)
{
v___x_4420_ = v___x_4387_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4385_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4428_, lean_object* v_fnNames_4429_, lean_object* v_xs_4430_, lean_object* v_values_4431_, lean_object* v_as_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_b_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_boxed_4441_; size_t v_i_boxed_4442_; lean_object* v_res_4443_; 
v_sz_boxed_4441_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4442_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4428_, v_fnNames_4429_, v_xs_4430_, v_values_4431_, v_as_4432_, v_sz_boxed_4441_, v_i_boxed_4442_, v_b_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_as_4432_);
lean_dec_ref(v_fnNames_4429_);
return v_res_4443_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4446_ = l_Lean_stringToMessageData(v___x_4445_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4449_ = l_Lean_stringToMessageData(v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4450_, lean_object* v_xs_4451_, lean_object* v_values_4452_, lean_object* v_candidates_4453_, lean_object* v_k_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v_candidates_4460_; lean_object* v_report_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4521_; 
v_candidates_4460_ = lean_ctor_get(v_candidates_4453_, 0);
v_report_4461_ = lean_ctor_get(v_candidates_4453_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_candidates_4453_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4463_ = v_candidates_4453_;
v_isShared_4464_ = v_isSharedCheck_4521_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_report_4461_);
lean_inc(v_candidates_4460_);
lean_dec(v_candidates_4453_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4521_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4465_ = lean_box(0);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4465_);
v___x_4467_ = v___x_4463_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_report_4461_);
v___x_4467_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
size_t v_sz_4468_; size_t v___x_4469_; lean_object* v___x_4470_; 
v_sz_4468_ = lean_array_size(v_candidates_4460_);
v___x_4469_ = ((size_t)0ULL);
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4454_, v_fnNames_4450_, v_xs_4451_, v_values_4452_, v_candidates_4460_, v_sz_4468_, v___x_4469_, v___x_4467_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec_ref(v_candidates_4460_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4511_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4511_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4511_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_fst_4475_; 
v_fst_4475_ = lean_ctor_get(v_a_4471_, 0);
if (lean_obj_tag(v_fst_4475_) == 0)
{
lean_object* v_toCold_4476_; lean_object* v_options_4477_; lean_object* v_snd_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4505_; 
lean_del_object(v___x_4473_);
v_toCold_4476_ = lean_ctor_get(v_a_4457_, 0);
v_options_4477_ = lean_ctor_get(v_toCold_4476_, 2);
v_snd_4478_ = lean_ctor_get(v_a_4471_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_a_4471_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; 
v_unused_4506_ = lean_ctor_get(v_a_4471_, 0);
lean_dec(v_unused_4506_);
v___x_4480_ = v_a_4471_;
v_isShared_4481_ = v_isSharedCheck_4505_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_snd_4478_);
lean_dec(v_a_4471_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4505_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v_inheritedTraceOptions_4482_; uint8_t v_hasTrace_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v_inheritedTraceOptions_4482_ = lean_ctor_get(v_toCold_4476_, 11);
v_hasTrace_4483_ = lean_ctor_get_uint8(v_options_4477_, sizeof(void*)*1);
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4481_ == 0)
{
lean_ctor_set_tag(v___x_4480_, 7);
lean_ctor_set(v___x_4480_, 0, v___x_4484_);
v___x_4486_ = v___x_4480_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_snd_4478_);
v___x_4486_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
if (v_hasTrace_4483_ == 0)
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4486_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4488_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4489_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4482_, v_options_4477_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4486_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
return v___x_4491_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4486_);
v___x_4493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
lean_ctor_set(v___x_4493_, 1, v___x_4486_);
v___x_4494_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4488_, v___x_4493_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v___x_4495_; 
lean_dec_ref_known(v___x_4494_, 1);
v___x_4495_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4486_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
return v___x_4495_;
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec_ref(v___x_4486_);
v_a_4496_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4494_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4494_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
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
lean_object* v_val_4507_; lean_object* v___x_4509_; 
lean_inc_ref(v_fst_4475_);
lean_dec(v_a_4471_);
v_val_4507_ = lean_ctor_get(v_fst_4475_, 0);
lean_inc(v_val_4507_);
lean_dec_ref_known(v_fst_4475_, 1);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v_val_4507_);
v___x_4509_ = v___x_4473_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_val_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_a_4512_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4470_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4470_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4522_, lean_object* v_xs_4523_, lean_object* v_values_4524_, lean_object* v_candidates_4525_, lean_object* v_k_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4522_, v_xs_4523_, v_values_4524_, v_candidates_4525_, v_k_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_fnNames_4522_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4533_, lean_object* v_fnNames_4534_, lean_object* v_xs_4535_, lean_object* v_values_4536_, lean_object* v_candidates_4537_, lean_object* v_k_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4534_, v_xs_4535_, v_values_4536_, v_candidates_4537_, v_k_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4545_, lean_object* v_fnNames_4546_, lean_object* v_xs_4547_, lean_object* v_values_4548_, lean_object* v_candidates_4549_, lean_object* v_k_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4545_, v_fnNames_4546_, v_xs_4547_, v_values_4548_, v_candidates_4549_, v_k_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec_ref(v_fnNames_4546_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4557_, lean_object* v_k_4558_, lean_object* v_fnNames_4559_, lean_object* v_xs_4560_, lean_object* v_values_4561_, lean_object* v_as_4562_, size_t v_sz_4563_, size_t v_i_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4558_, v_fnNames_4559_, v_xs_4560_, v_values_4561_, v_as_4562_, v_sz_4563_, v_i_4564_, v_b_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4572_, lean_object* v_k_4573_, lean_object* v_fnNames_4574_, lean_object* v_xs_4575_, lean_object* v_values_4576_, lean_object* v_as_4577_, lean_object* v_sz_4578_, lean_object* v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4578_);
lean_dec(v_sz_4578_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4579_);
lean_dec(v_i_4579_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4572_, v_k_4573_, v_fnNames_4574_, v_xs_4575_, v_values_4576_, v_as_4577_, v_sz_boxed_4586_, v_i_boxed_4587_, v_b_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec_ref(v_as_4577_);
lean_dec_ref(v_fnNames_4574_);
return v_res_4588_;
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
