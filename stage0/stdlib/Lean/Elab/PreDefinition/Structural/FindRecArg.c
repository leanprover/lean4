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
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_nbuckets_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1913_ = lean_array_get_size(v_data_1912_);
v___x_1914_ = lean_unsigned_to_nat(2u);
v_nbuckets_1915_ = lean_nat_mul(v___x_1913_, v___x_1914_);
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_mk_array(v_nbuckets_1915_, v___x_1917_);
v___x_1919_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1916_, v_data_1912_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
uint8_t v___x_1922_; 
v___x_1922_ = 0;
return v___x_1922_;
}
else
{
lean_object* v_key_1923_; lean_object* v_tail_1924_; uint8_t v___x_1925_; 
v_key_1923_ = lean_ctor_get(v_x_1921_, 0);
v_tail_1924_ = lean_ctor_get(v_x_1921_, 2);
v___x_1925_ = lean_nat_dec_eq(v_key_1923_, v_a_1920_);
if (v___x_1925_ == 0)
{
v_x_1921_ = v_tail_1924_;
goto _start;
}
else
{
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1927_, lean_object* v_x_1928_){
_start:
{
uint8_t v_res_1929_; lean_object* v_r_1930_; 
v_res_1929_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1927_, v_x_1928_);
lean_dec(v_x_1928_);
lean_dec(v_a_1927_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1931_, lean_object* v_a_1932_, lean_object* v_b_1933_){
_start:
{
lean_object* v_size_1934_; lean_object* v_buckets_1935_; lean_object* v___x_1936_; uint64_t v___x_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v_fold_1940_; uint64_t v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; lean_object* v_bkt_1949_; uint8_t v___x_1950_; 
v_size_1934_ = lean_ctor_get(v_m_1931_, 0);
v_buckets_1935_ = lean_ctor_get(v_m_1931_, 1);
v___x_1936_ = lean_array_get_size(v_buckets_1935_);
v___x_1937_ = lean_uint64_of_nat(v_a_1932_);
v___x_1938_ = 32ULL;
v___x_1939_ = lean_uint64_shift_right(v___x_1937_, v___x_1938_);
v_fold_1940_ = lean_uint64_xor(v___x_1937_, v___x_1939_);
v___x_1941_ = 16ULL;
v___x_1942_ = lean_uint64_shift_right(v_fold_1940_, v___x_1941_);
v___x_1943_ = lean_uint64_xor(v_fold_1940_, v___x_1942_);
v___x_1944_ = lean_uint64_to_usize(v___x_1943_);
v___x_1945_ = lean_usize_of_nat(v___x_1936_);
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_sub(v___x_1945_, v___x_1946_);
v___x_1948_ = lean_usize_land(v___x_1944_, v___x_1947_);
v_bkt_1949_ = lean_array_uget_borrowed(v_buckets_1935_, v___x_1948_);
v___x_1950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1932_, v_bkt_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1971_; 
lean_inc_ref(v_buckets_1935_);
lean_inc(v_size_1934_);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_m_1931_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; lean_object* v_unused_1973_; 
v_unused_1972_ = lean_ctor_get(v_m_1931_, 1);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_m_1931_, 0);
lean_dec(v_unused_1973_);
v___x_1952_ = v_m_1931_;
v_isShared_1953_ = v_isSharedCheck_1971_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v_m_1931_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1971_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v_size_x27_1955_; lean_object* v___x_1956_; lean_object* v_buckets_x27_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1954_ = lean_unsigned_to_nat(1u);
v_size_x27_1955_ = lean_nat_add(v_size_1934_, v___x_1954_);
lean_dec(v_size_1934_);
lean_inc(v_bkt_1949_);
v___x_1956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1932_);
lean_ctor_set(v___x_1956_, 1, v_b_1933_);
lean_ctor_set(v___x_1956_, 2, v_bkt_1949_);
v_buckets_x27_1957_ = lean_array_uset(v_buckets_1935_, v___x_1948_, v___x_1956_);
v___x_1958_ = lean_unsigned_to_nat(4u);
v___x_1959_ = lean_nat_mul(v_size_x27_1955_, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(3u);
v___x_1961_ = lean_nat_div(v___x_1959_, v___x_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_array_get_size(v_buckets_x27_1957_);
v___x_1963_ = lean_nat_dec_le(v___x_1961_, v___x_1962_);
lean_dec(v___x_1961_);
if (v___x_1963_ == 0)
{
lean_object* v_val_1964_; lean_object* v___x_1966_; 
v_val_1964_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1957_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_val_1964_);
lean_ctor_set(v___x_1952_, 0, v_size_x27_1955_);
v___x_1966_ = v___x_1952_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_size_x27_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_val_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1969_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_buckets_x27_1957_);
lean_ctor_set(v___x_1952_, 0, v_size_x27_1955_);
v___x_1969_ = v___x_1952_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_size_x27_1955_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_buckets_x27_1957_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_dec(v_b_1933_);
lean_dec(v_a_1932_);
return v_m_1931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1974_, size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_b_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1978_ == 0)
{
return v_b_1977_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; 
v_a_1979_ = lean_array_uget_borrowed(v_as_1974_, v_i_1976_);
v___x_1980_ = lean_box(0);
lean_inc(v_a_1979_);
v___x_1981_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1977_, v_a_1979_, v___x_1980_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1976_, v___x_1982_);
v_i_1976_ = v___x_1983_;
v_b_1977_ = v___x_1981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1985_, lean_object* v_sz_1986_, lean_object* v_i_1987_, lean_object* v_b_1988_){
_start:
{
size_t v_sz_boxed_1989_; size_t v_i_boxed_1990_; lean_object* v_res_1991_; 
v_sz_boxed_1989_ = lean_unbox_usize(v_sz_1986_);
lean_dec(v_sz_1986_);
v_i_boxed_1990_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1985_, v_sz_boxed_1989_, v_i_boxed_1990_, v_b_1988_);
lean_dec_ref(v_as_1985_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_1992_, size_t v_sz_1993_, size_t v_i_1994_, lean_object* v_b_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_usize_dec_lt(v_i_1994_, v_sz_1993_);
if (v___x_1996_ == 0)
{
return v_b_1995_;
}
else
{
lean_object* v_a_1997_; lean_object* v_indicesPos_1998_; size_t v_sz_1999_; size_t v___x_2000_; lean_object* v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; 
v_a_1997_ = lean_array_uget_borrowed(v_as_1992_, v_i_1994_);
v_indicesPos_1998_ = lean_ctor_get(v_a_1997_, 3);
v_sz_1999_ = lean_array_size(v_indicesPos_1998_);
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_1998_, v_sz_1999_, v___x_2000_, v_b_1995_);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1994_, v___x_2002_);
v_i_1994_ = v___x_2003_;
v_b_1995_ = v___x_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2005_, lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_b_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2005_, v_sz_boxed_2009_, v_i_boxed_2010_, v_b_2008_);
lean_dec_ref(v_as_2005_);
return v_res_2011_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_buckets_2014_; lean_object* v___x_2015_; uint64_t v___x_2016_; uint64_t v___x_2017_; uint64_t v___x_2018_; uint64_t v_fold_2019_; uint64_t v___x_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_buckets_2014_ = lean_ctor_get(v_m_2012_, 1);
v___x_2015_ = lean_array_get_size(v_buckets_2014_);
v___x_2016_ = lean_uint64_of_nat(v_a_2013_);
v___x_2017_ = 32ULL;
v___x_2018_ = lean_uint64_shift_right(v___x_2016_, v___x_2017_);
v_fold_2019_ = lean_uint64_xor(v___x_2016_, v___x_2018_);
v___x_2020_ = 16ULL;
v___x_2021_ = lean_uint64_shift_right(v_fold_2019_, v___x_2020_);
v___x_2022_ = lean_uint64_xor(v_fold_2019_, v___x_2021_);
v___x_2023_ = lean_uint64_to_usize(v___x_2022_);
v___x_2024_ = lean_usize_of_nat(v___x_2015_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_sub(v___x_2024_, v___x_2025_);
v___x_2027_ = lean_usize_land(v___x_2023_, v___x_2026_);
v___x_2028_ = lean_array_uget_borrowed(v_buckets_2014_, v___x_2027_);
v___x_2029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2013_, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2030_, lean_object* v_a_2031_){
_start:
{
uint8_t v_res_2032_; lean_object* v_r_2033_; 
v_res_2032_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_m_2030_);
v_r_2033_ = lean_box(v_res_2032_);
return v_r_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2034_, lean_object* v_as_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_b_2038_){
_start:
{
lean_object* v_a_2040_; uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_lt(v_i_2037_, v_sz_2036_);
if (v___x_2044_ == 0)
{
return v_b_2038_;
}
else
{
lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2061_; 
v_fst_2045_ = lean_ctor_get(v_b_2038_, 0);
v_snd_2046_ = lean_ctor_get(v_b_2038_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_2038_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2048_ = v_b_2038_;
v_isShared_2049_ = v_isSharedCheck_2061_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snd_2046_);
lean_inc(v_fst_2045_);
lean_dec(v_b_2038_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2061_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_a_2050_; lean_object* v_recArgPos_2051_; uint8_t v___x_2052_; 
v_a_2050_ = lean_array_uget_borrowed(v_as_2035_, v_i_2037_);
v_recArgPos_2051_ = lean_ctor_get(v_a_2050_, 2);
v___x_2052_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2034_, v_recArgPos_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
lean_inc(v_a_2050_);
v___x_2053_ = lean_array_push(v_snd_2046_, v_a_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v___x_2053_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_fst_2045_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v_a_2040_ = v___x_2055_;
goto v___jp_2039_;
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_inc(v_a_2050_);
v___x_2057_ = lean_array_push(v_fst_2045_, v_a_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2057_);
v___x_2059_ = v___x_2048_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_snd_2046_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
v_a_2040_ = v___x_2059_;
goto v___jp_2039_;
}
}
}
}
v___jp_2039_:
{
size_t v___x_2041_; size_t v___x_2042_; 
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2037_, v___x_2041_);
v_i_2037_ = v___x_2042_;
v_b_2038_ = v_a_2040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2062_, lean_object* v_as_2063_, lean_object* v_sz_2064_, lean_object* v_i_2065_, lean_object* v_b_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2064_);
lean_dec(v_sz_2064_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2062_, v_as_2063_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2066_);
lean_dec_ref(v_as_2063_);
lean_dec_ref(v___x_2062_);
return v_res_2069_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_unsigned_to_nat(16u);
v___x_2072_ = lean_mk_array(v___x_2071_, v___x_2070_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_indicesPos_2075_; 
v___x_2073_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2074_ = lean_unsigned_to_nat(0u);
v_indicesPos_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2075_, 0, v___x_2074_);
lean_ctor_set(v_indicesPos_2075_, 1, v___x_2073_);
return v_indicesPos_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2078_){
_start:
{
lean_object* v_indicesPos_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_fst_2085_; lean_object* v_snd_2086_; lean_object* v___x_2087_; 
v_indicesPos_2079_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2080_ = lean_array_size(v_recArgInfos_2078_);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2078_, v_sz_2080_, v___x_2081_, v_indicesPos_2079_);
v___x_2083_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2082_, v_recArgInfos_2078_, v_sz_2080_, v___x_2081_, v___x_2083_);
lean_dec_ref(v___x_2082_);
v_fst_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_fst_2085_);
v_snd_2086_ = lean_ctor_get(v___x_2084_, 1);
lean_inc(v_snd_2086_);
lean_dec_ref(v___x_2084_);
v___x_2087_ = l_Array_append___redArg(v_snd_2086_, v_fst_2085_);
lean_dec(v_fst_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2088_);
lean_dec_ref(v_recArgInfos_2088_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2090_, lean_object* v_m_2091_, lean_object* v_a_2092_, lean_object* v_b_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2091_, v_a_2092_, v_b_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2095_, lean_object* v_m_2096_, lean_object* v_a_2097_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2096_, v_a_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2099_, lean_object* v_m_2100_, lean_object* v_a_2101_){
_start:
{
uint8_t v_res_2102_; lean_object* v_r_2103_; 
v_res_2102_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2099_, v_m_2100_, v_a_2101_);
lean_dec(v_a_2101_);
lean_dec_ref(v_m_2100_);
v_r_2103_ = lean_box(v_res_2102_);
return v_r_2103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2104_, lean_object* v_a_2105_, lean_object* v_x_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2105_, v_x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2108_, lean_object* v_a_2109_, lean_object* v_x_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2108_, v_a_2109_, v_x_2110_);
lean_dec(v_x_2110_);
lean_dec(v_a_2109_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2113_, lean_object* v_data_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2116_, lean_object* v_i_2117_, lean_object* v_source_2118_, lean_object* v_target_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2117_, v_source_2118_, v_target_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2122_, v_x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2125_, lean_object* v_a_2126_, lean_object* v_toPure_2127_, uint8_t v_____do__lift_2128_){
_start:
{
if (v_____do__lift_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_array_push(v___y_2125_, v_a_2126_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec(v_a_2126_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___y_2125_);
v___x_2133_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2132_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2134_, lean_object* v_a_2135_, lean_object* v_toPure_2136_, lean_object* v_____do__lift_2137_){
_start:
{
uint8_t v_____do__lift_159__boxed_2138_; lean_object* v_res_2139_; 
v_____do__lift_159__boxed_2138_ = lean_unbox(v_____do__lift_2137_);
v_res_2139_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2134_, v_a_2135_, v_toPure_2136_, v_____do__lift_159__boxed_2138_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2140_, lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_apply_2(v_eq_2140_, v_x_2142_, v_a_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2144_, lean_object* v___x_2145_, lean_object* v_toBind_2146_, lean_object* v_eq_2147_, lean_object* v_inst_2148_, lean_object* v_a_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___f_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
lean_inc(v_toPure_2144_);
lean_inc(v_a_2149_);
lean_inc_ref(v___y_2151_);
v___f_2152_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2152_, 0, v___y_2151_);
lean_closure_set(v___f_2152_, 1, v_a_2149_);
lean_closure_set(v___f_2152_, 2, v_toPure_2144_);
v___x_2153_ = lean_array_get_size(v___y_2151_);
v___x_2154_ = lean_nat_dec_lt(v___x_2145_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v___y_2151_);
lean_dec(v_a_2149_);
lean_dec_ref(v_inst_2148_);
lean_dec(v_eq_2147_);
v___x_2155_ = lean_box(v___x_2154_);
v___x_2156_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2155_);
v___x_2157_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2156_, v___f_2152_);
return v___x_2157_;
}
else
{
if (v___x_2154_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v___y_2151_);
lean_dec(v_a_2149_);
lean_dec_ref(v_inst_2148_);
lean_dec(v_eq_2147_);
v___x_2158_ = lean_box(v___x_2154_);
v___x_2159_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2158_);
v___x_2160_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2159_, v___f_2152_);
return v___x_2160_;
}
else
{
lean_object* v___f_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec(v_toPure_2144_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2161_, 0, v_eq_2147_);
lean_closure_set(v___f_2161_, 1, v_a_2149_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = lean_usize_of_nat(v___x_2153_);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2148_, v___f_2161_, v___y_2151_, v___x_2162_, v___x_2163_);
v___x_2165_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2164_, v___f_2152_);
return v___x_2165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2166_, lean_object* v___x_2167_, lean_object* v_toBind_2168_, lean_object* v_eq_2169_, lean_object* v_inst_2170_, lean_object* v_a_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2166_, v___x_2167_, v_toBind_2168_, v_eq_2169_, v_inst_2170_, v_a_2171_, v_x_2172_, v___y_2173_);
lean_dec(v___x_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2175_, lean_object* v_____s_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_apply_2(v_toPure_2175_, lean_box(0), v_____s_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2180_, lean_object* v_eq_2181_, lean_object* v_xs_2182_){
_start:
{
lean_object* v_toApplicative_2183_; lean_object* v_toBind_2184_; lean_object* v_toPure_2185_; lean_object* v___x_2186_; lean_object* v_ret_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; size_t v_sz_2190_; size_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_toApplicative_2183_ = lean_ctor_get(v_inst_2180_, 0);
v_toBind_2184_ = lean_ctor_get(v_inst_2180_, 1);
lean_inc_n(v_toBind_2184_, 2);
v_toPure_2185_ = lean_ctor_get(v_toApplicative_2183_, 1);
v___x_2186_ = lean_unsigned_to_nat(0u);
v_ret_2187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2180_);
lean_inc_n(v_toPure_2185_, 2);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2188_, 0, v_toPure_2185_);
lean_closure_set(v___f_2188_, 1, v___x_2186_);
lean_closure_set(v___f_2188_, 2, v_toBind_2184_);
lean_closure_set(v___f_2188_, 3, v_eq_2181_);
lean_closure_set(v___f_2188_, 4, v_inst_2180_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2189_, 0, v_toPure_2185_);
v_sz_2190_ = lean_array_size(v_xs_2182_);
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2180_, v_xs_2182_, v___f_2188_, v_sz_2190_, v___x_2191_, v_ret_2187_);
v___x_2193_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2192_, v___f_2189_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2194_, lean_object* v_00_u03b1_2195_, lean_object* v_inst_2196_, lean_object* v_eq_2197_, lean_object* v_xs_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2196_, v_eq_2197_, v_xs_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2200_, size_t v_i_2201_, lean_object* v_bs_2202_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
if (v___x_2203_ == 0)
{
return v_bs_2202_;
}
else
{
lean_object* v_v_2204_; lean_object* v_indGroupInst_2205_; lean_object* v___x_2206_; lean_object* v_bs_x27_2207_; size_t v___x_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
v_v_2204_ = lean_array_uget_borrowed(v_bs_2202_, v_i_2201_);
v_indGroupInst_2205_ = lean_ctor_get(v_v_2204_, 4);
lean_inc_ref(v_indGroupInst_2205_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v_bs_x27_2207_ = lean_array_uset(v_bs_2202_, v_i_2201_, v___x_2206_);
v___x_2208_ = ((size_t)1ULL);
v___x_2209_ = lean_usize_add(v_i_2201_, v___x_2208_);
v___x_2210_ = lean_array_uset(v_bs_x27_2207_, v_i_2201_, v_indGroupInst_2205_);
v_i_2201_ = v___x_2209_;
v_bs_2202_ = v___x_2210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_bs_2214_){
_start:
{
size_t v_sz_boxed_2215_; size_t v_i_boxed_2216_; lean_object* v_res_2217_; 
v_sz_boxed_2215_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2216_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2215_, v_i_boxed_2216_, v_bs_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2218_, lean_object* v_a_2219_, lean_object* v_as_2220_, size_t v_i_2221_, size_t v_stop_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_eq(v_i_2221_, v_stop_2222_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_array_uget_borrowed(v_as_2220_, v_i_2221_);
lean_inc_ref(v_eq_2218_);
lean_inc(v___y_2226_);
lean_inc_ref(v___y_2225_);
lean_inc(v___y_2224_);
lean_inc_ref(v___y_2223_);
lean_inc(v_a_2219_);
lean_inc(v___x_2229_);
v___x_2230_ = lean_apply_7(v_eq_2218_, v___x_2229_, v_a_2219_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, lean_box(0));
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_unbox(v_a_2231_);
if (v___x_2235_ == 0)
{
size_t v___x_2236_; size_t v___x_2237_; 
lean_del_object(v___x_2233_);
lean_dec(v_a_2231_);
v___x_2236_ = ((size_t)1ULL);
v___x_2237_ = lean_usize_add(v_i_2221_, v___x_2236_);
v_i_2221_ = v___x_2237_;
goto _start;
}
else
{
lean_object* v___x_2240_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_eq_2218_);
if (v_isShared_2234_ == 0)
{
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2231_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_dec(v_a_2219_);
lean_dec_ref(v_eq_2218_);
return v___x_2230_;
}
}
else
{
uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_eq_2218_);
v___x_2243_ = 0;
v___x_2244_ = lean_box(v___x_2243_);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2246_, lean_object* v_a_2247_, lean_object* v_as_2248_, lean_object* v_i_2249_, lean_object* v_stop_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
size_t v_i_boxed_2256_; size_t v_stop_boxed_2257_; lean_object* v_res_2258_; 
v_i_boxed_2256_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_stop_boxed_2257_ = lean_unbox_usize(v_stop_2250_);
lean_dec(v_stop_2250_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2246_, v_a_2247_, v_as_2248_, v_i_boxed_2256_, v_stop_boxed_2257_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_as_2248_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2259_, lean_object* v_a_2260_, uint8_t v_____do__lift_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
if (v_____do__lift_2261_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_array_push(v_b_2259_, v_a_2260_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_a_2260_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_b_2259_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2272_, lean_object* v_a_2273_, lean_object* v_____do__lift_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v_____do__lift_1269__boxed_2280_; lean_object* v_res_2281_; 
v_____do__lift_1269__boxed_2280_ = lean_unbox(v_____do__lift_2274_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2272_, v_a_2273_, v_____do__lift_1269__boxed_2280_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2282_, lean_object* v_as_2283_, size_t v_sz_2284_, size_t v_i_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_a_2293_; lean_object* v___y_2298_; uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_lt(v_i_2285_, v_sz_2284_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
lean_dec_ref(v_eq_2282_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_b_2286_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v_a_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2319_ = lean_unsigned_to_nat(0u);
v_a_2320_ = lean_array_uget_borrowed(v_as_2283_, v_i_2285_);
v___x_2321_ = lean_array_get_size(v_b_2286_);
v___x_2322_ = lean_nat_dec_lt(v___x_2319_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_inc(v_a_2320_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2286_, v_a_2320_, v___x_2322_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
v___y_2298_ = v___x_2323_;
goto v___jp_2297_;
}
else
{
if (v___x_2322_ == 0)
{
lean_object* v___x_2324_; 
lean_inc(v_a_2320_);
v___x_2324_ = lean_array_push(v_b_2286_, v_a_2320_);
v_a_2293_ = v___x_2324_;
goto v___jp_2292_;
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = lean_usize_of_nat(v___x_2321_);
lean_inc(v_a_2320_);
lean_inc_ref(v_eq_2282_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2282_, v_a_2320_, v_b_2286_, v___x_2325_, v___x_2326_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
lean_inc(v_a_2320_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2286_, v_a_2320_, v___x_2329_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
v___y_2298_ = v___x_2330_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec_ref(v_b_2286_);
lean_dec_ref(v_eq_2282_);
v_a_2331_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2327_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2327_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
v___jp_2292_:
{
size_t v___x_2294_; size_t v___x_2295_; 
v___x_2294_ = ((size_t)1ULL);
v___x_2295_ = lean_usize_add(v_i_2285_, v___x_2294_);
v_i_2285_ = v___x_2295_;
v_b_2286_ = v_a_2293_;
goto _start;
}
v___jp_2297_:
{
if (lean_obj_tag(v___y_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2308_; 
v_a_2299_ = lean_ctor_get(v___y_2298_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___y_2298_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2301_ = v___y_2298_;
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___y_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
if (lean_obj_tag(v_a_2299_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; 
lean_dec_ref(v_eq_2282_);
v_a_2303_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v_a_2299_, 1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_a_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v_a_2307_; 
lean_del_object(v___x_2301_);
v_a_2307_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v_a_2299_, 1);
v_a_2293_ = v_a_2307_;
goto v___jp_2292_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_eq_2282_);
v_a_2309_ = lean_ctor_get(v___y_2298_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___y_2298_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___y_2298_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___y_2298_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2339_, lean_object* v_as_2340_, lean_object* v_sz_2341_, lean_object* v_i_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
size_t v_sz_boxed_2349_; size_t v_i_boxed_2350_; lean_object* v_res_2351_; 
v_sz_boxed_2349_ = lean_unbox_usize(v_sz_2341_);
lean_dec(v_sz_2341_);
v_i_boxed_2350_ = lean_unbox_usize(v_i_2342_);
lean_dec(v_i_2342_);
v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2339_, v_as_2340_, v_sz_boxed_2349_, v_i_boxed_2350_, v_b_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_as_2340_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2352_, lean_object* v_xs_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_ret_2359_; size_t v_sz_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v_ret_2359_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2360_ = lean_array_size(v_xs_2353_);
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2352_, v_xs_2353_, v_sz_2360_, v___x_2361_, v_ret_2359_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2363_, lean_object* v_xs_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2363_, v_xs_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v_xs_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; size_t v_sz_2379_; size_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2378_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2379_ = lean_array_size(v_recArgInfos_2372_);
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2379_, v___x_2380_, v_recArgInfos_2372_);
v___x_2382_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2378_, v___x_2381_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec_ref(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2390_, lean_object* v_eq_2391_, lean_object* v_xs_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2391_, v_xs_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_eq_2400_, lean_object* v_xs_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2399_, v_eq_2400_, v_xs_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v_xs_2401_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2408_, lean_object* v_eq_2409_, lean_object* v_a_2410_, lean_object* v_as_2411_, size_t v_i_2412_, size_t v_stop_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2409_, v_a_2410_, v_as_2411_, v_i_2412_, v_stop_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_eq_2421_, lean_object* v_a_2422_, lean_object* v_as_2423_, lean_object* v_i_2424_, lean_object* v_stop_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
size_t v_i_boxed_2431_; size_t v_stop_boxed_2432_; lean_object* v_res_2433_; 
v_i_boxed_2431_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_stop_boxed_2432_ = lean_unbox_usize(v_stop_2425_);
lean_dec(v_stop_2425_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2420_, v_eq_2421_, v_a_2422_, v_as_2423_, v_i_boxed_2431_, v_stop_boxed_2432_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_as_2423_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2434_, lean_object* v_eq_2435_, lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2435_, v_as_2436_, v_sz_2437_, v_i_2438_, v_b_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2446_, lean_object* v_eq_2447_, lean_object* v_as_2448_, lean_object* v_sz_2449_, lean_object* v_i_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
size_t v_sz_boxed_2457_; size_t v_i_boxed_2458_; lean_object* v_res_2459_; 
v_sz_boxed_2457_ = lean_unbox_usize(v_sz_2449_);
lean_dec(v_sz_2449_);
v_i_boxed_2458_ = lean_unbox_usize(v_i_2450_);
lean_dec(v_i_2450_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2446_, v_eq_2447_, v_as_2448_, v_sz_boxed_2457_, v_i_boxed_2458_, v_b_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec_ref(v_as_2448_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v___x_2463_; 
v___x_2463_ = l_Lean_Expr_hasMVar(v_e_2460_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_e_2460_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v_mctx_2466_; lean_object* v___x_2467_; lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___x_2470_; lean_object* v_cache_2471_; lean_object* v_zetaDeltaFVarIds_2472_; lean_object* v_postponed_2473_; lean_object* v_diag_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2483_; 
v___x_2465_ = lean_st_ref_get(v___y_2461_);
v_mctx_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_mctx_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = l_Lean_instantiateMVarsCore(v_mctx_2466_, v_e_2460_);
v_fst_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_fst_2468_);
v_snd_2469_ = lean_ctor_get(v___x_2467_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v___x_2467_);
v___x_2470_ = lean_st_ref_take(v___y_2461_);
v_cache_2471_ = lean_ctor_get(v___x_2470_, 1);
v_zetaDeltaFVarIds_2472_ = lean_ctor_get(v___x_2470_, 2);
v_postponed_2473_ = lean_ctor_get(v___x_2470_, 3);
v_diag_2474_ = lean_ctor_get(v___x_2470_, 4);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2484_);
v___x_2476_ = v___x_2470_;
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_diag_2474_);
lean_inc(v_postponed_2473_);
lean_inc(v_zetaDeltaFVarIds_2472_);
lean_inc(v_cache_2471_);
lean_dec(v___x_2470_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v_snd_2469_);
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_snd_2469_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_cache_2471_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_zetaDeltaFVarIds_2472_);
lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_postponed_2473_);
lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_diag_2474_);
v___x_2479_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_st_ref_put(v___y_2461_, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_fst_2468_);
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2485_, v___y_2486_);
lean_dec(v___y_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2489_, v___y_2491_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2505_ = lean_unsigned_to_nat(109u);
v___x_2506_ = lean_unsigned_to_nat(216u);
v___x_2507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2509_ = l_mkPanicMessageWithDecl(v___x_2508_, v___x_2507_, v___x_2506_, v___x_2505_, v___x_2504_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2510_, size_t v_sz_2511_, size_t v_i_2512_, lean_object* v_bs_2513_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_lt(v_i_2512_, v_sz_2511_);
if (v___x_2514_ == 0)
{
return v_bs_2513_;
}
else
{
lean_object* v_v_2515_; lean_object* v___x_2516_; lean_object* v_bs_x27_2517_; lean_object* v___y_2519_; lean_object* v___x_2524_; 
v_v_2515_ = lean_array_uget(v_bs_2513_, v_i_2512_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v_bs_x27_2517_ = lean_array_uset(v_bs_2513_, v_i_2512_, v___x_2516_);
v___x_2524_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2510_, v_v_2515_);
lean_dec(v_v_2515_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2526_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2525_);
v___y_2519_ = v___x_2526_;
goto v___jp_2518_;
}
else
{
lean_object* v_val_2527_; 
v_val_2527_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2527_);
lean_dec_ref_known(v___x_2524_, 1);
v___y_2519_ = v_val_2527_;
goto v___jp_2518_;
}
v___jp_2518_:
{
size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2512_, v___x_2520_);
v___x_2522_ = lean_array_uset(v_bs_x27_2517_, v_i_2512_, v___y_2519_);
v_i_2512_ = v___x_2521_;
v_bs_2513_ = v___x_2522_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2528_, lean_object* v_sz_2529_, lean_object* v_i_2530_, lean_object* v_bs_2531_){
_start:
{
size_t v_sz_boxed_2532_; size_t v_i_boxed_2533_; lean_object* v_res_2534_; 
v_sz_boxed_2532_ = lean_unbox_usize(v_sz_2529_);
lean_dec(v_sz_2529_);
v_i_boxed_2533_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2528_, v_sz_boxed_2532_, v_i_boxed_2533_, v_bs_2531_);
lean_dec_ref(v___x_2528_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_bs_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_lt(v_i_2536_, v_sz_2535_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_bs_2537_);
return v___x_2544_;
}
else
{
lean_object* v_v_2545_; lean_object* v___x_2546_; 
v_v_2545_ = lean_array_uget_borrowed(v_bs_2537_, v_i_2536_);
lean_inc(v_v_2545_);
v___x_2546_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2545_, v___y_2539_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v_bs_x27_2549_; size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = lean_unsigned_to_nat(0u);
v_bs_x27_2549_ = lean_array_uset(v_bs_2537_, v_i_2536_, v___x_2548_);
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2536_, v___x_2550_);
v___x_2552_ = lean_array_uset(v_bs_x27_2549_, v_i_2536_, v_a_2547_);
v_i_2536_ = v___x_2551_;
v_bs_2537_ = v___x_2552_;
goto _start;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_bs_2537_);
v_a_2554_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2546_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2546_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_bs_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
size_t v_sz_boxed_2570_; size_t v_i_boxed_2571_; lean_object* v_res_2572_; 
v_sz_boxed_2570_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2571_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2570_, v_i_boxed_2571_, v_bs_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2573_, lean_object* v___x_2574_, lean_object* v_as_2575_, size_t v_i_2576_, size_t v_stop_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_eq(v_i_2576_, v_stop_2577_);
if (v___x_2578_ == 0)
{
uint8_t v___x_2579_; uint8_t v___y_2581_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2579_ = 1;
v___x_2585_ = lean_array_uget_borrowed(v_as_2575_, v_i_2576_);
v___x_2586_ = l_Lean_Expr_isFVar(v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2581_ = v_a_2573_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_nat_dec_eq(v___x_2574_, v___x_2587_);
v___y_2581_ = v___x_2588_;
goto v___jp_2580_;
}
v___jp_2580_:
{
if (v___y_2581_ == 0)
{
size_t v___x_2582_; size_t v___x_2583_; 
v___x_2582_ = ((size_t)1ULL);
v___x_2583_ = lean_usize_add(v_i_2576_, v___x_2582_);
v_i_2576_ = v___x_2583_;
goto _start;
}
else
{
return v___x_2579_;
}
}
}
else
{
uint8_t v___x_2589_; 
v___x_2589_ = 0;
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2590_, lean_object* v___x_2591_, lean_object* v_as_2592_, lean_object* v_i_2593_, lean_object* v_stop_2594_){
_start:
{
uint8_t v_a_7782__boxed_2595_; size_t v_i_boxed_2596_; size_t v_stop_boxed_2597_; uint8_t v_res_2598_; lean_object* v_r_2599_; 
v_a_7782__boxed_2595_ = lean_unbox(v_a_2590_);
v_i_boxed_2596_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_stop_boxed_2597_ = lean_unbox_usize(v_stop_2594_);
lean_dec(v_stop_2594_);
v_res_2598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7782__boxed_2595_, v___x_2591_, v_as_2592_, v_i_boxed_2596_, v_stop_boxed_2597_);
lean_dec_ref(v_as_2592_);
lean_dec(v___x_2591_);
v_r_2599_ = lean_box(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2600_, lean_object* v_ys_2601_, lean_object* v___x_2602_, lean_object* v_recArgInfo_2603_, lean_object* v___x_2604_, lean_object* v___x_2605_, lean_object* v_group_2606_, lean_object* v___x_2607_, lean_object* v_as_2608_, size_t v_sz_2609_, size_t v_i_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_a_2618_; uint8_t v___x_2622_; 
v___x_2622_ = lean_usize_dec_lt(v_i_2610_, v_sz_2609_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_b_2611_);
return v___x_2623_;
}
else
{
lean_object* v_snd_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2780_; 
v_snd_2624_ = lean_ctor_get(v_b_2611_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_b_2611_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; 
v_unused_2781_ = lean_ctor_get(v_b_2611_, 0);
lean_dec(v_unused_2781_);
v___x_2626_ = v_b_2611_;
v_isShared_2627_ = v_isSharedCheck_2780_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2624_);
lean_dec(v_b_2611_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2780_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_next_2628_; lean_object* v_upperBound_2629_; lean_object* v___x_2630_; 
v_next_2628_ = lean_ctor_get(v_snd_2624_, 0);
lean_inc(v_next_2628_);
v_upperBound_2629_ = lean_ctor_get(v_snd_2624_, 1);
v___x_2630_ = lean_box(0);
if (lean_obj_tag(v_next_2628_) == 0)
{
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
goto v___jp_2631_;
}
else
{
lean_object* v_val_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2779_; 
v_val_2636_ = lean_ctor_get(v_next_2628_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_next_2628_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2638_ = v_next_2628_;
v_isShared_2639_ = v_isSharedCheck_2779_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_val_2636_);
lean_dec(v_next_2628_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2779_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_lt(v_val_2636_, v_upperBound_2629_);
if (v___x_2640_ == 0)
{
lean_del_object(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
goto v___jp_2631_;
}
else
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2776_; 
lean_inc(v_upperBound_2629_);
lean_del_object(v___x_2626_);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_snd_2624_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; 
v_unused_2777_ = lean_ctor_get(v_snd_2624_, 1);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_snd_2624_, 0);
lean_dec(v_unused_2778_);
v___x_2642_ = v_snd_2624_;
v_isShared_2643_ = v_isSharedCheck_2776_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v_snd_2624_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2776_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; 
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc(v___y_2613_);
lean_inc_ref(v___y_2612_);
lean_inc_ref(v___x_2600_);
v___x_2644_ = lean_infer_type(v___x_2600_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = l_Lean_Meta_whnfD(v_a_2645_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v_a_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v_a_2648_ = lean_array_uget_borrowed(v_as_2608_, v_i_2610_);
v___x_2649_ = 0;
lean_inc(v_a_2648_);
v___x_2650_ = l_Lean_Meta_forallMetaTelescope(v_a_2648_, v___x_2649_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_snd_2652_; lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2751_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_snd_2652_ = lean_ctor_get(v_a_2651_, 1);
v_fst_2653_ = lean_ctor_get(v_a_2651_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2655_ = v_a_2651_;
v_isShared_2656_ = v_isSharedCheck_2751_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2653_);
lean_dec(v_a_2651_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2751_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2749_; 
v_snd_2657_ = lean_ctor_get(v_snd_2652_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_snd_2652_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; 
v_unused_2750_ = lean_ctor_get(v_snd_2652_, 0);
lean_dec(v_unused_2750_);
v___x_2659_ = v_snd_2652_;
v_isShared_2660_ = v_isSharedCheck_2749_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_dec(v_snd_2652_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2749_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2657_, v_a_2647_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_val_2636_, v___x_2663_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2664_);
v___x_2666_ = v___x_2638_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2666_);
v___x_2668_ = v___x_2642_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_upperBound_2629_);
v___x_2668_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_unbox(v_a_2662_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2671_; 
lean_dec(v_a_2662_);
lean_del_object(v___x_2655_);
lean_dec(v_fst_2653_);
lean_dec(v_val_2636_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2668_);
lean_ctor_set(v___x_2659_, 0, v___x_2630_);
v___x_2671_ = v___x_2659_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2668_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
v_a_2618_ = v___x_2671_;
goto v___jp_2617_;
}
}
else
{
size_t v_sz_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v_sz_2673_ = lean_array_size(v_fst_2653_);
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2673_, v___x_2674_, v_fst_2653_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = lean_array_get_size(v_a_2676_);
v___x_2724_ = lean_nat_dec_lt(v___x_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_dec(v_a_2662_);
lean_del_object(v___x_2655_);
goto v___jp_2677_;
}
else
{
if (v___x_2724_ == 0)
{
lean_dec(v_a_2662_);
lean_del_object(v___x_2655_);
goto v___jp_2677_;
}
else
{
size_t v___x_2725_; uint8_t v___x_2726_; uint8_t v___x_2727_; 
v___x_2725_ = lean_usize_of_nat(v___x_2723_);
v___x_2726_ = lean_unbox(v_a_2662_);
lean_dec(v_a_2662_);
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2726_, v___x_2607_, v_a_2676_, v___x_2674_, v___x_2725_);
if (v___x_2727_ == 0)
{
lean_del_object(v___x_2655_);
goto v___jp_2677_;
}
else
{
lean_object* v___x_2729_; 
lean_dec(v_a_2676_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2636_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2668_);
lean_ctor_set(v___x_2655_, 0, v___x_2630_);
v___x_2729_ = v___x_2655_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2668_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v_a_2618_ = v___x_2729_;
goto v___jp_2617_;
}
}
}
}
v___jp_2677_:
{
uint8_t v___x_2678_; 
v___x_2678_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2676_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2680_; 
lean_dec(v_a_2676_);
lean_dec(v_val_2636_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2668_);
lean_ctor_set(v___x_2659_, 0, v___x_2630_);
v___x_2680_ = v___x_2659_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2668_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v_a_2618_ = v___x_2680_;
goto v___jp_2617_;
}
}
else
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2601_, v_a_2676_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2713_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2713_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2713_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
if (lean_obj_tag(v_a_2683_) == 1)
{
lean_object* v___x_2688_; 
lean_dec_ref_known(v_a_2683_, 1);
lean_del_object(v___x_2685_);
lean_dec(v_a_2676_);
lean_dec(v_val_2636_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2668_);
lean_ctor_set(v___x_2659_, 0, v___x_2630_);
v___x_2688_ = v___x_2659_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2668_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v_a_2618_ = v___x_2688_;
goto v___jp_2617_;
}
}
else
{
lean_object* v_fnName_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2683_);
lean_dec_ref(v___x_2600_);
v_fnName_2690_ = lean_ctor_get(v_recArgInfo_2603_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_recArgInfo_2603_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2708_ = lean_ctor_get(v_recArgInfo_2603_, 5);
lean_dec(v_unused_2708_);
v_unused_2709_ = lean_ctor_get(v_recArgInfo_2603_, 4);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_recArgInfo_2603_, 3);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_recArgInfo_2603_, 2);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_recArgInfo_2603_, 1);
lean_dec(v_unused_2712_);
v___x_2692_ = v_recArgInfo_2603_;
v_isShared_2693_ = v_isSharedCheck_2707_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_fnName_2690_);
lean_dec(v_recArgInfo_2603_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2707_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
size_t v_sz_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v_sz_2694_ = lean_array_size(v_a_2676_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2602_, v_sz_2694_, v___x_2674_, v_a_2676_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 5, v_val_2636_);
lean_ctor_set(v___x_2692_, 4, v_group_2606_);
lean_ctor_set(v___x_2692_, 3, v___x_2695_);
lean_ctor_set(v___x_2692_, 2, v___x_2605_);
lean_ctor_set(v___x_2692_, 1, v___x_2604_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_fnName_2690_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_group_2606_);
lean_ctor_set(v_reuseFailAlloc_2706_, 5, v_val_2636_);
v___x_2697_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2668_);
lean_ctor_set(v___x_2659_, 0, v___x_2699_);
v___x_2701_ = v___x_2659_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2668_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2701_);
v___x_2703_ = v___x_2685_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2676_);
lean_dec_ref(v___x_2668_);
lean_del_object(v___x_2659_);
lean_dec(v_val_2636_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2714_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2682_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2682_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v___x_2668_);
lean_dec(v_a_2662_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
lean_dec(v_val_2636_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2731_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2675_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2675_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
lean_dec(v_fst_2653_);
lean_del_object(v___x_2642_);
lean_del_object(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec(v_upperBound_2629_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2741_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2661_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2661_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2647_);
lean_del_object(v___x_2642_);
lean_del_object(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec(v_upperBound_2629_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2752_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2650_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2650_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_del_object(v___x_2642_);
lean_del_object(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec(v_upperBound_2629_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2760_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2646_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2646_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_del_object(v___x_2642_);
lean_del_object(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec(v_upperBound_2629_);
lean_dec_ref(v_group_2606_);
lean_dec(v___x_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v_recArgInfo_2603_);
lean_dec_ref(v___x_2600_);
v_a_2768_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2644_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2644_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
v___jp_2631_:
{
lean_object* v___x_2633_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2630_);
v___x_2633_ = v___x_2626_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_snd_2624_);
v___x_2633_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
}
}
}
v___jp_2617_:
{
size_t v___x_2619_; size_t v___x_2620_; 
v___x_2619_ = ((size_t)1ULL);
v___x_2620_ = lean_usize_add(v_i_2610_, v___x_2619_);
v_i_2610_ = v___x_2620_;
v_b_2611_ = v_a_2618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2782_ = _args[0];
lean_object* v_ys_2783_ = _args[1];
lean_object* v___x_2784_ = _args[2];
lean_object* v_recArgInfo_2785_ = _args[3];
lean_object* v___x_2786_ = _args[4];
lean_object* v___x_2787_ = _args[5];
lean_object* v_group_2788_ = _args[6];
lean_object* v___x_2789_ = _args[7];
lean_object* v_as_2790_ = _args[8];
lean_object* v_sz_2791_ = _args[9];
lean_object* v_i_2792_ = _args[10];
lean_object* v_b_2793_ = _args[11];
lean_object* v___y_2794_ = _args[12];
lean_object* v___y_2795_ = _args[13];
lean_object* v___y_2796_ = _args[14];
lean_object* v___y_2797_ = _args[15];
lean_object* v___y_2798_ = _args[16];
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2782_, v_ys_2783_, v___x_2784_, v_recArgInfo_2785_, v___x_2786_, v___x_2787_, v_group_2788_, v___x_2789_, v_as_2790_, v_sz_boxed_2799_, v_i_boxed_2800_, v_b_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v_as_2790_);
lean_dec(v___x_2789_);
lean_dec_ref(v___x_2784_);
lean_dec_ref(v_ys_2783_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2802_, lean_object* v___x_2803_, lean_object* v_ys_2804_, lean_object* v___x_2805_, lean_object* v_recArgInfo_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v_group_2809_, lean_object* v_as_2810_, size_t v_sz_2811_, size_t v_i_2812_, lean_object* v_b_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_a_2820_; uint8_t v___x_2824_; 
v___x_2824_ = lean_usize_dec_lt(v_i_2812_, v_sz_2811_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_b_2813_);
return v___x_2825_;
}
else
{
lean_object* v_snd_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2982_; 
v_snd_2826_ = lean_ctor_get(v_b_2813_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_b_2813_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_b_2813_, 0);
lean_dec(v_unused_2983_);
v___x_2828_ = v_b_2813_;
v_isShared_2829_ = v_isSharedCheck_2982_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_snd_2826_);
lean_dec(v_b_2813_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2982_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_next_2830_; lean_object* v_upperBound_2831_; lean_object* v___x_2832_; 
v_next_2830_ = lean_ctor_get(v_snd_2826_, 0);
lean_inc(v_next_2830_);
v_upperBound_2831_ = lean_ctor_get(v_snd_2826_, 1);
v___x_2832_ = lean_box(0);
if (lean_obj_tag(v_next_2830_) == 0)
{
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
goto v___jp_2833_;
}
else
{
lean_object* v_val_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2981_; 
v_val_2838_ = lean_ctor_get(v_next_2830_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_next_2830_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2840_ = v_next_2830_;
v_isShared_2841_ = v_isSharedCheck_2981_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_val_2838_);
lean_dec(v_next_2830_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2981_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_nat_dec_lt(v_val_2838_, v_upperBound_2831_);
if (v___x_2842_ == 0)
{
lean_del_object(v___x_2840_);
lean_dec(v_val_2838_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
goto v___jp_2833_;
}
else
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2978_; 
lean_inc(v_upperBound_2831_);
lean_del_object(v___x_2828_);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_snd_2826_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; 
v_unused_2979_ = lean_ctor_get(v_snd_2826_, 1);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_snd_2826_, 0);
lean_dec(v_unused_2980_);
v___x_2844_ = v_snd_2826_;
v_isShared_2845_ = v_isSharedCheck_2978_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v_snd_2826_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2978_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; 
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc_ref(v___x_2802_);
v___x_2846_ = lean_infer_type(v___x_2802_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_Meta_whnfD(v_a_2847_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v_a_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v_a_2850_ = lean_array_uget_borrowed(v_as_2810_, v_i_2812_);
v___x_2851_ = 0;
lean_inc(v_a_2850_);
v___x_2852_ = l_Lean_Meta_forallMetaTelescope(v_a_2850_, v___x_2851_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_snd_2854_; lean_object* v_fst_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2953_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v_snd_2854_ = lean_ctor_get(v_a_2853_, 1);
v_fst_2855_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2857_ = v_a_2853_;
v_isShared_2858_ = v_isSharedCheck_2953_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_snd_2854_);
lean_inc(v_fst_2855_);
lean_dec(v_a_2853_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2953_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_snd_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2951_; 
v_snd_2859_ = lean_ctor_get(v_snd_2854_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_snd_2854_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v_snd_2854_, 0);
lean_dec(v_unused_2952_);
v___x_2861_ = v_snd_2854_;
v_isShared_2862_ = v_isSharedCheck_2951_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_snd_2859_);
lean_dec(v_snd_2854_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2951_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2859_, v_a_2849_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = lean_unsigned_to_nat(1u);
v___x_2866_ = lean_nat_add(v_val_2838_, v___x_2865_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2866_);
v___x_2868_ = v___x_2840_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2868_);
v___x_2870_ = v___x_2844_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_upperBound_2831_);
v___x_2870_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_unbox(v_a_2864_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2873_; 
lean_dec(v_a_2864_);
lean_del_object(v___x_2857_);
lean_dec(v_fst_2855_);
lean_dec(v_val_2838_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v___x_2870_);
lean_ctor_set(v___x_2861_, 0, v___x_2832_);
v___x_2873_ = v___x_2861_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2870_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
v_a_2820_ = v___x_2873_;
goto v___jp_2819_;
}
}
else
{
size_t v_sz_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
v_sz_2875_ = lean_array_size(v_fst_2855_);
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2875_, v___x_2876_, v_fst_2855_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_array_get_size(v_a_2878_);
v___x_2926_ = lean_nat_dec_lt(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_dec(v_a_2864_);
lean_del_object(v___x_2857_);
goto v___jp_2879_;
}
else
{
if (v___x_2926_ == 0)
{
lean_dec(v_a_2864_);
lean_del_object(v___x_2857_);
goto v___jp_2879_;
}
else
{
size_t v___x_2927_; uint8_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2927_ = lean_usize_of_nat(v___x_2925_);
v___x_2928_ = lean_unbox(v_a_2864_);
lean_dec(v_a_2864_);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2928_, v___x_2803_, v_a_2878_, v___x_2876_, v___x_2927_);
if (v___x_2929_ == 0)
{
lean_del_object(v___x_2857_);
goto v___jp_2879_;
}
else
{
lean_object* v___x_2931_; 
lean_dec(v_a_2878_);
lean_del_object(v___x_2861_);
lean_dec(v_val_2838_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v___x_2870_);
lean_ctor_set(v___x_2857_, 0, v___x_2832_);
v___x_2931_ = v___x_2857_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2870_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
v_a_2820_ = v___x_2931_;
goto v___jp_2819_;
}
}
}
}
v___jp_2879_:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2878_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v_a_2878_);
lean_dec(v_val_2838_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v___x_2870_);
lean_ctor_set(v___x_2861_, 0, v___x_2832_);
v___x_2882_ = v___x_2861_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2870_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
v_a_2820_ = v___x_2882_;
goto v___jp_2819_;
}
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2804_, v_a_2878_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2915_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2915_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v___x_2890_; 
lean_dec_ref_known(v_a_2885_, 1);
lean_del_object(v___x_2887_);
lean_dec(v_a_2878_);
lean_dec(v_val_2838_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v___x_2870_);
lean_ctor_set(v___x_2861_, 0, v___x_2832_);
v___x_2890_ = v___x_2861_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2870_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
v_a_2820_ = v___x_2890_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_fnName_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2885_);
lean_dec_ref(v___x_2802_);
v_fnName_2892_ = lean_ctor_get(v_recArgInfo_2806_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_recArgInfo_2806_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; lean_object* v_unused_2911_; lean_object* v_unused_2912_; lean_object* v_unused_2913_; lean_object* v_unused_2914_; 
v_unused_2910_ = lean_ctor_get(v_recArgInfo_2806_, 5);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_recArgInfo_2806_, 4);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_recArgInfo_2806_, 3);
lean_dec(v_unused_2912_);
v_unused_2913_ = lean_ctor_get(v_recArgInfo_2806_, 2);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_recArgInfo_2806_, 1);
lean_dec(v_unused_2914_);
v___x_2894_ = v_recArgInfo_2806_;
v_isShared_2895_ = v_isSharedCheck_2909_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_fnName_2892_);
lean_dec(v_recArgInfo_2806_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2909_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
size_t v_sz_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v_sz_2896_ = lean_array_size(v_a_2878_);
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2805_, v_sz_2896_, v___x_2876_, v_a_2878_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 5, v_val_2838_);
lean_ctor_set(v___x_2894_, 4, v_group_2809_);
lean_ctor_set(v___x_2894_, 3, v___x_2897_);
lean_ctor_set(v___x_2894_, 2, v___x_2808_);
lean_ctor_set(v___x_2894_, 1, v___x_2807_);
v___x_2899_ = v___x_2894_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_fnName_2892_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_group_2809_);
lean_ctor_set(v_reuseFailAlloc_2908_, 5, v_val_2838_);
v___x_2899_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v___x_2870_);
lean_ctor_set(v___x_2861_, 0, v___x_2901_);
v___x_2903_ = v___x_2861_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2870_);
v___x_2903_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2905_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2903_);
v___x_2905_ = v___x_2887_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_a_2878_);
lean_dec_ref(v___x_2870_);
lean_del_object(v___x_2861_);
lean_dec(v_val_2838_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2916_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2884_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2884_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___x_2870_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_del_object(v___x_2857_);
lean_dec(v_val_2838_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2933_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2877_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2877_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_del_object(v___x_2861_);
lean_del_object(v___x_2857_);
lean_dec(v_fst_2855_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2840_);
lean_dec(v_val_2838_);
lean_dec(v_upperBound_2831_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2943_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2863_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2863_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_a_2849_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2840_);
lean_dec(v_val_2838_);
lean_dec(v_upperBound_2831_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2954_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2852_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2852_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_del_object(v___x_2844_);
lean_del_object(v___x_2840_);
lean_dec(v_val_2838_);
lean_dec(v_upperBound_2831_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2962_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2848_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2848_);
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
lean_del_object(v___x_2844_);
lean_del_object(v___x_2840_);
lean_dec(v_val_2838_);
lean_dec(v_upperBound_2831_);
lean_dec_ref(v_group_2809_);
lean_dec(v___x_2808_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_recArgInfo_2806_);
lean_dec_ref(v___x_2802_);
v_a_2970_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2846_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2846_);
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
}
}
}
v___jp_2833_:
{
lean_object* v___x_2835_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2832_);
v___x_2835_ = v___x_2828_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_snd_2826_);
v___x_2835_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
}
v___jp_2819_:
{
size_t v___x_2821_; size_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_add(v_i_2812_, v___x_2821_);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2802_, v_ys_2804_, v___x_2805_, v_recArgInfo_2806_, v___x_2807_, v___x_2808_, v_group_2809_, v___x_2803_, v_as_2810_, v_sz_2811_, v___x_2822_, v_a_2820_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2984_ = _args[0];
lean_object* v___x_2985_ = _args[1];
lean_object* v_ys_2986_ = _args[2];
lean_object* v___x_2987_ = _args[3];
lean_object* v_recArgInfo_2988_ = _args[4];
lean_object* v___x_2989_ = _args[5];
lean_object* v___x_2990_ = _args[6];
lean_object* v_group_2991_ = _args[7];
lean_object* v_as_2992_ = _args[8];
lean_object* v_sz_2993_ = _args[9];
lean_object* v_i_2994_ = _args[10];
lean_object* v_b_2995_ = _args[11];
lean_object* v___y_2996_ = _args[12];
lean_object* v___y_2997_ = _args[13];
lean_object* v___y_2998_ = _args[14];
lean_object* v___y_2999_ = _args[15];
lean_object* v___y_3000_ = _args[16];
_start:
{
size_t v_sz_boxed_3001_; size_t v_i_boxed_3002_; lean_object* v_res_3003_; 
v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2993_);
lean_dec(v_sz_2993_);
v_i_boxed_3002_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2984_, v___x_2985_, v_ys_2986_, v___x_2987_, v_recArgInfo_2988_, v___x_2989_, v___x_2990_, v_group_2991_, v_as_2992_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_as_2992_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_ys_2986_);
lean_dec(v___x_2985_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3004_, lean_object* v_fixedParamPerm_3005_, lean_object* v_xs_3006_, lean_object* v___x_3007_, lean_object* v_recArgPos_3008_, lean_object* v_a_3009_, lean_object* v___x_3010_, lean_object* v___x_3011_, lean_object* v_ys_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_toIndGroupInfo_3019_; lean_object* v_all_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3058_; 
v_toIndGroupInfo_3019_ = lean_ctor_get(v_group_3004_, 0);
lean_inc_ref(v_toIndGroupInfo_3019_);
v_all_3020_ = lean_ctor_get(v_toIndGroupInfo_3019_, 0);
lean_inc_ref(v_ys_3012_);
lean_inc_ref(v_fixedParamPerm_3005_);
v___x_3021_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3005_, v_xs_3006_, v_ys_3012_);
v___x_3022_ = lean_array_get(v___x_3007_, v___x_3021_, v_recArgPos_3008_);
v___x_3023_ = lean_array_get_size(v_all_3020_);
v___x_3024_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3019_);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_toIndGroupInfo_3019_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; lean_object* v_unused_3060_; 
v_unused_3059_ = lean_ctor_get(v_toIndGroupInfo_3019_, 1);
lean_dec(v_unused_3059_);
v_unused_3060_ = lean_ctor_get(v_toIndGroupInfo_3019_, 0);
lean_dec(v_unused_3060_);
v___x_3026_ = v_toIndGroupInfo_3019_;
v_isShared_3027_ = v_isSharedCheck_3058_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_toIndGroupInfo_3019_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3058_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3023_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
lean_ctor_set(v___x_3026_, 0, v___x_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3024_);
v___x_3030_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; size_t v_sz_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3030_);
v_sz_3033_ = lean_array_size(v_a_3009_);
v___x_3034_ = ((size_t)0ULL);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3022_, v___x_3010_, v_ys_3012_, v___x_3021_, v___x_3011_, v_fixedParamPerm_3005_, v_recArgPos_3008_, v_group_3004_, v_a_3009_, v_sz_3033_, v___x_3034_, v___x_3032_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec_ref(v___x_3021_);
lean_dec_ref(v_ys_3012_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3048_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_fst_3040_; 
v_fst_3040_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_fst_3040_);
lean_dec(v_a_3036_);
if (lean_obj_tag(v_fst_3040_) == 0)
{
lean_object* v___x_3042_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3031_);
v___x_3042_ = v___x_3038_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3031_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
else
{
lean_object* v_val_3044_; lean_object* v___x_3046_; 
v_val_3044_ = lean_ctor_get(v_fst_3040_, 0);
lean_inc(v_val_3044_);
lean_dec_ref_known(v_fst_3040_, 1);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_val_3044_);
v___x_3046_ = v___x_3038_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_val_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_a_3049_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3035_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3035_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3061_, lean_object* v_fixedParamPerm_3062_, lean_object* v_xs_3063_, lean_object* v___x_3064_, lean_object* v_recArgPos_3065_, lean_object* v_a_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v_ys_3069_, lean_object* v_x_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3061_, v_fixedParamPerm_3062_, v_xs_3063_, v___x_3064_, v_recArgPos_3065_, v_a_3066_, v___x_3067_, v___x_3068_, v_ys_3069_, v_x_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_x_3070_);
lean_dec(v___x_3067_);
lean_dec_ref(v_a_3066_);
lean_dec_ref(v___x_3064_);
lean_dec_ref(v_xs_3063_);
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
lean_object* v___x_3099_; lean_object* v_fixedParamPerm_3100_; lean_object* v_recArgPos_3101_; lean_object* v_indGroupInst_3102_; lean_object* v___x_3103_; 
v___x_3099_ = lean_array_uget_borrowed(v_as_3081_, v_i_3082_);
v_fixedParamPerm_3100_ = lean_ctor_get(v___x_3099_, 1);
v_recArgPos_3101_ = lean_ctor_get(v___x_3099_, 2);
v_indGroupInst_3102_ = lean_ctor_get(v___x_3099_, 4);
lean_inc_ref(v_indGroupInst_3102_);
lean_inc_ref(v_group_3077_);
v___x_3103_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3077_, v_indGroupInst_3102_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; uint8_t v___x_3105_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_array_get_size(v_a_3078_);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___f_3110_; lean_object* v___x_3111_; 
v___x_3109_ = l_Lean_instInhabitedExpr;
lean_inc(v___x_3099_);
lean_inc_ref(v_a_3078_);
lean_inc(v_recArgPos_3101_);
lean_inc_ref(v_xs_3079_);
lean_inc_ref(v_fixedParamPerm_3100_);
lean_inc_ref(v_group_3077_);
v___f_3110_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3110_, 0, v_group_3077_);
lean_closure_set(v___f_3110_, 1, v_fixedParamPerm_3100_);
lean_closure_set(v___f_3110_, 2, v_xs_3079_);
lean_closure_set(v___f_3110_, 3, v___x_3109_);
lean_closure_set(v___f_3110_, 4, v_recArgPos_3101_);
lean_closure_set(v___f_3110_, 5, v_a_3078_);
lean_closure_set(v___f_3110_, 6, v___x_3106_);
lean_closure_set(v___f_3110_, 7, v___x_3099_);
lean_inc_ref(v_value_3080_);
v___x_3111_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3080_, v___f_3110_, v___x_3108_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
if (lean_obj_tag(v_a_3112_) == 0)
{
v_a_3091_ = v_b_3084_;
goto v___jp_3090_;
}
else
{
lean_object* v_val_3113_; 
v_val_3113_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v_a_3112_, 1);
v_val_3096_ = v_val_3113_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_b_3084_);
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v_a_3114_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3111_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3111_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
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
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v_b_3084_);
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v_a_3122_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3103_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3103_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v___x_3130_; 
lean_dec_ref(v_value_3080_);
lean_dec_ref(v_xs_3079_);
lean_dec_ref(v_a_3078_);
lean_dec_ref(v_group_3077_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_b_3084_);
return v___x_3130_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3131_, lean_object* v_a_3132_, lean_object* v_xs_3133_, lean_object* v_value_3134_, lean_object* v_as_3135_, lean_object* v_i_3136_, lean_object* v_stop_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
size_t v_i_boxed_3144_; size_t v_stop_boxed_3145_; lean_object* v_res_3146_; 
v_i_boxed_3144_ = lean_unbox_usize(v_i_3136_);
lean_dec(v_i_3136_);
v_stop_boxed_3145_ = lean_unbox_usize(v_stop_3137_);
lean_dec(v_stop_3137_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3131_, v_a_3132_, v_xs_3133_, v_value_3134_, v_as_3135_, v_i_boxed_3144_, v_stop_boxed_3145_, v_b_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v_as_3135_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3147_, lean_object* v_a_3148_, lean_object* v_xs_3149_, lean_object* v_value_3150_, lean_object* v_as_3151_, lean_object* v_start_3152_, lean_object* v_stop_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3160_ = lean_nat_dec_lt(v_start_3152_, v_stop_3153_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v_value_3150_);
lean_dec_ref(v_xs_3149_);
lean_dec_ref(v_a_3148_);
lean_dec_ref(v_group_3147_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = lean_array_get_size(v_as_3151_);
v___x_3163_ = lean_nat_dec_le(v_stop_3153_, v___x_3162_);
if (v___x_3163_ == 0)
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_nat_dec_lt(v_start_3152_, v___x_3162_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_dec_ref(v_value_3150_);
lean_dec_ref(v_xs_3149_);
lean_dec_ref(v_a_3148_);
lean_dec_ref(v_group_3147_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3159_);
return v___x_3165_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_usize_of_nat(v_start_3152_);
v___x_3167_ = lean_usize_of_nat(v___x_3162_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3147_, v_a_3148_, v_xs_3149_, v_value_3150_, v_as_3151_, v___x_3166_, v___x_3167_, v___x_3159_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
return v___x_3168_;
}
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_usize_of_nat(v_start_3152_);
v___x_3170_ = lean_usize_of_nat(v_stop_3153_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3147_, v_a_3148_, v_xs_3149_, v_value_3150_, v_as_3151_, v___x_3169_, v___x_3170_, v___x_3159_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3172_, lean_object* v_a_3173_, lean_object* v_xs_3174_, lean_object* v_value_3175_, lean_object* v_as_3176_, lean_object* v_start_3177_, lean_object* v_stop_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3172_, v_a_3173_, v_xs_3174_, v_value_3175_, v_as_3176_, v_start_3177_, v_stop_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_stop_3178_);
lean_dec(v_start_3177_);
lean_dec_ref(v_as_3176_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3185_, lean_object* v_xs_3186_, lean_object* v_value_3187_, lean_object* v_recArgInfos_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v___x_3194_; 
lean_inc_ref(v_group_3185_);
v___x_3194_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3185_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_array_get_size(v_recArgInfos_3188_);
v___x_3198_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3185_, v_a_3195_, v_xs_3186_, v_value_3187_, v_recArgInfos_3188_, v___x_3196_, v___x_3197_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
return v___x_3198_;
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v_value_3187_);
lean_dec_ref(v_xs_3186_);
lean_dec_ref(v_group_3185_);
v_a_3199_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3194_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3194_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3207_, lean_object* v_xs_3208_, lean_object* v_value_3209_, lean_object* v_recArgInfos_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Elab_Structural_argsInGroup(v_group_3207_, v_xs_3208_, v_value_3209_, v_recArgInfos_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec_ref(v_recArgInfos_3210_);
return v_res_3216_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_unsigned_to_nat(10u);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3220_, lean_object* v_i_3221_, lean_object* v_acc_3222_){
_start:
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = lean_array_get_size(v_xss_3220_);
v___x_3224_ = lean_nat_dec_lt(v_i_3221_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_mk_empty_array_with_capacity(v___x_3225_);
v___x_3227_ = lean_array_push(v___x_3226_, v_acc_3222_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3228_ = lean_array_fget_borrowed(v_xss_3220_, v_i_3221_);
v___x_3229_ = lean_unsigned_to_nat(0u);
v___x_3230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3231_ = lean_array_get_size(v___x_3228_);
v___x_3232_ = lean_nat_dec_lt(v___x_3229_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_dec_ref(v_acc_3222_);
return v___x_3230_;
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_usize_of_nat(v___x_3231_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3221_, v_acc_3222_, v_xss_3220_, v___x_3228_, v___x_3233_, v___x_3234_, v___x_3230_);
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3236_, lean_object* v_acc_3237_, lean_object* v_xss_3238_, lean_object* v_as_3239_, size_t v_i_3240_, size_t v_stop_3241_, lean_object* v_b_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_usize_dec_eq(v_i_3240_, v_stop_3241_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; size_t v___x_3250_; size_t v___x_3251_; 
v___x_3244_ = lean_array_uget_borrowed(v_as_3239_, v_i_3240_);
v___x_3245_ = lean_unsigned_to_nat(1u);
v___x_3246_ = lean_nat_add(v_i_3236_, v___x_3245_);
lean_inc(v___x_3244_);
lean_inc_ref(v_acc_3237_);
v___x_3247_ = lean_array_push(v_acc_3237_, v___x_3244_);
v___x_3248_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3238_, v___x_3246_, v___x_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = l_Array_append___redArg(v_b_3242_, v___x_3248_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = ((size_t)1ULL);
v___x_3251_ = lean_usize_add(v_i_3240_, v___x_3250_);
v_i_3240_ = v___x_3251_;
v_b_3242_ = v___x_3249_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3237_);
return v_b_3242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3253_, lean_object* v_acc_3254_, lean_object* v_xss_3255_, lean_object* v_as_3256_, lean_object* v_i_3257_, lean_object* v_stop_3258_, lean_object* v_b_3259_){
_start:
{
size_t v_i_boxed_3260_; size_t v_stop_boxed_3261_; lean_object* v_res_3262_; 
v_i_boxed_3260_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_stop_boxed_3261_ = lean_unbox_usize(v_stop_3258_);
lean_dec(v_stop_3258_);
v_res_3262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3253_, v_acc_3254_, v_xss_3255_, v_as_3256_, v_i_boxed_3260_, v_stop_boxed_3261_, v_b_3259_);
lean_dec_ref(v_as_3256_);
lean_dec_ref(v_xss_3255_);
lean_dec(v_i_3253_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3263_, lean_object* v_i_3264_, lean_object* v_acc_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3263_, v_i_3264_, v_acc_3265_);
lean_dec(v_i_3264_);
lean_dec_ref(v_xss_3263_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3267_, lean_object* v_xss_3268_, lean_object* v_i_3269_, lean_object* v_acc_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3268_, v_i_3269_, v_acc_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_xss_3273_, lean_object* v_i_3274_, lean_object* v_acc_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3272_, v_xss_3273_, v_i_3274_, v_acc_3275_);
lean_dec(v_i_3274_);
lean_dec_ref(v_xss_3273_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3277_, lean_object* v_i_3278_, lean_object* v_acc_3279_, lean_object* v_xss_3280_, lean_object* v_as_3281_, size_t v_i_3282_, size_t v_stop_3283_, lean_object* v_b_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3278_, v_acc_3279_, v_xss_3280_, v_as_3281_, v_i_3282_, v_stop_3283_, v_b_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3286_, lean_object* v_i_3287_, lean_object* v_acc_3288_, lean_object* v_xss_3289_, lean_object* v_as_3290_, lean_object* v_i_3291_, lean_object* v_stop_3292_, lean_object* v_b_3293_){
_start:
{
size_t v_i_boxed_3294_; size_t v_stop_boxed_3295_; lean_object* v_res_3296_; 
v_i_boxed_3294_ = lean_unbox_usize(v_i_3291_);
lean_dec(v_i_3291_);
v_stop_boxed_3295_ = lean_unbox_usize(v_stop_3292_);
lean_dec(v_stop_3292_);
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3286_, v_i_3287_, v_acc_3288_, v_xss_3289_, v_as_3290_, v_i_boxed_3294_, v_stop_boxed_3295_, v_b_3293_);
lean_dec_ref(v_as_3290_);
lean_dec_ref(v_xss_3289_);
lean_dec(v_i_3287_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3297_, size_t v_i_3298_, size_t v_stop_3299_, lean_object* v_b_3300_){
_start:
{
uint8_t v___x_3301_; 
v___x_3301_ = lean_usize_dec_eq(v_i_3298_, v_stop_3299_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; size_t v___x_3305_; size_t v___x_3306_; 
v___x_3302_ = lean_array_uget_borrowed(v_as_3297_, v_i_3298_);
v___x_3303_ = lean_array_get_size(v___x_3302_);
v___x_3304_ = lean_nat_mul(v_b_3300_, v___x_3303_);
lean_dec(v_b_3300_);
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = lean_usize_add(v_i_3298_, v___x_3305_);
v_i_3298_ = v___x_3306_;
v_b_3300_ = v___x_3304_;
goto _start;
}
else
{
return v_b_3300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3308_, lean_object* v_i_3309_, lean_object* v_stop_3310_, lean_object* v_b_3311_){
_start:
{
size_t v_i_boxed_3312_; size_t v_stop_boxed_3313_; lean_object* v_res_3314_; 
v_i_boxed_3312_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_stop_boxed_3313_ = lean_unbox_usize(v_stop_3310_);
lean_dec(v_stop_3310_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3308_, v_i_boxed_3312_, v_stop_boxed_3313_, v_b_3311_);
lean_dec_ref(v_as_3308_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3315_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___y_3320_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3316_ = lean_unsigned_to_nat(10u);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3326_ = lean_array_get_size(v_xss_3315_);
v___x_3327_ = lean_nat_dec_lt(v___x_3318_, v___x_3326_);
if (v___x_3327_ == 0)
{
v___y_3320_ = v___x_3317_;
goto v___jp_3319_;
}
else
{
uint8_t v___x_3328_; 
v___x_3328_ = lean_nat_dec_le(v___x_3326_, v___x_3326_);
if (v___x_3328_ == 0)
{
if (v___x_3327_ == 0)
{
v___y_3320_ = v___x_3317_;
goto v___jp_3319_;
}
else
{
size_t v___x_3329_; size_t v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = ((size_t)0ULL);
v___x_3330_ = lean_usize_of_nat(v___x_3326_);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3315_, v___x_3329_, v___x_3330_, v___x_3317_);
v___y_3320_ = v___x_3331_;
goto v___jp_3319_;
}
}
else
{
size_t v___x_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = lean_usize_of_nat(v___x_3326_);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3315_, v___x_3332_, v___x_3333_, v___x_3317_);
v___y_3320_ = v___x_3334_;
goto v___jp_3319_;
}
}
v___jp_3319_:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_lt(v___x_3316_, v___y_3320_);
lean_dec(v___y_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3323_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3315_, v___x_3318_, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_box(0);
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3335_);
lean_dec_ref(v_xss_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3337_, lean_object* v_xss_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3340_, lean_object* v_xss_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3340_, v_xss_3341_);
lean_dec_ref(v_xss_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3343_, lean_object* v_as_3344_, size_t v_i_3345_, size_t v_stop_3346_, lean_object* v_b_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3344_, v_i_3345_, v_stop_3346_, v_b_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3349_, lean_object* v_as_3350_, lean_object* v_i_3351_, lean_object* v_stop_3352_, lean_object* v_b_3353_){
_start:
{
size_t v_i_boxed_3354_; size_t v_stop_boxed_3355_; lean_object* v_res_3356_; 
v_i_boxed_3354_ = lean_unbox_usize(v_i_3351_);
lean_dec(v_i_3351_);
v_stop_boxed_3355_ = lean_unbox_usize(v_stop_3352_);
lean_dec(v_stop_3352_);
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3349_, v_as_3350_, v_i_boxed_3354_, v_stop_boxed_3355_, v_b_3353_);
lean_dec_ref(v_as_3350_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3357_, size_t v_i_3358_, size_t v_stop_3359_, lean_object* v_b_3360_){
_start:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_usize_dec_eq(v_i_3358_, v_stop_3359_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; size_t v___x_3364_; size_t v___x_3365_; 
v___x_3362_ = lean_array_uget_borrowed(v_as_3357_, v_i_3358_);
v___x_3363_ = l_Array_append___redArg(v_b_3360_, v___x_3362_);
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = lean_usize_add(v_i_3358_, v___x_3364_);
v_i_3358_ = v___x_3365_;
v_b_3360_ = v___x_3363_;
goto _start;
}
else
{
return v_b_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3367_, lean_object* v_i_3368_, lean_object* v_stop_3369_, lean_object* v_b_3370_){
_start:
{
size_t v_i_boxed_3371_; size_t v_stop_boxed_3372_; lean_object* v_res_3373_; 
v_i_boxed_3371_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_stop_boxed_3372_ = lean_unbox_usize(v_stop_3369_);
lean_dec(v_stop_3369_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3367_, v_i_boxed_3371_, v_stop_boxed_3372_, v_b_3370_);
lean_dec_ref(v_as_3367_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
if (lean_obj_tag(v_a_3374_) == 0)
{
lean_object* v___x_3376_; 
v___x_3376_ = l_List_reverse___redArg(v_a_3375_);
return v___x_3376_;
}
else
{
lean_object* v_head_3377_; lean_object* v_tail_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3388_; 
v_head_3377_ = lean_ctor_get(v_a_3374_, 0);
v_tail_3378_ = lean_ctor_get(v_a_3374_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_a_3374_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3380_ = v_a_3374_;
v_isShared_3381_ = v_isSharedCheck_3388_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_tail_3378_);
lean_inc(v_head_3377_);
lean_dec(v_a_3374_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3388_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3382_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3377_);
v___x_3383_ = l_Lean_MessageData_ofFormat(v___x_3382_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v_a_3375_);
lean_ctor_set(v___x_3380_, 0, v___x_3383_);
v___x_3385_ = v___x_3380_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_a_3375_);
v___x_3385_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
v_a_3374_ = v_tail_3378_;
v_a_3375_ = v___x_3385_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3389_, size_t v_i_3390_, lean_object* v_bs_3391_){
_start:
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_usize_dec_lt(v_i_3390_, v_sz_3389_);
if (v___x_3392_ == 0)
{
return v_bs_3391_;
}
else
{
lean_object* v_v_3393_; lean_object* v___x_3394_; lean_object* v_bs_x27_3395_; lean_object* v___x_3396_; size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v_v_3393_ = lean_array_uget(v_bs_3391_, v_i_3390_);
v___x_3394_ = lean_unsigned_to_nat(0u);
v_bs_x27_3395_ = lean_array_uset(v_bs_3391_, v_i_3390_, v___x_3394_);
v___x_3396_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3393_);
lean_dec(v_v_3393_);
v___x_3397_ = ((size_t)1ULL);
v___x_3398_ = lean_usize_add(v_i_3390_, v___x_3397_);
v___x_3399_ = lean_array_uset(v_bs_x27_3395_, v_i_3390_, v___x_3396_);
v_i_3390_ = v___x_3398_;
v_bs_3391_ = v___x_3399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3401_, lean_object* v_i_3402_, lean_object* v_bs_3403_){
_start:
{
size_t v_sz_boxed_3404_; size_t v_i_boxed_3405_; lean_object* v_res_3406_; 
v_sz_boxed_3404_ = lean_unbox_usize(v_sz_3401_);
lean_dec(v_sz_3401_);
v_i_boxed_3405_ = lean_unbox_usize(v_i_3402_);
lean_dec(v_i_3402_);
v_res_3406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3404_, v_i_boxed_3405_, v_bs_3403_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3407_, lean_object* v_as_3408_, size_t v_sz_3409_, size_t v_i_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_usize_dec_lt(v_i_3410_, v_sz_3409_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; 
lean_dec_ref(v_xs_3407_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_b_3411_);
return v___x_3418_;
}
else
{
lean_object* v_snd_3419_; lean_object* v_snd_3420_; lean_object* v_snd_3421_; lean_object* v_snd_3422_; lean_object* v_fst_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3567_; 
v_snd_3419_ = lean_ctor_get(v_b_3411_, 1);
lean_inc(v_snd_3419_);
v_snd_3420_ = lean_ctor_get(v_snd_3419_, 1);
lean_inc(v_snd_3420_);
v_snd_3421_ = lean_ctor_get(v_snd_3420_, 1);
lean_inc(v_snd_3421_);
v_snd_3422_ = lean_ctor_get(v_snd_3421_, 1);
lean_inc(v_snd_3422_);
v_fst_3423_ = lean_ctor_get(v_b_3411_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_b_3411_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_b_3411_, 1);
lean_dec(v_unused_3568_);
v___x_3425_ = v_b_3411_;
v_isShared_3426_ = v_isSharedCheck_3567_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_fst_3423_);
lean_dec(v_b_3411_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3567_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_fst_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3565_; 
v_fst_3427_ = lean_ctor_get(v_snd_3419_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_snd_3419_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v_snd_3419_, 1);
lean_dec(v_unused_3566_);
v___x_3429_ = v_snd_3419_;
v_isShared_3430_ = v_isSharedCheck_3565_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_fst_3427_);
lean_dec(v_snd_3419_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3565_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_fst_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3563_; 
v_fst_3431_ = lean_ctor_get(v_snd_3420_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_snd_3420_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v_snd_3420_, 1);
lean_dec(v_unused_3564_);
v___x_3433_ = v_snd_3420_;
v_isShared_3434_ = v_isSharedCheck_3563_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_fst_3431_);
lean_dec(v_snd_3420_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3563_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_fst_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3561_; 
v_fst_3435_ = lean_ctor_get(v_snd_3421_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v_snd_3421_, 1);
lean_dec(v_unused_3562_);
v___x_3437_ = v_snd_3421_;
v_isShared_3438_ = v_isSharedCheck_3561_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_fst_3435_);
lean_dec(v_snd_3421_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3561_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v_array_3439_; lean_object* v_start_3440_; lean_object* v_stop_3441_; uint8_t v___x_3442_; 
v_array_3439_ = lean_ctor_get(v_snd_3422_, 0);
v_start_3440_ = lean_ctor_get(v_snd_3422_, 1);
v_stop_3441_ = lean_ctor_get(v_snd_3422_, 2);
v___x_3442_ = lean_nat_dec_lt(v_start_3440_, v_stop_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3444_; 
lean_dec_ref(v_xs_3407_);
if (v_isShared_3438_ == 0)
{
v___x_3444_ = v___x_3437_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3435_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_snd_3422_);
v___x_3444_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3444_);
v___x_3446_ = v___x_3433_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3446_);
v___x_3448_ = v___x_3429_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3427_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v___x_3448_);
v___x_3450_ = v___x_3425_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_fst_3423_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
}
}
else
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3557_; 
lean_inc(v_stop_3441_);
lean_inc(v_start_3440_);
lean_inc_ref(v_array_3439_);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_snd_3422_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; 
v_unused_3558_ = lean_ctor_get(v_snd_3422_, 2);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_snd_3422_, 1);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_snd_3422_, 0);
lean_dec(v_unused_3560_);
v___x_3457_ = v_snd_3422_;
v_isShared_3458_ = v_isSharedCheck_3557_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v_snd_3422_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3557_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_array_3459_; lean_object* v_start_3460_; lean_object* v_stop_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v_array_3459_ = lean_ctor_get(v_fst_3435_, 0);
v_start_3460_ = lean_ctor_get(v_fst_3435_, 1);
v_stop_3461_ = lean_ctor_get(v_fst_3435_, 2);
v___x_3462_ = lean_array_fget(v_array_3439_, v_start_3440_);
v___x_3463_ = lean_unsigned_to_nat(1u);
v___x_3464_ = lean_nat_add(v_start_3440_, v___x_3463_);
lean_dec(v_start_3440_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v___x_3464_);
v___x_3466_ = v___x_3457_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_array_3439_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_stop_3441_);
v___x_3466_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_nat_dec_lt(v_start_3460_, v_stop_3461_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v___x_3462_);
lean_dec_ref(v_xs_3407_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3466_);
v___x_3469_ = v___x_3437_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_fst_3435_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3466_);
v___x_3469_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3469_);
v___x_3471_ = v___x_3433_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3471_);
v___x_3473_ = v___x_3429_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_fst_3427_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v___x_3473_);
v___x_3475_ = v___x_3425_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_fst_3423_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
}
}
}
else
{
lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3552_; 
lean_inc(v_stop_3461_);
lean_inc(v_start_3460_);
lean_inc_ref(v_array_3459_);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_fst_3435_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3553_ = lean_ctor_get(v_fst_3435_, 2);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_fst_3435_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_fst_3435_, 0);
lean_dec(v_unused_3555_);
v___x_3482_ = v_fst_3435_;
v_isShared_3483_ = v_isSharedCheck_3552_;
goto v_resetjp_3481_;
}
else
{
lean_dec(v_fst_3435_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3552_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_array_3484_; lean_object* v_start_3485_; lean_object* v_stop_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v_array_3484_ = lean_ctor_get(v_fst_3431_, 0);
v_start_3485_ = lean_ctor_get(v_fst_3431_, 1);
v_stop_3486_ = lean_ctor_get(v_fst_3431_, 2);
v___x_3487_ = lean_array_fget(v_array_3459_, v_start_3460_);
v___x_3488_ = lean_nat_add(v_start_3460_, v___x_3463_);
lean_dec(v_start_3460_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3488_);
v___x_3490_ = v___x_3482_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_array_3459_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_stop_3461_);
v___x_3490_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_nat_dec_lt(v_start_3485_, v_stop_3486_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v___x_3487_);
lean_dec(v___x_3462_);
lean_dec_ref(v_xs_3407_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3466_);
lean_ctor_set(v___x_3437_, 0, v___x_3490_);
v___x_3493_ = v___x_3437_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3466_);
v___x_3493_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3493_);
v___x_3495_ = v___x_3433_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3495_);
v___x_3497_ = v___x_3429_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_fst_3427_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v___x_3497_);
v___x_3499_ = v___x_3425_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_fst_3423_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
}
}
}
}
else
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3547_; 
lean_inc(v_stop_3486_);
lean_inc(v_start_3485_);
lean_inc_ref(v_array_3484_);
lean_del_object(v___x_3425_);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_fst_3431_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3548_ = lean_ctor_get(v_fst_3431_, 2);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_fst_3431_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_fst_3431_, 0);
lean_dec(v_unused_3550_);
v___x_3506_ = v_fst_3431_;
v_isShared_3507_ = v_isSharedCheck_3547_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_fst_3431_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3547_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_a_3508_ = lean_array_uget_borrowed(v_as_3408_, v_i_3410_);
v___x_3509_ = lean_array_fget_borrowed(v_array_3484_, v_start_3485_);
lean_inc(v___x_3509_);
lean_inc_ref(v_xs_3407_);
lean_inc(v_a_3508_);
v___x_3510_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3508_, v___x_3462_, v_xs_3407_, v___x_3509_, v___x_3487_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3538_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v_fst_3512_ = lean_ctor_get(v_a_3511_, 0);
v_snd_3513_ = lean_ctor_get(v_a_3511_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3515_ = v_a_3511_;
v_isShared_3516_ = v_isSharedCheck_3538_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_snd_3513_);
lean_inc(v_fst_3512_);
lean_dec(v_a_3511_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3538_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = lean_nat_add(v_start_3485_, v___x_3463_);
lean_dec(v_start_3485_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3517_);
v___x_3519_ = v___x_3506_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_array_3484_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_stop_3486_);
v___x_3519_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v_fst_3423_);
lean_ctor_set(v___x_3520_, 1, v_snd_3513_);
v___x_3521_ = lean_array_push(v_fst_3427_, v_fst_3512_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3466_);
lean_ctor_set(v___x_3515_, 0, v___x_3490_);
v___x_3523_ = v___x_3515_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3466_);
v___x_3523_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3523_);
lean_ctor_set(v___x_3437_, 0, v___x_3519_);
v___x_3525_ = v___x_3437_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3527_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3525_);
lean_ctor_set(v___x_3433_, 0, v___x_3521_);
v___x_3527_ = v___x_3433_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3527_);
lean_ctor_set(v___x_3429_, 0, v___x_3520_);
v___x_3529_ = v___x_3429_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
size_t v___x_3530_; size_t v___x_3531_; 
v___x_3530_ = ((size_t)1ULL);
v___x_3531_ = lean_usize_add(v_i_3410_, v___x_3530_);
v_i_3410_ = v___x_3531_;
v_b_3411_ = v___x_3529_;
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
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_del_object(v___x_3506_);
lean_dec_ref(v___x_3490_);
lean_dec(v_stop_3486_);
lean_dec(v_start_3485_);
lean_dec_ref(v_array_3484_);
lean_dec_ref(v___x_3466_);
lean_del_object(v___x_3437_);
lean_del_object(v___x_3433_);
lean_del_object(v___x_3429_);
lean_dec(v_fst_3427_);
lean_dec(v_fst_3423_);
lean_dec_ref(v_xs_3407_);
v_a_3539_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3510_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3510_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3569_, lean_object* v_as_3570_, lean_object* v_sz_3571_, lean_object* v_i_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
size_t v_sz_boxed_3579_; size_t v_i_boxed_3580_; lean_object* v_res_3581_; 
v_sz_boxed_3579_ = lean_unbox_usize(v_sz_3571_);
lean_dec(v_sz_3571_);
v_i_boxed_3580_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_res_3581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3569_, v_as_3570_, v_sz_boxed_3579_, v_i_boxed_3580_, v_b_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v_as_3570_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
if (lean_obj_tag(v_a_3582_) == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = l_List_reverse___redArg(v_a_3583_);
return v___x_3584_;
}
else
{
lean_object* v_head_3585_; lean_object* v_tail_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3595_; 
v_head_3585_ = lean_ctor_get(v_a_3582_, 0);
v_tail_3586_ = lean_ctor_get(v_a_3582_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3582_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3588_ = v_a_3582_;
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_tail_3586_);
lean_inc(v_head_3585_);
lean_dec(v_a_3582_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3585_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v_a_3583_);
lean_ctor_set(v___x_3588_, 0, v___x_3590_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_a_3583_);
v___x_3592_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
v_a_3582_ = v_tail_3586_;
v_a_3583_ = v___x_3592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3596_, lean_object* v_j_3597_){
_start:
{
lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = lean_array_get_size(v_as_3596_);
v___x_3599_ = lean_nat_dec_lt(v_j_3597_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
lean_dec(v_j_3597_);
v___x_3600_ = lean_box(0);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3601_ = lean_array_fget_borrowed(v_as_3596_, v_j_3597_);
v___x_3602_ = lean_array_get_size(v___x_3601_);
v___x_3603_ = lean_unsigned_to_nat(0u);
v___x_3604_ = lean_nat_dec_eq(v___x_3602_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = lean_nat_add(v_j_3597_, v___x_3605_);
lean_dec(v_j_3597_);
v_j_3597_ = v___x_3606_;
goto _start;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_j_3597_);
return v___x_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3609_, lean_object* v_j_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3609_, v_j_3610_);
lean_dec_ref(v_as_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3612_, lean_object* v_as_3613_, size_t v_sz_3614_, size_t v_i_3615_, lean_object* v_b_3616_){
_start:
{
uint8_t v___x_3618_; 
v___x_3618_ = lean_usize_dec_lt(v_i_3615_, v_sz_3614_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v_a_3612_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_b_3616_);
return v___x_3619_;
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; size_t v___x_3623_; size_t v___x_3624_; 
v_a_3620_ = lean_array_uget_borrowed(v_as_3613_, v_i_3615_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3612_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_a_3612_);
lean_ctor_set(v___x_3621_, 1, v_a_3620_);
v___x_3622_ = lean_array_push(v_b_3616_, v___x_3621_);
v___x_3623_ = ((size_t)1ULL);
v___x_3624_ = lean_usize_add(v_i_3615_, v___x_3623_);
v_i_3615_ = v___x_3624_;
v_b_3616_ = v___x_3622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3626_, lean_object* v_as_3627_, lean_object* v_sz_3628_, lean_object* v_i_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_){
_start:
{
size_t v_sz_boxed_3632_; size_t v_i_boxed_3633_; lean_object* v_res_3634_; 
v_sz_boxed_3632_ = lean_unbox_usize(v_sz_3628_);
lean_dec(v_sz_3628_);
v_i_boxed_3633_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3626_, v_as_3627_, v_sz_boxed_3632_, v_i_boxed_3633_, v_b_3630_);
lean_dec_ref(v_as_3627_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3635_, lean_object* v_xs_3636_, lean_object* v_as_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_b_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_usize_dec_lt(v_i_3639_, v_sz_3638_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; 
lean_dec_ref(v_xs_3636_);
lean_dec_ref(v_a_3635_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_b_3640_);
return v___x_3647_;
}
else
{
lean_object* v_snd_3648_; lean_object* v_fst_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3692_; 
v_snd_3648_ = lean_ctor_get(v_b_3640_, 1);
v_fst_3649_ = lean_ctor_get(v_b_3640_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_b_3640_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3651_ = v_b_3640_;
v_isShared_3652_ = v_isSharedCheck_3692_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_snd_3648_);
lean_inc(v_fst_3649_);
lean_dec(v_b_3640_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3692_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_array_3653_; lean_object* v_start_3654_; lean_object* v_stop_3655_; uint8_t v___x_3656_; 
v_array_3653_ = lean_ctor_get(v_snd_3648_, 0);
v_start_3654_ = lean_ctor_get(v_snd_3648_, 1);
v_stop_3655_ = lean_ctor_get(v_snd_3648_, 2);
v___x_3656_ = lean_nat_dec_lt(v_start_3654_, v_stop_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3658_; 
lean_dec_ref(v_xs_3636_);
lean_dec_ref(v_a_3635_);
if (v_isShared_3652_ == 0)
{
v___x_3658_ = v___x_3651_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_fst_3649_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_snd_3648_);
v___x_3658_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
}
else
{
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3688_; 
lean_inc(v_stop_3655_);
lean_inc(v_start_3654_);
lean_inc_ref(v_array_3653_);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_snd_3648_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; 
v_unused_3689_ = lean_ctor_get(v_snd_3648_, 2);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_snd_3648_, 1);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_snd_3648_, 0);
lean_dec(v_unused_3691_);
v___x_3662_ = v_snd_3648_;
v_isShared_3663_ = v_isSharedCheck_3688_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v_snd_3648_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3688_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_a_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_a_3664_ = lean_array_uget_borrowed(v_as_3637_, v_i_3639_);
v___x_3665_ = lean_array_fget_borrowed(v_array_3653_, v_start_3654_);
lean_inc(v_a_3664_);
lean_inc_ref(v_xs_3636_);
lean_inc_ref(v_a_3635_);
v___x_3666_ = l_Lean_Elab_Structural_argsInGroup(v_a_3635_, v_xs_3636_, v_a_3664_, v___x_3665_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = lean_unsigned_to_nat(1u);
v___x_3669_ = lean_nat_add(v_start_3654_, v___x_3668_);
lean_dec(v_start_3654_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v___x_3669_);
v___x_3671_ = v___x_3662_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_array_3653_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_stop_3655_);
v___x_3671_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = lean_array_push(v_fst_3649_, v_a_3667_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3671_);
lean_ctor_set(v___x_3651_, 0, v___x_3672_);
v___x_3674_ = v___x_3651_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3671_);
v___x_3674_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
size_t v___x_3675_; size_t v___x_3676_; 
v___x_3675_ = ((size_t)1ULL);
v___x_3676_ = lean_usize_add(v_i_3639_, v___x_3675_);
v_i_3639_ = v___x_3676_;
v_b_3640_ = v___x_3674_;
goto _start;
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_del_object(v___x_3662_);
lean_dec(v_stop_3655_);
lean_dec(v_start_3654_);
lean_dec_ref(v_array_3653_);
lean_del_object(v___x_3651_);
lean_dec(v_fst_3649_);
lean_dec_ref(v_xs_3636_);
lean_dec_ref(v_a_3635_);
v_a_3680_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3666_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3666_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3693_, lean_object* v_xs_3694_, lean_object* v_as_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
size_t v_sz_boxed_3704_; size_t v_i_boxed_3705_; lean_object* v_res_3706_; 
v_sz_boxed_3704_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3705_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3693_, v_xs_3694_, v_as_3695_, v_sz_boxed_3704_, v_i_boxed_3705_, v_b_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_as_3695_);
return v_res_3706_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3714_ = l_Lean_stringToMessageData(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3717_ = l_Lean_stringToMessageData(v___x_3716_);
return v___x_3717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3727_, lean_object* v_values_3728_, lean_object* v_xs_3729_, lean_object* v_fnNames_3730_, lean_object* v_as_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_a_3741_; uint8_t v___x_3745_; 
v___x_3745_ = lean_usize_dec_lt(v_i_3733_, v_sz_3732_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
lean_dec_ref(v_xs_3729_);
lean_dec_ref(v___x_3727_);
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_b_3734_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v_recArgInfoss_3748_; lean_object* v_a_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; size_t v_sz_3753_; size_t v___x_3754_; lean_object* v___x_3755_; 
v___x_3747_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3749_ = lean_array_uget_borrowed(v_as_3731_, v_i_3733_);
v___x_3750_ = lean_array_get_size(v___x_3727_);
lean_inc_ref(v___x_3727_);
v___x_3751_ = l_Array_toSubarray___redArg(v___x_3727_, v___x_3747_, v___x_3750_);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v_recArgInfoss_3748_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v_sz_3753_ = lean_array_size(v_values_3728_);
v___x_3754_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3729_);
lean_inc(v_a_3749_);
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3749_, v_xs_3729_, v_values_3728_, v_sz_3753_, v___x_3754_, v___x_3752_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v_fst_3757_; lean_object* v_snd_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3816_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v_fst_3757_ = lean_ctor_get(v_b_3734_, 0);
v_snd_3758_ = lean_ctor_get(v_b_3734_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_b_3734_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3760_ = v_b_3734_;
v_isShared_3761_ = v_isSharedCheck_3816_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_snd_3758_);
lean_inc(v_fst_3757_);
lean_dec(v_b_3734_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3816_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v_fst_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3814_; 
v_fst_3762_ = lean_ctor_get(v_a_3756_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_a_3756_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v_a_3756_, 1);
lean_dec(v_unused_3815_);
v___x_3764_ = v_a_3756_;
v_isShared_3765_ = v_isSharedCheck_3814_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_fst_3762_);
lean_dec(v_a_3756_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3814_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3762_, v___x_3747_);
if (lean_obj_tag(v___x_3766_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_dec(v_fst_3762_);
v_val_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_val_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3749_);
v___x_3770_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3749_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set_tag(v___x_3760_, 7);
lean_ctor_set(v___x_3760_, 1, v___x_3770_);
lean_ctor_set(v___x_3760_, 0, v___x_3769_);
v___x_3772_ = v___x_3760_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3773_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_array_get_borrowed(v___x_3768_, v_fnNames_3730_, v_val_3767_);
lean_dec(v_val_3767_);
lean_inc(v___x_3775_);
v___x_3776_ = l_Lean_MessageData_ofName(v___x_3775_);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3774_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_fst_3757_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v_snd_3758_);
lean_ctor_set(v___x_3764_, 0, v___x_3780_);
v___x_3782_ = v___x_3764_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_snd_3758_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
v_a_3741_ = v___x_3782_;
goto v___jp_3740_;
}
}
}
else
{
lean_object* v___x_3785_; 
lean_dec(v___x_3766_);
v___x_3785_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3762_);
lean_dec(v_fst_3762_);
if (lean_obj_tag(v___x_3785_) == 1)
{
lean_object* v_val_3786_; size_t v_sz_3787_; lean_object* v___x_3788_; 
lean_del_object(v___x_3760_);
v_val_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v_sz_3787_ = lean_array_size(v_val_3786_);
lean_inc(v_a_3749_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3749_, v_val_3786_, v_sz_3787_, v___x_3754_, v_snd_3758_);
lean_dec(v_val_3786_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v_a_3789_);
lean_ctor_set(v___x_3764_, 0, v_fst_3757_);
v___x_3791_ = v___x_3764_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_fst_3757_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_a_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v_a_3741_ = v___x_3791_;
goto v___jp_3740_;
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_del_object(v___x_3764_);
lean_dec(v_fst_3757_);
lean_dec_ref(v_xs_3729_);
lean_dec_ref(v___x_3727_);
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
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
lean_dec(v___x_3785_);
v___x_3801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3749_);
v___x_3802_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3749_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set_tag(v___x_3760_, 7);
lean_ctor_set(v___x_3760_, 1, v___x_3802_);
lean_ctor_set(v___x_3760_, 0, v___x_3801_);
v___x_3804_ = v___x_3760_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_fst_3757_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v_snd_3758_);
lean_ctor_set(v___x_3764_, 0, v___x_3809_);
v___x_3811_ = v___x_3764_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_snd_3758_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v_a_3741_ = v___x_3811_;
goto v___jp_3740_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v_b_3734_);
lean_dec_ref(v_xs_3729_);
lean_dec_ref(v___x_3727_);
v_a_3817_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3755_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3755_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
v___jp_3740_:
{
size_t v___x_3742_; size_t v___x_3743_; 
v___x_3742_ = ((size_t)1ULL);
v___x_3743_ = lean_usize_add(v_i_3733_, v___x_3742_);
v_i_3733_ = v___x_3743_;
v_b_3734_ = v_a_3741_;
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
lean_object* v___x_3861_; lean_object* v_recArgInfoss_3862_; lean_object* v_a_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; size_t v_sz_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3861_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3863_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
v___x_3864_ = lean_array_get_size(v___x_3842_);
lean_inc_ref(v___x_3842_);
v___x_3865_ = l_Array_toSubarray___redArg(v___x_3842_, v___x_3861_, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_recArgInfoss_3862_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v_sz_3867_ = lean_array_size(v_values_3843_);
v___x_3868_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3841_);
lean_inc(v_a_3863_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3863_, v_xs_3841_, v_values_3843_, v_sz_3867_, v___x_3868_, v___x_3866_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3930_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v_fst_3871_ = lean_ctor_get(v_b_3848_, 0);
v_snd_3872_ = lean_ctor_get(v_b_3848_, 1);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_b_3848_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3874_ = v_b_3848_;
v_isShared_3875_ = v_isSharedCheck_3930_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_snd_3872_);
lean_inc(v_fst_3871_);
lean_dec(v_b_3848_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3930_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_fst_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3928_; 
v_fst_3876_ = lean_ctor_get(v_a_3870_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3870_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_a_3870_, 1);
lean_dec(v_unused_3929_);
v___x_3878_ = v_a_3870_;
v_isShared_3879_ = v_isSharedCheck_3928_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_fst_3876_);
lean_dec(v_a_3870_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3928_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3876_, v___x_3861_);
if (lean_obj_tag(v___x_3880_) == 1)
{
lean_object* v_val_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
lean_dec(v_fst_3876_);
v_val_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_val_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3863_);
v___x_3884_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3863_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 7);
lean_ctor_set(v___x_3874_, 1, v___x_3884_);
lean_ctor_set(v___x_3874_, 0, v___x_3883_);
v___x_3886_ = v___x_3874_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_array_get_borrowed(v___x_3882_, v_fnNames_3844_, v_val_3881_);
lean_dec(v_val_3881_);
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
lean_ctor_set(v___x_3894_, 0, v_fst_3871_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v_snd_3872_);
lean_ctor_set(v___x_3878_, 0, v___x_3894_);
v___x_3896_ = v___x_3878_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_snd_3872_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
v_a_3855_ = v___x_3896_;
goto v___jp_3854_;
}
}
}
else
{
lean_object* v___x_3899_; 
lean_dec(v___x_3880_);
v___x_3899_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3876_);
lean_dec(v_fst_3876_);
if (lean_obj_tag(v___x_3899_) == 1)
{
lean_object* v_val_3900_; size_t v_sz_3901_; lean_object* v___x_3902_; 
lean_del_object(v___x_3874_);
v_val_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v_sz_3901_ = lean_array_size(v_val_3900_);
lean_inc(v_a_3863_);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3863_, v_val_3900_, v_sz_3901_, v___x_3868_, v_snd_3872_);
lean_dec(v_val_3900_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v_a_3903_);
lean_ctor_set(v___x_3878_, 0, v_fst_3871_);
v___x_3905_ = v___x_3878_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_fst_3871_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_a_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
v_a_3855_ = v___x_3905_;
goto v___jp_3854_;
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_del_object(v___x_3878_);
lean_dec(v_fst_3871_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v_xs_3841_);
v_a_3907_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3902_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3902_);
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
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
lean_dec(v___x_3899_);
v___x_3915_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3863_);
v___x_3916_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3863_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 7);
lean_ctor_set(v___x_3874_, 1, v___x_3916_);
lean_ctor_set(v___x_3874_, 0, v___x_3915_);
v___x_3918_ = v___x_3874_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v_fst_3871_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v_snd_3872_);
lean_ctor_set(v___x_3878_, 0, v___x_3923_);
v___x_3925_ = v___x_3878_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3872_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
v_a_3855_ = v___x_3925_;
goto v___jp_3854_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v_b_3848_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v_xs_3841_);
v_a_3931_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3869_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3869_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3939_, lean_object* v___x_3940_, lean_object* v_values_3941_, lean_object* v_fnNames_3942_, lean_object* v_as_3943_, lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3939_, v___x_3940_, v_values_3941_, v_fnNames_3942_, v_as_3943_, v_sz_boxed_3952_, v_i_boxed_3953_, v_b_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec_ref(v_as_3943_);
lean_dec_ref(v_fnNames_3942_);
lean_dec_ref(v_values_3941_);
return v_res_3954_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3959_ = l_Lean_MessageData_ofFormat(v___x_3958_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3962_ = l_Lean_stringToMessageData(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
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
lean_object* v___x_3980_; lean_object* v_recArgInfoss_3981_; lean_object* v___x_3982_; lean_object* v_perms_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_report_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3980_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
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
lean_ctor_set(v___x_3992_, 0, v_recArgInfoss_3981_);
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
v___x_4113_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
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
v___x_4119_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
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
lean_ctor_set(v___x_4007_, 1, v_recArgInfoss_3981_);
lean_ctor_set(v___x_4007_, 0, v_report_4015_);
v___x_4021_ = v___x_4007_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_report_4015_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_recArgInfoss_3981_);
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
v___x_4058_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
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
v___x_4069_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4068_, v___y_4065_, v___y_4067_, v___y_4066_, v___y_4064_);
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
v___y_4052_ = v___y_4065_;
v___y_4053_ = v___y_4067_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4064_;
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
v___y_4052_ = v___y_4065_;
v___y_4053_ = v___y_4067_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4064_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4078_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4074_);
v___x_4079_ = lean_array_to_list(v_a_4074_);
v___x_4080_ = lean_box(0);
v___x_4081_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4079_, v___x_4080_);
v___x_4082_ = l_Lean_MessageData_ofList(v___x_4081_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4078_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4062_, v___x_4083_, v___y_4065_, v___y_4067_, v___y_4066_, v___y_4064_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_dec_ref_known(v___x_4084_, 1);
v___y_4051_ = v_a_4074_;
v___y_4052_ = v___y_4065_;
v___y_4053_ = v___y_4067_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4064_;
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
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4107_ = lean_array_get_size(v___x_4012_);
v___x_4108_ = lean_nat_dec_lt(v___x_3980_, v___x_4107_);
if (v___x_4108_ == 0)
{
v___y_4064_ = v___y_4105_;
v___y_4065_ = v___y_4102_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4103_;
v___y_4068_ = v___x_4106_;
goto v___jp_4063_;
}
else
{
size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_usize_of_nat(v___x_4107_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4012_, v___x_3995_, v___x_4109_, v___x_4106_);
v___y_4064_ = v___y_4105_;
v___y_4065_ = v___y_4102_;
v___y_4066_ = v___y_4104_;
v___y_4067_ = v___y_4103_;
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
lean_object* v_a_4225_; uint8_t v___y_4227_; uint8_t v___x_4245_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
v___x_4245_ = l_Lean_Exception_isInterrupt(v_a_4225_);
if (v___x_4245_ == 0)
{
uint8_t v___x_4246_; 
lean_inc(v_a_4225_);
v___x_4246_ = l_Lean_Exception_isRuntime(v_a_4225_);
v___y_4227_ = v___x_4246_;
goto v___jp_4226_;
}
else
{
v___y_4227_ = v___x_4245_;
goto v___jp_4226_;
}
v___jp_4226_:
{
if (v___y_4227_ == 0)
{
lean_object* v___x_4228_; 
lean_dec_ref_known(v___x_4224_, 1);
v___x_4228_ = l_Lean_Meta_SavedState_restore___redArg(v_a_4223_, v___y_4218_, v___y_4220_);
lean_dec(v_a_4223_);
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
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v_x_4216_);
v_a_4247_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4222_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4222_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(lean_object* v_00_u03b1_4262_, lean_object* v_x_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v_x_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(lean_object* v_00_u03b1_4270_, lean_object* v_x_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(v_00_u03b1_4270_, v_x_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
return v_res_4277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0));
v___x_4280_ = l_Lean_stringToMessageData(v___x_4279_);
return v___x_4280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2));
v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(lean_object* v___x_4284_, uint8_t v___x_4285_, lean_object* v_group_4286_, lean_object* v_k_4287_, lean_object* v_comb_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(v___x_4284_, v___x_4285_, v___y_4292_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; uint8_t v___x_4296_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref_known(v___x_4294_, 1);
v___x_4296_ = lean_unbox(v_a_4295_);
lean_dec(v_a_4295_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
v___x_4298_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_4286_);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4301_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v___x_4303_; 
lean_dec_ref_known(v___x_4302_, 1);
v___x_4303_ = lean_apply_6(v_k_4287_, v_comb_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, lean_box(0));
return v___x_4303_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_comb_4288_);
lean_dec_ref(v_k_4287_);
v_a_4304_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4302_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4302_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_object* v___x_4312_; 
lean_dec_ref(v_group_4286_);
v___x_4312_ = lean_apply_6(v_k_4287_, v_comb_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, lean_box(0));
return v___x_4312_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_comb_4288_);
lean_dec_ref(v_k_4287_);
lean_dec_ref(v_group_4286_);
v_a_4313_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4294_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4294_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(lean_object* v___x_4321_, lean_object* v___x_4322_, lean_object* v_group_4323_, lean_object* v_k_4324_, lean_object* v_comb_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
uint8_t v___x_4304__boxed_4331_; lean_object* v_res_4332_; 
v___x_4304__boxed_4331_ = lean_unbox(v___x_4322_);
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4321_, v___x_4304__boxed_4331_, v_group_4323_, v_k_4324_, v_comb_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
return v_res_4332_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0));
v___x_4335_ = l_Lean_stringToMessageData(v___x_4334_);
return v___x_4335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4));
v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(lean_object* v_k_4338_, lean_object* v_fnNames_4339_, lean_object* v_xs_4340_, lean_object* v_values_4341_, lean_object* v_as_4342_, size_t v_sz_4343_, size_t v_i_4344_, lean_object* v_b_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
uint8_t v___x_4351_; 
v___x_4351_ = lean_usize_dec_lt(v_i_4344_, v_sz_4343_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; 
lean_dec_ref(v_values_4341_);
lean_dec_ref(v_xs_4340_);
lean_dec_ref(v_k_4338_);
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_b_4345_);
return v___x_4352_;
}
else
{
lean_object* v_snd_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4423_; 
v_snd_4353_ = lean_ctor_get(v_b_4345_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v_b_4345_);
if (v_isSharedCheck_4423_ == 0)
{
lean_object* v_unused_4424_; 
v_unused_4424_ = lean_ctor_get(v_b_4345_, 0);
lean_dec(v_unused_4424_);
v___x_4355_ = v_b_4345_;
v_isShared_4356_ = v_isSharedCheck_4423_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_snd_4353_);
lean_dec(v_b_4345_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4423_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_a_4357_; lean_object* v_group_4358_; lean_object* v_comb_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4422_; 
v_a_4357_ = lean_array_uget(v_as_4342_, v_i_4344_);
v_group_4358_ = lean_ctor_get(v_a_4357_, 0);
v_comb_4359_ = lean_ctor_get(v_a_4357_, 1);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_a_4357_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4361_ = v_a_4357_;
v_isShared_4362_ = v_isSharedCheck_4422_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_comb_4359_);
lean_inc(v_group_4358_);
lean_dec(v_a_4357_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4422_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_toIndGroupInfo_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___f_4367_; lean_object* v___x_4368_; 
v_toIndGroupInfo_4363_ = lean_ctor_get(v_group_4358_, 0);
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4363_, v___x_4364_);
v___x_4366_ = lean_box(v___x_4351_);
lean_inc_ref(v_comb_4359_);
lean_inc_ref(v_k_4338_);
v___f_4367_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4367_, 0, v___x_4365_);
lean_closure_set(v___f_4367_, 1, v___x_4366_);
lean_closure_set(v___f_4367_, 2, v_group_4358_);
lean_closure_set(v___f_4367_, 3, v_k_4338_);
lean_closure_set(v___f_4367_, 4, v_comb_4359_);
v___x_4368_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_4367_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4380_; 
lean_del_object(v___x_4361_);
lean_dec_ref(v_comb_4359_);
lean_dec_ref(v_values_4341_);
lean_dec_ref(v_xs_4340_);
lean_dec_ref(v_k_4338_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4380_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4380_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_a_4369_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4373_);
v___x_4375_ = v___x_4355_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4373_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_snd_4353_);
v___x_4375_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
lean_object* v___x_4377_; 
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4375_);
v___x_4377_ = v___x_4371_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4421_; 
v_a_4381_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4383_ = v___x_4368_;
v_isShared_4384_ = v_isSharedCheck_4421_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4368_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4421_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; uint8_t v___y_4387_; uint8_t v___x_4419_; 
v___x_4385_ = lean_box(0);
v___x_4419_ = l_Lean_Exception_isInterrupt(v_a_4381_);
if (v___x_4419_ == 0)
{
uint8_t v___x_4420_; 
lean_inc(v_a_4381_);
v___x_4420_ = l_Lean_Exception_isRuntime(v_a_4381_);
v___y_4387_ = v___x_4420_;
goto v___jp_4386_;
}
else
{
v___y_4387_ = v___x_4419_;
goto v___jp_4386_;
}
v___jp_4386_:
{
if (v___y_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_del_object(v___x_4383_);
lean_inc_ref(v_values_4341_);
lean_inc_ref(v_xs_4340_);
v___x_4388_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_4339_, v_xs_4340_, v_values_4341_, v_comb_4359_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; lean_object* v___x_4392_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v___x_4390_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
if (v_isShared_4362_ == 0)
{
lean_ctor_set_tag(v___x_4361_, 7);
lean_ctor_set(v___x_4361_, 1, v_a_4389_);
lean_ctor_set(v___x_4361_, 0, v___x_4390_);
v___x_4392_ = v___x_4361_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_a_4389_);
v___x_4392_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4393_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4392_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = l_Lean_Exception_toMessageData(v_a_4381_);
v___x_4396_ = l_Lean_indentD(v___x_4395_);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4394_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v_snd_4353_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 1, v___x_4400_);
lean_ctor_set(v___x_4355_, 0, v___x_4385_);
v___x_4402_ = v___x_4355_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4385_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
size_t v___x_4403_; size_t v___x_4404_; 
v___x_4403_ = ((size_t)1ULL);
v___x_4404_ = lean_usize_add(v_i_4344_, v___x_4403_);
v_i_4344_ = v___x_4404_;
v_b_4345_ = v___x_4402_;
goto _start;
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4381_);
lean_del_object(v___x_4361_);
lean_del_object(v___x_4355_);
lean_dec(v_snd_4353_);
lean_dec_ref(v_values_4341_);
lean_dec_ref(v_xs_4340_);
lean_dec_ref(v_k_4338_);
v_a_4408_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4388_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4388_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
else
{
lean_object* v___x_4417_; 
lean_del_object(v___x_4361_);
lean_dec_ref(v_comb_4359_);
lean_del_object(v___x_4355_);
lean_dec(v_snd_4353_);
lean_dec_ref(v_values_4341_);
lean_dec_ref(v_xs_4340_);
lean_dec_ref(v_k_4338_);
if (v_isShared_4384_ == 0)
{
v___x_4417_ = v___x_4383_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4381_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(lean_object* v_k_4425_, lean_object* v_fnNames_4426_, lean_object* v_xs_4427_, lean_object* v_values_4428_, lean_object* v_as_4429_, lean_object* v_sz_4430_, lean_object* v_i_4431_, lean_object* v_b_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
size_t v_sz_boxed_4438_; size_t v_i_boxed_4439_; lean_object* v_res_4440_; 
v_sz_boxed_4438_ = lean_unbox_usize(v_sz_4430_);
lean_dec(v_sz_4430_);
v_i_boxed_4439_ = lean_unbox_usize(v_i_4431_);
lean_dec(v_i_4431_);
v_res_4440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4425_, v_fnNames_4426_, v_xs_4427_, v_values_4428_, v_as_4429_, v_sz_boxed_4438_, v_i_boxed_4439_, v_b_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec_ref(v_as_4429_);
lean_dec_ref(v_fnNames_4426_);
return v_res_4440_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1(void){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0));
v___x_4443_ = l_Lean_stringToMessageData(v___x_4442_);
return v___x_4443_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = ((lean_object*)(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2));
v___x_4446_ = l_Lean_stringToMessageData(v___x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg(lean_object* v_fnNames_4447_, lean_object* v_xs_4448_, lean_object* v_values_4449_, lean_object* v_candidates_4450_, lean_object* v_k_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_candidates_4457_; lean_object* v_report_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4518_; 
v_candidates_4457_ = lean_ctor_get(v_candidates_4450_, 0);
v_report_4458_ = lean_ctor_get(v_candidates_4450_, 1);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_candidates_4450_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4460_ = v_candidates_4450_;
v_isShared_4461_ = v_isSharedCheck_4518_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_report_4458_);
lean_inc(v_candidates_4457_);
lean_dec(v_candidates_4450_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4518_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4462_ = lean_box(0);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4462_);
v___x_4464_ = v___x_4460_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_report_4458_);
v___x_4464_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
size_t v_sz_4465_; size_t v___x_4466_; lean_object* v___x_4467_; 
v_sz_4465_ = lean_array_size(v_candidates_4457_);
v___x_4466_ = ((size_t)0ULL);
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4451_, v_fnNames_4447_, v_xs_4448_, v_values_4449_, v_candidates_4457_, v_sz_4465_, v___x_4466_, v___x_4464_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
lean_dec_ref(v_candidates_4457_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4508_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4508_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4508_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v_fst_4472_; 
v_fst_4472_ = lean_ctor_get(v_a_4468_, 0);
if (lean_obj_tag(v_fst_4472_) == 0)
{
lean_object* v_toCold_4473_; lean_object* v_options_4474_; lean_object* v_snd_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4502_; 
lean_del_object(v___x_4470_);
v_toCold_4473_ = lean_ctor_get(v_a_4454_, 0);
v_options_4474_ = lean_ctor_get(v_toCold_4473_, 2);
v_snd_4475_ = lean_ctor_get(v_a_4468_, 1);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_a_4468_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v_a_4468_, 0);
lean_dec(v_unused_4503_);
v___x_4477_ = v_a_4468_;
v_isShared_4478_ = v_isSharedCheck_4502_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_snd_4475_);
lean_dec(v_a_4468_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4502_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v_inheritedTraceOptions_4479_; uint8_t v_hasTrace_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v_inheritedTraceOptions_4479_ = lean_ctor_get(v_toCold_4473_, 11);
v_hasTrace_4480_ = lean_ctor_get_uint8(v_options_4474_, sizeof(void*)*1);
v___x_4481_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__1, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1);
if (v_isShared_4478_ == 0)
{
lean_ctor_set_tag(v___x_4477_, 7);
lean_ctor_set(v___x_4477_, 0, v___x_4481_);
v___x_4483_ = v___x_4477_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_snd_4475_);
v___x_4483_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
if (v_hasTrace_4480_ == 0)
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4483_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4484_;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; 
v___x_4485_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4486_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4479_, v_options_4474_, v___x_4486_);
if (v___x_4487_ == 0)
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4483_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4488_;
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = lean_obj_once(&l_Lean_Elab_Structural_tryCandidates___redArg___closed__3, &l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3);
lean_inc_ref(v___x_4483_);
v___x_4490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
lean_ctor_set(v___x_4490_, 1, v___x_4483_);
v___x_4491_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4485_, v___x_4490_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4492_; 
lean_dec_ref_known(v___x_4491_, 1);
v___x_4492_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_4483_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4492_;
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec_ref(v___x_4483_);
v_a_4493_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4491_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4491_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
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
lean_object* v_val_4504_; lean_object* v___x_4506_; 
lean_inc_ref(v_fst_4472_);
lean_dec(v_a_4468_);
v_val_4504_ = lean_ctor_get(v_fst_4472_, 0);
lean_inc(v_val_4504_);
lean_dec_ref_known(v_fst_4472_, 1);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 0, v_val_4504_);
v___x_4506_ = v___x_4470_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_val_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
v_a_4509_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4467_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4467_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___redArg___boxed(lean_object* v_fnNames_4519_, lean_object* v_xs_4520_, lean_object* v_values_4521_, lean_object* v_candidates_4522_, lean_object* v_k_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4519_, v_xs_4520_, v_values_4521_, v_candidates_4522_, v_k_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec_ref(v_fnNames_4519_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates(lean_object* v_00_u03b1_4530_, lean_object* v_fnNames_4531_, lean_object* v_xs_4532_, lean_object* v_values_4533_, lean_object* v_candidates_4534_, lean_object* v_k_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_Elab_Structural_tryCandidates___redArg(v_fnNames_4531_, v_xs_4532_, v_values_4533_, v_candidates_4534_, v_k_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryCandidates___boxed(lean_object* v_00_u03b1_4542_, lean_object* v_fnNames_4543_, lean_object* v_xs_4544_, lean_object* v_values_4545_, lean_object* v_candidates_4546_, lean_object* v_k_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_Elab_Structural_tryCandidates(v_00_u03b1_4542_, v_fnNames_4543_, v_xs_4544_, v_values_4545_, v_candidates_4546_, v_k_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec_ref(v_fnNames_4543_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(lean_object* v_00_u03b1_4554_, lean_object* v_k_4555_, lean_object* v_fnNames_4556_, lean_object* v_xs_4557_, lean_object* v_values_4558_, lean_object* v_as_4559_, size_t v_sz_4560_, size_t v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v___x_4568_; 
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_4555_, v_fnNames_4556_, v_xs_4557_, v_values_4558_, v_as_4559_, v_sz_4560_, v_i_4561_, v_b_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(lean_object* v_00_u03b1_4569_, lean_object* v_k_4570_, lean_object* v_fnNames_4571_, lean_object* v_xs_4572_, lean_object* v_values_4573_, lean_object* v_as_4574_, lean_object* v_sz_4575_, lean_object* v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
size_t v_sz_boxed_4583_; size_t v_i_boxed_4584_; lean_object* v_res_4585_; 
v_sz_boxed_4583_ = lean_unbox_usize(v_sz_4575_);
lean_dec(v_sz_4575_);
v_i_boxed_4584_ = lean_unbox_usize(v_i_4576_);
lean_dec(v_i_4576_);
v_res_4585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_4569_, v_k_4570_, v_fnNames_4571_, v_xs_4572_, v_values_4573_, v_as_4574_, v_sz_boxed_4583_, v_i_boxed_4584_, v_b_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v_as_4574_);
lean_dec_ref(v_fnNames_4571_);
return v_res_4585_;
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
