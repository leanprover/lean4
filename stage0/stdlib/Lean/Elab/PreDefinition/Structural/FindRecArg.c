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
v___x_360_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_array_get(v___x_359_, v_values_310_, v___x_361_);
lean_dec_ref(v_values_310_);
v___x_363_ = lean_array_get(v___x_360_, v_recArgInfos_311_, v___x_361_);
lean_dec_ref(v_recArgInfos_311_);
v___x_364_ = l_Lean_Elab_Structural_prettyRecArg(v_xs_309_, v___x_362_, v___x_363_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
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
v___x_492_ = lean_st_ref_put(v___y_476_, v___x_491_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_4724__overap_971_; lean_object* v___x_972_; 
v___f_970_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___closed__0));
v___x_4724__overap_971_ = lean_panic_fn_borrowed(v___f_970_, v_msg_964_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
v___x_972_ = lean_apply_5(v___x_4724__overap_971_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, lean_box(0));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_984_ = lean_unsigned_to_nat(107u);
v___x_985_ = lean_unsigned_to_nat(97u);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_988_ = l_mkPanicMessageWithDecl(v___x_987_, v___x_986_, v___x_985_, v___x_984_, v___x_983_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(lean_object* v_xs_989_, size_t v_sz_990_, size_t v_i_991_, lean_object* v_bs_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_991_, v_sz_990_);
if (v___x_993_ == 0)
{
return v_bs_992_;
}
else
{
lean_object* v_v_994_; lean_object* v___x_995_; lean_object* v_bs_x27_996_; lean_object* v___y_998_; lean_object* v___x_1003_; 
v_v_994_ = lean_array_uget(v_bs_992_, v_i_991_);
v___x_995_ = lean_unsigned_to_nat(0u);
v_bs_x27_996_ = lean_array_uset(v_bs_992_, v_i_991_, v___x_995_);
v___x_1003_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_989_, v_v_994_);
lean_dec(v_v_994_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__3);
v___x_1005_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_1004_);
v___y_998_ = v___x_1005_;
goto v___jp_997_;
}
else
{
lean_object* v_val_1006_; 
v_val_1006_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v___x_1003_, 1);
v___y_998_ = v_val_1006_;
goto v___jp_997_;
}
v___jp_997_:
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_991_, v___x_999_);
v___x_1001_ = lean_array_uset(v_bs_x27_996_, v_i_991_, v___y_998_);
v_i_991_ = v___x_1000_;
v_bs_992_ = v___x_1001_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_xs_1007_, lean_object* v_sz_1008_, lean_object* v_i_1009_, lean_object* v_bs_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1008_);
lean_dec(v_sz_1008_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1007_, v_sz_boxed_1011_, v_i_boxed_1012_, v_bs_1010_);
lean_dec_ref(v_xs_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_ref_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_ref_1020_ = lean_ctor_get(v___y_1017_, 5);
v___x_1021_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc(v_ref_1020_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_ref_1020_);
lean_ctor_set(v___x_1026_, 1, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(lean_object* v_xs_1038_, lean_object* v_v_1039_, lean_object* v_i_1040_){
_start:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_array_get_size(v_xs_1038_);
v___x_1042_ = lean_nat_dec_lt(v_i_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec(v_i_1040_);
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_array_fget_borrowed(v_xs_1038_, v_i_1040_);
v___x_1045_ = lean_name_eq(v___x_1044_, v_v_1039_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v_i_1040_, v___x_1046_);
lean_dec(v_i_1040_);
v_i_1040_ = v___x_1047_;
goto _start;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_i_1040_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7___boxed(lean_object* v_xs_1050_, lean_object* v_v_1051_, lean_object* v_i_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1050_, v_v_1051_, v_i_1052_);
lean_dec(v_v_1051_);
lean_dec_ref(v_xs_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(lean_object* v_xs_1054_, lean_object* v_v_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5_spec__7(v_xs_1054_, v_v_1055_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5___boxed(lean_object* v_xs_1058_, lean_object* v_v_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1058_, v_v_1059_);
lean_dec(v_v_1059_);
lean_dec_ref(v_xs_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(lean_object* v_xs_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4_spec__5(v_xs_1061_, v_v_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_val_1065_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_val_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(lean_object* v_xs_1073_, lean_object* v_v_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1073_, v_v_1074_);
lean_dec(v_v_1074_);
lean_dec_ref(v_xs_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(lean_object* v_i_1076_, lean_object* v___x_1077_, lean_object* v_as_1078_, size_t v_i_1079_, size_t v_stop_1080_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_eq(v_i_1079_, v_stop_1080_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_array_uget_borrowed(v_as_1078_, v_i_1079_);
v___x_1087_ = l_Lean_Expr_isFVar(v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_nat_dec_lt(v_i_1076_, v___x_1077_);
if (v___x_1088_ == 0)
{
goto v___jp_1081_;
}
else
{
return v___x_1088_;
}
}
else
{
goto v___jp_1081_;
}
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
return v___x_1089_;
}
v___jp_1081_:
{
size_t v___x_1082_; size_t v___x_1083_; 
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1079_, v___x_1082_);
v_i_1079_ = v___x_1083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(lean_object* v_i_1090_, lean_object* v___x_1091_, lean_object* v_as_1092_, lean_object* v_i_1093_, lean_object* v_stop_1094_){
_start:
{
size_t v_i_boxed_1095_; size_t v_stop_boxed_1096_; uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_i_boxed_1095_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_stop_boxed_1096_ = lean_unbox_usize(v_stop_1094_);
lean_dec(v_stop_1094_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1090_, v___x_1091_, v_as_1092_, v_i_boxed_1095_, v_stop_boxed_1096_);
lean_dec_ref(v_as_1092_);
lean_dec(v___x_1091_);
lean_dec(v_i_1090_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(lean_object* v_as_1099_, lean_object* v_a_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_zero_1102_; uint8_t v_isZero_1103_; 
v_zero_1102_ = lean_unsigned_to_nat(0u);
v_isZero_1103_ = lean_nat_dec_eq(v_x_1101_, v_zero_1102_);
if (v_isZero_1103_ == 1)
{
lean_dec(v_x_1101_);
return v_isZero_1103_;
}
else
{
lean_object* v_one_1104_; lean_object* v_n_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_one_1104_ = lean_unsigned_to_nat(1u);
v_n_1105_ = lean_nat_sub(v_x_1101_, v_one_1104_);
lean_dec(v_x_1101_);
v___x_1106_ = lean_array_fget_borrowed(v_as_1099_, v_n_1105_);
v___x_1107_ = lean_expr_eqv(v_a_1100_, v___x_1106_);
if (v___x_1107_ == 0)
{
v_x_1101_ = v_n_1105_;
goto _start;
}
else
{
lean_dec(v_n_1105_);
return v_isZero_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_as_1109_, lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1109_, v_a_1110_, v_x_1111_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_as_1109_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(lean_object* v_as_1114_, lean_object* v_i_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_get_size(v_as_1114_);
v___x_1117_ = lean_nat_dec_lt(v_i_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; 
lean_dec(v_i_1115_);
v___x_1118_ = 1;
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_array_fget_borrowed(v_as_1114_, v_i_1115_);
lean_inc(v_i_1115_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1114_, v___x_1119_, v_i_1115_);
if (v___x_1120_ == 0)
{
lean_dec(v_i_1115_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_i_1115_, v___x_1121_);
lean_dec(v_i_1115_);
v_i_1115_ = v___x_1122_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3___boxed(lean_object* v_as_1124_, lean_object* v_i_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1124_, v_i_1125_);
lean_dec_ref(v_as_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(lean_object* v_as_1128_){
_start:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3(v_as_1128_, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(lean_object* v_as_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_as_1131_);
lean_dec_ref(v_as_1131_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__0));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__2));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__4));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__6));
v___x_1145_ = lean_unsigned_to_nat(59u);
v___x_1146_ = lean_unsigned_to_nat(96u);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1149_ = l_mkPanicMessageWithDecl(v___x_1148_, v___x_1147_, v___x_1146_, v___x_1145_, v___x_1144_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__8));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__10));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__12));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__14));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__16));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__18));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__20));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__22));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24(void){
_start:
{
lean_object* v___x_1174_; lean_object* v_dummy_1175_; 
v___x_1174_ = lean_box(0);
v_dummy_1175_ = l_Lean_Expr_sort___override(v___x_1174_);
return v_dummy_1175_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__25));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__27));
v___x_1181_ = lean_unsigned_to_nat(2u);
v___x_1182_ = lean_unsigned_to_nat(68u);
v___x_1183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__1));
v___x_1184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_1185_ = l_mkPanicMessageWithDecl(v___x_1184_, v___x_1183_, v___x_1182_, v___x_1181_, v___x_1180_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__29));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__31));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__33));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfo___closed__35));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo(lean_object* v_fnName_1198_, lean_object* v_fixedParamPerm_1199_, lean_object* v_xs_1200_, lean_object* v_i_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v_lower_1348_; lean_object* v_upper_1349_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; uint8_t v___x_1434_; 
v___x_1333_ = lean_array_get_size(v_fixedParamPerm_1199_);
v___x_1334_ = lean_array_get_size(v_xs_1200_);
v___x_1434_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__28, &l_Lean_Elab_Structural_getRecArgInfo___closed__28_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28);
v___x_1436_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1435_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1436_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_lt(v_i_1201_, v___x_1334_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___x_1438_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__30, &l_Lean_Elab_Structural_getRecArgInfo___closed__30_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v_i_1201_, v___x_1439_);
lean_dec(v_i_1201_);
v___x_1441_ = l_Nat_reprFast(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = l_Lean_MessageData_ofFormat(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1438_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__32, &l_Lean_Elab_Structural_getRecArgInfo___closed__32_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Nat_reprFast(v___x_1334_);
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l_Lean_MessageData_ofFormat(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__34, &l_Lean_Elab_Structural_getRecArgInfo___closed__34_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1452_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1453_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_1199_, v_i_1201_);
if (v___x_1454_ == 0)
{
v___y_1407_ = v_a_1202_;
v___y_1408_ = v_a_1203_;
v___y_1409_ = v_a_1204_;
v___y_1410_ = v_a_1205_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__36, &l_Lean_Elab_Structural_getRecArgInfo___closed__36_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36);
v___x_1456_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1455_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
v___jp_1207_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__1, &l_Lean_Elab_Structural_getRecArgInfo___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1);
v___x_1213_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1212_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
v___jp_1214_:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___y_1218_);
if (v___x_1226_ == 0)
{
lean_object* v_name_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_name_1227_ = lean_ctor_get(v___y_1216_, 0);
lean_inc(v_name_1227_);
lean_dec_ref(v___y_1216_);
v___x_1228_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1229_ = l_Lean_MessageData_ofName(v_name_1227_);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_indentExpr(v___y_1217_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1234_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1199_, v_xs_1200_);
v___x_1237_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1236_, v___y_1218_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
if (lean_obj_tag(v_a_1238_) == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1236_, v___y_1224_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
lean_dec_ref(v___x_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1290_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1290_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1290_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_a_1240_) == 0)
{
lean_object* v_name_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v___y_1217_);
v_name_1244_ = lean_ctor_get(v___y_1216_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___y_1216_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; lean_object* v_unused_1266_; 
v_unused_1265_ = lean_ctor_get(v___y_1216_, 2);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v___y_1216_, 1);
lean_dec(v_unused_1266_);
v___x_1246_ = v___y_1216_;
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_name_1244_);
lean_dec(v___y_1216_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1264_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_array_mk(v___y_1220_);
v___x_1249_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v___x_1248_, v_name_1244_);
lean_dec(v_name_1244_);
lean_dec_ref(v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 1)
{
lean_object* v_val_1250_; size_t v_sz_1251_; size_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v_sz_1251_ = lean_array_size(v___y_1218_);
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_xs_1200_, v_sz_1251_, v___x_1252_, v___y_1218_);
v___x_1254_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1219_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 2, v___y_1224_);
lean_ctor_set(v___x_1246_, 1, v___y_1223_);
lean_ctor_set(v___x_1246_, 0, v___x_1254_);
v___x_1256_ = v___x_1246_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___y_1223_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v___y_1224_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1257_, 0, v_fnName_1198_);
lean_ctor_set(v___x_1257_, 1, v_fixedParamPerm_1199_);
lean_ctor_set(v___x_1257_, 2, v_i_1201_);
lean_ctor_set(v___x_1257_, 3, v___x_1253_);
lean_ctor_set(v___x_1257_, 4, v___x_1256_);
lean_ctor_set(v___x_1257_, 5, v_val_1250_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1257_);
v___x_1259_ = v___x_1242_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v___x_1249_);
lean_del_object(v___x_1246_);
lean_del_object(v___x_1242_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___x_1262_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1263_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___x_1262_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
return v___x_1263_;
}
}
}
else
{
lean_object* v_val_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1289_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1216_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_val_1267_ = lean_ctor_get(v_a_1240_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v_a_1240_, 1);
v_fst_1268_ = lean_ctor_get(v_val_1267_, 0);
v_snd_1269_ = lean_ctor_get(v_val_1267_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_val_1267_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1271_ = v_val_1267_;
v_isShared_1272_ = v_isSharedCheck_1289_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snd_1269_);
lean_inc(v_fst_1268_);
lean_dec(v_val_1267_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1289_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1273_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__9, &l_Lean_Elab_Structural_getRecArgInfo___closed__9_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9);
v___x_1274_ = l_Lean_indentExpr(v___y_1217_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 7);
lean_ctor_set(v___x_1271_, 1, v___x_1274_);
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1277_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__11, &l_Lean_Elab_Structural_getRecArgInfo___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_indentExpr(v_fst_1268_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__13, &l_Lean_Elab_Structural_getRecArgInfo___closed__13_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_indentExpr(v_snd_1269_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__15, &l_Lean_Elab_Structural_getRecArgInfo___closed__15_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1286_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
return v___x_1287_;
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_a_1291_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1239_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1239_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_val_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_val_1299_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_a_1238_, 1);
v_fst_1300_ = lean_ctor_get(v_val_1299_, 0);
v_snd_1301_ = lean_ctor_get(v_val_1299_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_val_1299_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1303_ = v_val_1299_;
v_isShared_1304_ = v_isSharedCheck_1324_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_snd_1301_);
lean_inc(v_fst_1300_);
lean_dec(v_val_1299_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1324_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_name_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v_name_1305_ = lean_ctor_get(v___y_1216_, 0);
lean_inc(v_name_1305_);
lean_dec_ref(v___y_1216_);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1307_ = l_Lean_MessageData_ofName(v_name_1305_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 7);
lean_ctor_set(v___x_1303_, 1, v___x_1307_);
lean_ctor_set(v___x_1303_, 0, v___x_1306_);
v___x_1309_ = v___x_1303_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1310_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__17, &l_Lean_Elab_Structural_getRecArgInfo___closed__17_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_indentExpr(v___y_1217_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__19, &l_Lean_Elab_Structural_getRecArgInfo___closed__19_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_indentExpr(v_fst_1300_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__21, &l_Lean_Elab_Structural_getRecArgInfo___closed__21_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = l_Lean_indentExpr(v_snd_1301_);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1321_, v___y_1225_, v___y_1221_, v___y_1215_, v___y_1222_);
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_a_1325_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1237_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1237_);
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
}
v___jp_1335_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1350_ = l_Array_toSubarray___redArg(v___y_1336_, v_lower_1348_, v_upper_1349_);
v___x_1351_ = l_Subarray_copy___redArg(v___x_1350_);
v___x_1352_ = lean_array_get_size(v___x_1351_);
v___x_1353_ = lean_nat_dec_lt(v___y_1345_, v___x_1352_);
lean_dec(v___y_1345_);
if (v___x_1353_ == 0)
{
v___y_1215_ = v___y_1342_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1343_;
v___y_1218_ = v___x_1351_;
v___y_1219_ = v___y_1338_;
v___y_1220_ = v___y_1344_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1346_;
v___y_1225_ = v___y_1347_;
goto v___jp_1214_;
}
else
{
if (v___x_1353_ == 0)
{
v___y_1215_ = v___y_1342_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1343_;
v___y_1218_ = v___x_1351_;
v___y_1219_ = v___y_1338_;
v___y_1220_ = v___y_1344_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1346_;
v___y_1225_ = v___y_1347_;
goto v___jp_1214_;
}
else
{
size_t v___x_1354_; size_t v___x_1355_; uint8_t v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1352_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_i_1201_, v___x_1334_, v___x_1351_, v___x_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
v___y_1215_ = v___y_1342_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___y_1343_;
v___y_1218_ = v___x_1351_;
v___y_1219_ = v___y_1338_;
v___y_1220_ = v___y_1344_;
v___y_1221_ = v___y_1339_;
v___y_1222_ = v___y_1340_;
v___y_1223_ = v___y_1341_;
v___y_1224_ = v___y_1346_;
v___y_1225_ = v___y_1347_;
goto v___jp_1214_;
}
else
{
lean_object* v_name_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v___x_1351_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1344_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1338_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_name_1357_ = lean_ctor_get(v___y_1337_, 0);
lean_inc(v_name_1357_);
lean_dec_ref(v___y_1337_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1359_ = l_Lean_MessageData_ofName(v_name_1357_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__23, &l_Lean_Elab_Structural_getRecArgInfo___closed__23_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_indentExpr(v___y_1343_);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1364_, v___y_1347_, v___y_1339_, v___y_1342_, v___y_1340_);
return v___x_1365_;
}
}
}
}
v___jp_1366_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = l_Lean_LocalDecl_type(v___y_1367_);
lean_dec_ref(v___y_1367_);
v___x_1373_ = l_Lean_Meta_whnfD(v___x_1372_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_Expr_getAppFn(v_a_1374_);
if (lean_obj_tag(v___x_1375_) == 4)
{
lean_object* v_declName_1376_; lean_object* v_us_1377_; lean_object* v___x_1378_; lean_object* v_env_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; 
v_declName_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_declName_1376_);
v_us_1377_ = lean_ctor_get(v___x_1375_, 1);
lean_inc(v_us_1377_);
lean_dec_ref_known(v___x_1375_, 2);
v___x_1378_ = lean_st_ref_get(v___y_1371_);
v_env_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_ref(v_env_1379_);
lean_dec(v___x_1378_);
v___x_1380_ = 0;
v___x_1381_ = l_Lean_Environment_find_x3f(v_env_1379_, v_declName_1376_, v___x_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec(v_us_1377_);
lean_dec(v_a_1374_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___y_1208_ = v___y_1368_;
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
goto v___jp_1207_;
}
else
{
lean_object* v_val_1382_; 
v_val_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v_val_1382_) == 5)
{
lean_object* v_val_1383_; lean_object* v_toConstantVal_1384_; lean_object* v_numParams_1385_; lean_object* v_all_1386_; lean_object* v_nargs_1387_; lean_object* v_dummy_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_val_1383_ = lean_ctor_get(v_val_1382_, 0);
lean_inc_ref(v_val_1383_);
lean_dec_ref_known(v_val_1382_, 1);
v_toConstantVal_1384_ = lean_ctor_get(v_val_1383_, 0);
lean_inc_ref(v_toConstantVal_1384_);
v_numParams_1385_ = lean_ctor_get(v_val_1383_, 1);
v_all_1386_ = lean_ctor_get(v_val_1383_, 3);
lean_inc(v_all_1386_);
v_nargs_1387_ = l_Lean_Expr_getAppNumArgs(v_a_1374_);
v_dummy_1388_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__24, &l_Lean_Elab_Structural_getRecArgInfo___closed__24_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24);
lean_inc(v_nargs_1387_);
v___x_1389_ = lean_mk_array(v_nargs_1387_, v_dummy_1388_);
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_nat_sub(v_nargs_1387_, v___x_1390_);
lean_dec(v_nargs_1387_);
lean_inc(v_a_1374_);
v___x_1392_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1374_, v___x_1389_, v___x_1391_);
v___x_1393_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1385_);
lean_inc_ref(v___x_1392_);
v___x_1394_ = l_Array_toSubarray___redArg(v___x_1392_, v___x_1393_, v_numParams_1385_);
v___x_1395_ = l_Subarray_copy___redArg(v___x_1394_);
v___x_1396_ = lean_array_get_size(v___x_1392_);
v___x_1397_ = lean_nat_dec_le(v_numParams_1385_, v___x_1393_);
if (v___x_1397_ == 0)
{
lean_inc(v_numParams_1385_);
v___y_1336_ = v___x_1392_;
v___y_1337_ = v_toConstantVal_1384_;
v___y_1338_ = v_val_1383_;
v___y_1339_ = v___y_1369_;
v___y_1340_ = v___y_1371_;
v___y_1341_ = v_us_1377_;
v___y_1342_ = v___y_1370_;
v___y_1343_ = v_a_1374_;
v___y_1344_ = v_all_1386_;
v___y_1345_ = v___x_1393_;
v___y_1346_ = v___x_1395_;
v___y_1347_ = v___y_1368_;
v_lower_1348_ = v_numParams_1385_;
v_upper_1349_ = v___x_1396_;
goto v___jp_1335_;
}
else
{
v___y_1336_ = v___x_1392_;
v___y_1337_ = v_toConstantVal_1384_;
v___y_1338_ = v_val_1383_;
v___y_1339_ = v___y_1369_;
v___y_1340_ = v___y_1371_;
v___y_1341_ = v_us_1377_;
v___y_1342_ = v___y_1370_;
v___y_1343_ = v_a_1374_;
v___y_1344_ = v_all_1386_;
v___y_1345_ = v___x_1393_;
v___y_1346_ = v___x_1395_;
v___y_1347_ = v___y_1368_;
v_lower_1348_ = v___x_1393_;
v_upper_1349_ = v___x_1396_;
goto v___jp_1335_;
}
}
else
{
lean_dec(v_val_1382_);
lean_dec(v_us_1377_);
lean_dec(v_a_1374_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___y_1208_ = v___y_1368_;
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
goto v___jp_1207_;
}
}
}
else
{
lean_dec_ref(v___x_1375_);
lean_dec(v_a_1374_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___y_1208_ = v___y_1368_;
v___y_1209_ = v___y_1369_;
v___y_1210_ = v___y_1370_;
v___y_1211_ = v___y_1371_;
goto v___jp_1207_;
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_a_1398_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1373_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1373_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
v___jp_1406_:
{
lean_object* v_x_1411_; lean_object* v___x_1412_; 
v_x_1411_ = lean_array_fget_borrowed(v_xs_1200_, v_i_1201_);
v___x_1412_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_x_1411_, v___y_1407_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; uint8_t v___x_1414_; uint8_t v___x_1415_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = 0;
v___x_1415_ = l_Lean_LocalDecl_isLet(v_a_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
v___y_1367_ = v_a_1413_;
v___y_1368_ = v___y_1407_;
v___y_1369_ = v___y_1408_;
v___y_1370_ = v___y_1409_;
v___y_1371_ = v___y_1410_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1413_);
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v___x_1416_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__26, &l_Lean_Elab_Structural_getRecArgInfo___closed__26_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26);
v___x_1417_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1416_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
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
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_i_1201_);
lean_dec_ref(v_fixedParamPerm_1199_);
lean_dec(v_fnName_1198_);
v_a_1426_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1412_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1412_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfo___boxed(lean_object* v_fnName_1465_, lean_object* v_fixedParamPerm_1466_, lean_object* v_xs_1467_, lean_object* v_i_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1465_, v_fixedParamPerm_1466_, v_xs_1467_, v_i_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec_ref(v_xs_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(lean_object* v_00_u03b1_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v_msg_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_msg_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(v_00_u03b1_1483_, v_msg_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(lean_object* v_as_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___redArg(v_as_1491_, v_a_1492_, v_x_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4___boxed(lean_object* v_as_1496_, lean_object* v_a_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__3_spec__4(v_as_1496_, v_a_1497_, v_x_1498_, v_x_1499_);
lean_dec_ref(v_a_1497_);
lean_dec_ref(v_as_1496_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__0(lean_object* v___x_1502_, lean_object* v_e_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = l_Lean_indentD(v_e_1503_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1(lean_object* v_val_1506_, lean_object* v_fnName_1507_, lean_object* v_fixedParamPerm_1508_, lean_object* v_args_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_val_1506_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1507_, v_fixedParamPerm_1508_, v_args_1509_, v_a_1516_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1517_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v_fixedParamPerm_1508_);
lean_dec(v_fnName_1507_);
v_a_1518_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1515_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1515_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(lean_object* v_val_1526_, lean_object* v_fnName_1527_, lean_object* v_fixedParamPerm_1528_, lean_object* v_args_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(v_val_1526_, v_fnName_1527_, v_fixedParamPerm_1528_, v_args_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_args_1529_);
return v_res_1535_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5));
v___x_1546_ = l_Lean_MessageData_ofFormat(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(lean_object* v_upperBound_1547_, lean_object* v_fnName_1548_, lean_object* v_fixedParamPerm_1549_, lean_object* v_args_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_fst_1559_; lean_object* v_snd_1560_; uint8_t v___x_1565_; 
v___x_1565_ = lean_nat_dec_lt(v_a_1551_, v_upperBound_1547_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec(v_a_1551_);
lean_dec_ref(v_fixedParamPerm_1549_);
lean_dec(v_fnName_1548_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_b_1552_);
return v___x_1566_;
}
else
{
lean_object* v_fst_1567_; lean_object* v_snd_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1613_; 
v_fst_1567_ = lean_ctor_get(v_b_1552_, 0);
v_snd_1568_ = lean_ctor_get(v_b_1552_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_b_1552_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1570_ = v_b_1552_;
v_isShared_1571_ = v_isSharedCheck_1613_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snd_1568_);
lean_inc(v_fst_1567_);
lean_dec(v_b_1552_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1613_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; 
lean_inc(v_a_1551_);
lean_inc_ref(v_fixedParamPerm_1549_);
lean_inc(v_fnName_1548_);
v___x_1572_ = l_Lean_Elab_Structural_getRecArgInfo(v_fnName_1548_, v_fixedParamPerm_1549_, v_args_1550_, v_a_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1570_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_array_push(v_fst_1567_, v_a_1573_);
v_fst_1559_ = v___x_1574_;
v_snd_1560_ = v_snd_1568_;
goto v___jp_1558_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1612_; 
v_a_1575_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1577_ = v___x_1572_;
v_isShared_1578_ = v_isSharedCheck_1612_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1572_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1612_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___y_1580_; uint8_t v___x_1610_; 
v___x_1610_ = l_Lean_Exception_isInterrupt(v_a_1575_);
if (v___x_1610_ == 0)
{
uint8_t v___x_1611_; 
lean_inc(v_a_1575_);
v___x_1611_ = l_Lean_Exception_isRuntime(v_a_1575_);
v___y_1580_ = v___x_1611_;
goto v___jp_1579_;
}
else
{
v___y_1580_ = v___x_1610_;
goto v___jp_1579_;
}
v___jp_1579_:
{
if (v___y_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_del_object(v___x_1577_);
v___x_1581_ = l_Lean_Elab_Structural_prettyParam(v_args_1550_, v_a_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 7);
lean_ctor_set(v___x_1570_, 1, v_a_1582_);
lean_ctor_set(v___x_1570_, 0, v___x_1583_);
v___x_1585_ = v___x_1570_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1582_);
v___x_1585_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1586_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc(v_fnName_1548_);
v___x_1588_ = l_Lean_MessageData_ofName(v_fnName_1548_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Exception_toMessageData(v_a_1575_);
v___x_1593_ = l_Lean_indentD(v___x_1592_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_snd_1568_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v_fst_1559_ = v_fst_1567_;
v_snd_1560_ = v___x_1597_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1575_);
lean_del_object(v___x_1570_);
lean_dec(v_snd_1568_);
lean_dec(v_fst_1567_);
lean_dec(v_a_1551_);
lean_dec_ref(v_fixedParamPerm_1549_);
lean_dec(v_fnName_1548_);
v_a_1599_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1581_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1581_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1570_);
lean_dec(v_snd_1568_);
lean_dec(v_fst_1567_);
lean_dec(v_a_1551_);
lean_dec_ref(v_fixedParamPerm_1549_);
lean_dec(v_fnName_1548_);
if (v_isShared_1578_ == 0)
{
v___x_1608_ = v___x_1577_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1575_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
}
v___jp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_fst_1559_);
lean_ctor_set(v___x_1561_, 1, v_snd_1560_);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_add(v_a_1551_, v___x_1562_);
lean_dec(v_a_1551_);
v_a_1551_ = v___x_1563_;
v_b_1552_ = v___x_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(lean_object* v_upperBound_1614_, lean_object* v_fnName_1615_, lean_object* v_fixedParamPerm_1616_, lean_object* v_args_1617_, lean_object* v_a_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1614_, v_fnName_1615_, v_fixedParamPerm_1616_, v_args_1617_, v_a_1618_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_args_1617_);
lean_dec(v_upperBound_1614_);
return v_res_1625_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1626_; double v___x_1627_; 
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_float_of_nat(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(lean_object* v_cls_1629_, lean_object* v_msg_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_ref_1636_; lean_object* v___x_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1682_; 
v_ref_1636_ = lean_ctor_get(v___y_1633_, 5);
v___x_1637_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1682_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1682_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v_traceState_1643_; lean_object* v_env_1644_; lean_object* v_nextMacroScope_1645_; lean_object* v_ngen_1646_; lean_object* v_auxDeclNGen_1647_; lean_object* v_cache_1648_; lean_object* v_messages_1649_; lean_object* v_infoState_1650_; lean_object* v_snapshotTasks_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1681_; 
v___x_1642_ = lean_st_ref_take(v___y_1634_);
v_traceState_1643_ = lean_ctor_get(v___x_1642_, 4);
v_env_1644_ = lean_ctor_get(v___x_1642_, 0);
v_nextMacroScope_1645_ = lean_ctor_get(v___x_1642_, 1);
v_ngen_1646_ = lean_ctor_get(v___x_1642_, 2);
v_auxDeclNGen_1647_ = lean_ctor_get(v___x_1642_, 3);
v_cache_1648_ = lean_ctor_get(v___x_1642_, 5);
v_messages_1649_ = lean_ctor_get(v___x_1642_, 6);
v_infoState_1650_ = lean_ctor_get(v___x_1642_, 7);
v_snapshotTasks_1651_ = lean_ctor_get(v___x_1642_, 8);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1681_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snapshotTasks_1651_);
lean_inc(v_infoState_1650_);
lean_inc(v_messages_1649_);
lean_inc(v_cache_1648_);
lean_inc(v_traceState_1643_);
lean_inc(v_auxDeclNGen_1647_);
lean_inc(v_ngen_1646_);
lean_inc(v_nextMacroScope_1645_);
lean_inc(v_env_1644_);
lean_dec(v___x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1681_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint64_t v_tid_1655_; lean_object* v_traces_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1680_; 
v_tid_1655_ = lean_ctor_get_uint64(v_traceState_1643_, sizeof(void*)*1);
v_traces_1656_ = lean_ctor_get(v_traceState_1643_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_traceState_1643_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1658_ = v_traceState_1643_;
v_isShared_1659_ = v_isSharedCheck_1680_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_traces_1656_);
lean_dec(v_traceState_1643_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1680_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; double v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
v___x_1662_ = 0;
v___x_1663_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1664_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1664_, 0, v_cls_1629_);
lean_ctor_set(v___x_1664_, 1, v___x_1660_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
lean_ctor_set_float(v___x_1664_, sizeof(void*)*3, v___x_1661_);
lean_ctor_set_float(v___x_1664_, sizeof(void*)*3 + 8, v___x_1661_);
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*3 + 16, v___x_1662_);
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_1666_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v_a_1638_);
lean_ctor_set(v___x_1666_, 2, v___x_1665_);
lean_inc(v_ref_1636_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_ref_1636_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_PersistentArray_push___redArg(v_traces_1656_, v___x_1667_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1668_);
v___x_1670_ = v___x_1658_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1668_);
lean_ctor_set_uint64(v_reuseFailAlloc_1679_, sizeof(void*)*1, v_tid_1655_);
v___x_1670_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v___x_1670_);
v___x_1672_ = v___x_1653_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_env_1644_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_nextMacroScope_1645_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_ngen_1646_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_auxDeclNGen_1647_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1678_, 5, v_cache_1648_);
lean_ctor_set(v_reuseFailAlloc_1678_, 6, v_messages_1649_);
lean_ctor_set(v_reuseFailAlloc_1678_, 7, v_infoState_1650_);
lean_ctor_set(v_reuseFailAlloc_1678_, 8, v_snapshotTasks_1651_);
v___x_1672_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1673_ = lean_st_ref_put(v___y_1634_, v___x_1672_);
v___x_1674_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1674_);
v___x_1676_ = v___x_1640_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(lean_object* v_cls_1683_, lean_object* v_msg_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v_cls_1683_, v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1690_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0));
v___x_1693_ = l_Lean_stringToMessageData(v___x_1692_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___f_1695_; 
v___x_1694_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__0), 2, 1);
lean_closure_set(v___f_1695_, 0, v___x_1694_);
return v___f_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5(void){
_start:
{
lean_object* v_report_1700_; lean_object* v_recArgInfos_1701_; lean_object* v___x_1702_; 
v_report_1700_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v_recArgInfos_1701_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_recArgInfos_1701_);
lean_ctor_set(v___x_1702_, 1, v_report_1700_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11));
v___x_1715_ = l_Lean_Name_append(v___x_1714_, v___x_1713_);
return v___x_1715_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13));
v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2(lean_object* v_termMeasure_x3f_1719_, lean_object* v_fixedParamPerm_1720_, lean_object* v_xs_1721_, lean_object* v_fnName_1722_, lean_object* v_ys_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
if (lean_obj_tag(v_termMeasure_x3f_1719_) == 1)
{
lean_object* v_val_1730_; lean_object* v_ref_1731_; lean_object* v_fileName_1732_; lean_object* v_fileMap_1733_; lean_object* v_options_1734_; lean_object* v_currRecDepth_1735_; lean_object* v_maxRecDepth_1736_; lean_object* v_ref_1737_; lean_object* v_currNamespace_1738_; lean_object* v_openDecls_1739_; lean_object* v_initHeartbeats_1740_; lean_object* v_maxHeartbeats_1741_; lean_object* v_quotContext_1742_; lean_object* v_currMacroScope_1743_; uint8_t v_diag_1744_; lean_object* v_cancelTk_x3f_1745_; uint8_t v_suppressElabErrors_1746_; lean_object* v_inheritedTraceOptions_1747_; lean_object* v___f_1748_; lean_object* v_args_1749_; lean_object* v___f_1750_; lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_val_1730_ = lean_ctor_get(v_termMeasure_x3f_1719_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v_termMeasure_x3f_1719_, 1);
v_ref_1731_ = lean_ctor_get(v_val_1730_, 0);
lean_inc(v_ref_1731_);
v_fileName_1732_ = lean_ctor_get(v___y_1727_, 0);
v_fileMap_1733_ = lean_ctor_get(v___y_1727_, 1);
v_options_1734_ = lean_ctor_get(v___y_1727_, 2);
v_currRecDepth_1735_ = lean_ctor_get(v___y_1727_, 3);
v_maxRecDepth_1736_ = lean_ctor_get(v___y_1727_, 4);
v_ref_1737_ = lean_ctor_get(v___y_1727_, 5);
v_currNamespace_1738_ = lean_ctor_get(v___y_1727_, 6);
v_openDecls_1739_ = lean_ctor_get(v___y_1727_, 7);
v_initHeartbeats_1740_ = lean_ctor_get(v___y_1727_, 8);
v_maxHeartbeats_1741_ = lean_ctor_get(v___y_1727_, 9);
v_quotContext_1742_ = lean_ctor_get(v___y_1727_, 10);
v_currMacroScope_1743_ = lean_ctor_get(v___y_1727_, 11);
v_diag_1744_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*14);
v_cancelTk_x3f_1745_ = lean_ctor_get(v___y_1727_, 12);
v_suppressElabErrors_1746_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1747_ = lean_ctor_get(v___y_1727_, 13);
v___f_1748_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1720_);
v_args_1749_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1720_, v_xs_1721_, v_ys_1723_);
v___f_1750_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1750_, 0, v_val_1730_);
lean_closure_set(v___f_1750_, 1, v_fnName_1722_);
lean_closure_set(v___f_1750_, 2, v_fixedParamPerm_1720_);
lean_closure_set(v___f_1750_, 3, v_args_1749_);
v_ref_1751_ = l_Lean_replaceRef(v_ref_1731_, v_ref_1737_);
lean_dec(v_ref_1731_);
lean_inc_ref(v_inheritedTraceOptions_1747_);
lean_inc(v_cancelTk_x3f_1745_);
lean_inc(v_currMacroScope_1743_);
lean_inc(v_quotContext_1742_);
lean_inc(v_maxHeartbeats_1741_);
lean_inc(v_initHeartbeats_1740_);
lean_inc(v_openDecls_1739_);
lean_inc(v_currNamespace_1738_);
lean_inc(v_maxRecDepth_1736_);
lean_inc(v_currRecDepth_1735_);
lean_inc_ref(v_options_1734_);
lean_inc_ref(v_fileMap_1733_);
lean_inc_ref(v_fileName_1732_);
v___x_1752_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1752_, 0, v_fileName_1732_);
lean_ctor_set(v___x_1752_, 1, v_fileMap_1733_);
lean_ctor_set(v___x_1752_, 2, v_options_1734_);
lean_ctor_set(v___x_1752_, 3, v_currRecDepth_1735_);
lean_ctor_set(v___x_1752_, 4, v_maxRecDepth_1736_);
lean_ctor_set(v___x_1752_, 5, v_ref_1751_);
lean_ctor_set(v___x_1752_, 6, v_currNamespace_1738_);
lean_ctor_set(v___x_1752_, 7, v_openDecls_1739_);
lean_ctor_set(v___x_1752_, 8, v_initHeartbeats_1740_);
lean_ctor_set(v___x_1752_, 9, v_maxHeartbeats_1741_);
lean_ctor_set(v___x_1752_, 10, v_quotContext_1742_);
lean_ctor_set(v___x_1752_, 11, v_currMacroScope_1743_);
lean_ctor_set(v___x_1752_, 12, v_cancelTk_x3f_1745_);
lean_ctor_set(v___x_1752_, 13, v_inheritedTraceOptions_1747_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14, v_diag_1744_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14 + 1, v_suppressElabErrors_1746_);
v___x_1753_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1750_, v___f_1748_, v___y_1725_, v___y_1726_, v___x_1752_, v___y_1728_);
lean_dec_ref_known(v___x_1752_, 14);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1766_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1766_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1766_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_mk_empty_array_with_capacity(v___x_1758_);
v___x_1760_ = lean_array_push(v___x_1759_, v_a_1754_);
v___x_1761_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1762_);
v___x_1764_ = v___x_1756_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1753_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1753_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_args_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_termMeasure_x3f_1719_);
lean_inc_ref(v_fixedParamPerm_1720_);
v_args_1775_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1720_, v_xs_1721_, v_ys_1723_);
v___x_1776_ = lean_array_get_size(v_args_1775_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
v___x_1779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_1776_, v_fnName_1722_, v_fixedParamPerm_1720_, v_args_1775_, v___x_1777_, v___x_1778_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec_ref(v_args_1775_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1814_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1814_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1814_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_fst_1784_; lean_object* v_snd_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1813_; 
v_fst_1784_ = lean_ctor_get(v_a_1780_, 0);
v_snd_1785_ = lean_ctor_get(v_a_1780_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1780_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1787_ = v_a_1780_;
v_isShared_1788_ = v_isSharedCheck_1813_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_snd_1785_);
lean_inc(v_fst_1784_);
lean_dec(v_a_1780_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1813_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_options_1796_; uint8_t v_hasTrace_1797_; 
v_options_1796_ = lean_ctor_get(v___y_1727_, 2);
v_hasTrace_1797_ = lean_ctor_get_uint8(v_options_1796_, sizeof(void*)*1);
if (v_hasTrace_1797_ == 0)
{
goto v___jp_1789_;
}
else
{
lean_object* v_inheritedTraceOptions_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_inheritedTraceOptions_1798_ = lean_ctor_get(v___y_1727_, 13);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1800_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_1801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1798_, v_options_1796_, v___x_1800_);
if (v___x_1801_ == 0)
{
goto v___jp_1789_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14);
lean_inc(v_snd_1785_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v_snd_1785_);
v___x_1804_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_1799_, v___x_1803_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_dec_ref_known(v___x_1804_, 1);
goto v___jp_1789_;
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_del_object(v___x_1787_);
lean_dec(v_snd_1785_);
lean_dec(v_fst_1784_);
lean_del_object(v___x_1782_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
v___jp_1789_:
{
lean_object* v___x_1791_; 
if (v_isShared_1788_ == 0)
{
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_fst_1784_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_snd_1785_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1791_);
v___x_1793_ = v___x_1782_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1815_, lean_object* v_fixedParamPerm_1816_, lean_object* v_xs_1817_, lean_object* v_fnName_1818_, lean_object* v_ys_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1815_, v_fixedParamPerm_1816_, v_xs_1817_, v_fnName_1818_, v_ys_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_x_1820_);
lean_dec_ref(v_xs_1817_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1827_, lean_object* v_fixedParamPerm_1828_, lean_object* v_xs_1829_, lean_object* v_value_1830_, lean_object* v_termMeasure_x3f_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___f_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; 
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1837_, 0, v_termMeasure_x3f_1831_);
lean_closure_set(v___f_1837_, 1, v_fixedParamPerm_1828_);
lean_closure_set(v___f_1837_, 2, v_xs_1829_);
lean_closure_set(v___f_1837_, 3, v_fnName_1827_);
v___x_1838_ = 0;
v___x_1839_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1830_, v___f_1837_, v___x_1838_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1840_, lean_object* v_fixedParamPerm_1841_, lean_object* v_xs_1842_, lean_object* v_value_1843_, lean_object* v_termMeasure_x3f_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1840_, v_fixedParamPerm_1841_, v_xs_1842_, v_value_1843_, v_termMeasure_x3f_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(lean_object* v_upperBound_1851_, lean_object* v_fnName_1852_, lean_object* v_fixedParamPerm_1853_, lean_object* v_args_1854_, lean_object* v_inst_1855_, lean_object* v_R_1856_, lean_object* v_a_1857_, lean_object* v_b_1858_, lean_object* v_c_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v_upperBound_1851_, v_fnName_1852_, v_fixedParamPerm_1853_, v_args_1854_, v_a_1857_, v_b_1858_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(lean_object* v_upperBound_1866_, lean_object* v_fnName_1867_, lean_object* v_fixedParamPerm_1868_, lean_object* v_args_1869_, lean_object* v_inst_1870_, lean_object* v_R_1871_, lean_object* v_a_1872_, lean_object* v_b_1873_, lean_object* v_c_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v_upperBound_1866_, v_fnName_1867_, v_fixedParamPerm_1868_, v_args_1869_, v_inst_1870_, v_R_1871_, v_a_1872_, v_b_1873_, v_c_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v_args_1869_);
lean_dec(v_upperBound_1866_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
return v_x_1881_;
}
else
{
lean_object* v_key_1883_; lean_object* v_value_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1908_; 
v_key_1883_ = lean_ctor_get(v_x_1882_, 0);
v_value_1884_ = lean_ctor_get(v_x_1882_, 1);
v_tail_1885_ = lean_ctor_get(v_x_1882_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1887_ = v_x_1882_;
v_isShared_1888_ = v_isSharedCheck_1908_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_value_1884_);
lean_inc(v_key_1883_);
lean_dec(v_x_1882_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1908_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v_fold_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1889_ = lean_array_get_size(v_x_1881_);
v___x_1890_ = lean_uint64_of_nat(v_key_1883_);
v___x_1891_ = 32ULL;
v___x_1892_ = lean_uint64_shift_right(v___x_1890_, v___x_1891_);
v_fold_1893_ = lean_uint64_xor(v___x_1890_, v___x_1892_);
v___x_1894_ = 16ULL;
v___x_1895_ = lean_uint64_shift_right(v_fold_1893_, v___x_1894_);
v___x_1896_ = lean_uint64_xor(v_fold_1893_, v___x_1895_);
v___x_1897_ = lean_uint64_to_usize(v___x_1896_);
v___x_1898_ = lean_usize_of_nat(v___x_1889_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_sub(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_usize_land(v___x_1897_, v___x_1900_);
v___x_1902_ = lean_array_uget_borrowed(v_x_1881_, v___x_1901_);
lean_inc(v___x_1902_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 2, v___x_1902_);
v___x_1904_ = v___x_1887_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_key_1883_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_value_1884_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_array_uset(v_x_1881_, v___x_1901_, v___x_1904_);
v_x_1881_ = v___x_1905_;
v_x_1882_ = v_tail_1885_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1909_, lean_object* v_source_1910_, lean_object* v_target_1911_){
_start:
{
lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = lean_array_get_size(v_source_1910_);
v___x_1913_ = lean_nat_dec_lt(v_i_1909_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_dec_ref(v_source_1910_);
lean_dec(v_i_1909_);
return v_target_1911_;
}
else
{
lean_object* v_es_1914_; lean_object* v___x_1915_; lean_object* v_source_1916_; lean_object* v_target_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_es_1914_ = lean_array_fget(v_source_1910_, v_i_1909_);
v___x_1915_ = lean_box(0);
v_source_1916_ = lean_array_fset(v_source_1910_, v_i_1909_, v___x_1915_);
v_target_1917_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1911_, v_es_1914_);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_add(v_i_1909_, v___x_1918_);
lean_dec(v_i_1909_);
v_i_1909_ = v___x_1919_;
v_source_1910_ = v_source_1916_;
v_target_1911_ = v_target_1917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_nbuckets_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1922_ = lean_array_get_size(v_data_1921_);
v___x_1923_ = lean_unsigned_to_nat(2u);
v_nbuckets_1924_ = lean_nat_mul(v___x_1922_, v___x_1923_);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_mk_array(v_nbuckets_1924_, v___x_1926_);
v___x_1928_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1925_, v_data_1921_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1929_, lean_object* v_x_1930_){
_start:
{
if (lean_obj_tag(v_x_1930_) == 0)
{
uint8_t v___x_1931_; 
v___x_1931_ = 0;
return v___x_1931_;
}
else
{
lean_object* v_key_1932_; lean_object* v_tail_1933_; uint8_t v___x_1934_; 
v_key_1932_ = lean_ctor_get(v_x_1930_, 0);
v_tail_1933_ = lean_ctor_get(v_x_1930_, 2);
v___x_1934_ = lean_nat_dec_eq(v_key_1932_, v_a_1929_);
if (v___x_1934_ == 0)
{
v_x_1930_ = v_tail_1933_;
goto _start;
}
else
{
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1936_, lean_object* v_x_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1936_, v_x_1937_);
lean_dec(v_x_1937_);
lean_dec(v_a_1936_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1940_, lean_object* v_a_1941_, lean_object* v_b_1942_){
_start:
{
lean_object* v_size_1943_; lean_object* v_buckets_1944_; lean_object* v___x_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; uint64_t v_fold_1949_; uint64_t v___x_1950_; uint64_t v___x_1951_; uint64_t v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; lean_object* v_bkt_1958_; uint8_t v___x_1959_; 
v_size_1943_ = lean_ctor_get(v_m_1940_, 0);
v_buckets_1944_ = lean_ctor_get(v_m_1940_, 1);
v___x_1945_ = lean_array_get_size(v_buckets_1944_);
v___x_1946_ = lean_uint64_of_nat(v_a_1941_);
v___x_1947_ = 32ULL;
v___x_1948_ = lean_uint64_shift_right(v___x_1946_, v___x_1947_);
v_fold_1949_ = lean_uint64_xor(v___x_1946_, v___x_1948_);
v___x_1950_ = 16ULL;
v___x_1951_ = lean_uint64_shift_right(v_fold_1949_, v___x_1950_);
v___x_1952_ = lean_uint64_xor(v_fold_1949_, v___x_1951_);
v___x_1953_ = lean_uint64_to_usize(v___x_1952_);
v___x_1954_ = lean_usize_of_nat(v___x_1945_);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_sub(v___x_1954_, v___x_1955_);
v___x_1957_ = lean_usize_land(v___x_1953_, v___x_1956_);
v_bkt_1958_ = lean_array_uget_borrowed(v_buckets_1944_, v___x_1957_);
v___x_1959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1941_, v_bkt_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1980_; 
lean_inc_ref(v_buckets_1944_);
lean_inc(v_size_1943_);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_m_1940_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1981_ = lean_ctor_get(v_m_1940_, 1);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_m_1940_, 0);
lean_dec(v_unused_1982_);
v___x_1961_ = v_m_1940_;
v_isShared_1962_ = v_isSharedCheck_1980_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v_m_1940_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1980_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v_size_x27_1964_; lean_object* v___x_1965_; lean_object* v_buckets_x27_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
v_size_x27_1964_ = lean_nat_add(v_size_1943_, v___x_1963_);
lean_dec(v_size_1943_);
lean_inc(v_bkt_1958_);
v___x_1965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1965_, 0, v_a_1941_);
lean_ctor_set(v___x_1965_, 1, v_b_1942_);
lean_ctor_set(v___x_1965_, 2, v_bkt_1958_);
v_buckets_x27_1966_ = lean_array_uset(v_buckets_1944_, v___x_1957_, v___x_1965_);
v___x_1967_ = lean_unsigned_to_nat(4u);
v___x_1968_ = lean_nat_mul(v_size_x27_1964_, v___x_1967_);
v___x_1969_ = lean_unsigned_to_nat(3u);
v___x_1970_ = lean_nat_div(v___x_1968_, v___x_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_array_get_size(v_buckets_x27_1966_);
v___x_1972_ = lean_nat_dec_le(v___x_1970_, v___x_1971_);
lean_dec(v___x_1970_);
if (v___x_1972_ == 0)
{
lean_object* v_val_1973_; lean_object* v___x_1975_; 
v_val_1973_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1966_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 1, v_val_1973_);
lean_ctor_set(v___x_1961_, 0, v_size_x27_1964_);
v___x_1975_ = v___x_1961_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_size_x27_1964_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_val_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
else
{
lean_object* v___x_1978_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 1, v_buckets_x27_1966_);
lean_ctor_set(v___x_1961_, 0, v_size_x27_1964_);
v___x_1978_ = v___x_1961_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_size_x27_1964_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_buckets_x27_1966_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_dec(v_b_1942_);
lean_dec(v_a_1941_);
return v_m_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_1983_, size_t v_sz_1984_, size_t v_i_1985_, lean_object* v_b_1986_){
_start:
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_usize_dec_lt(v_i_1985_, v_sz_1984_);
if (v___x_1987_ == 0)
{
return v_b_1986_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; 
v_a_1988_ = lean_array_uget_borrowed(v_as_1983_, v_i_1985_);
v___x_1989_ = lean_box(0);
lean_inc(v_a_1988_);
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_1986_, v_a_1988_, v___x_1989_);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_i_1985_, v___x_1991_);
v_i_1985_ = v___x_1992_;
v_b_1986_ = v___x_1990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_1994_, lean_object* v_sz_1995_, lean_object* v_i_1996_, lean_object* v_b_1997_){
_start:
{
size_t v_sz_boxed_1998_; size_t v_i_boxed_1999_; lean_object* v_res_2000_; 
v_sz_boxed_1998_ = lean_unbox_usize(v_sz_1995_);
lean_dec(v_sz_1995_);
v_i_boxed_1999_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_1994_, v_sz_boxed_1998_, v_i_boxed_1999_, v_b_1997_);
lean_dec_ref(v_as_1994_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_b_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2005_ == 0)
{
return v_b_2004_;
}
else
{
lean_object* v_a_2006_; lean_object* v_indicesPos_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; 
v_a_2006_ = lean_array_uget_borrowed(v_as_2001_, v_i_2003_);
v_indicesPos_2007_ = lean_ctor_get(v_a_2006_, 3);
v_sz_2008_ = lean_array_size(v_indicesPos_2007_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2007_, v_sz_2008_, v___x_2009_, v_b_2004_);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2003_, v___x_2011_);
v_i_2003_ = v___x_2012_;
v_b_2004_ = v___x_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2014_, lean_object* v_sz_2015_, lean_object* v_i_2016_, lean_object* v_b_2017_){
_start:
{
size_t v_sz_boxed_2018_; size_t v_i_boxed_2019_; lean_object* v_res_2020_; 
v_sz_boxed_2018_ = lean_unbox_usize(v_sz_2015_);
lean_dec(v_sz_2015_);
v_i_boxed_2019_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2014_, v_sz_boxed_2018_, v_i_boxed_2019_, v_b_2017_);
lean_dec_ref(v_as_2014_);
return v_res_2020_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_buckets_2023_; lean_object* v___x_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; uint64_t v_fold_2028_; uint64_t v___x_2029_; uint64_t v___x_2030_; uint64_t v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v_buckets_2023_ = lean_ctor_get(v_m_2021_, 1);
v___x_2024_ = lean_array_get_size(v_buckets_2023_);
v___x_2025_ = lean_uint64_of_nat(v_a_2022_);
v___x_2026_ = 32ULL;
v___x_2027_ = lean_uint64_shift_right(v___x_2025_, v___x_2026_);
v_fold_2028_ = lean_uint64_xor(v___x_2025_, v___x_2027_);
v___x_2029_ = 16ULL;
v___x_2030_ = lean_uint64_shift_right(v_fold_2028_, v___x_2029_);
v___x_2031_ = lean_uint64_xor(v_fold_2028_, v___x_2030_);
v___x_2032_ = lean_uint64_to_usize(v___x_2031_);
v___x_2033_ = lean_usize_of_nat(v___x_2024_);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_sub(v___x_2033_, v___x_2034_);
v___x_2036_ = lean_usize_land(v___x_2032_, v___x_2035_);
v___x_2037_ = lean_array_uget_borrowed(v_buckets_2023_, v___x_2036_);
v___x_2038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2022_, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2039_, lean_object* v_a_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_m_2039_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2043_, lean_object* v_as_2044_, size_t v_sz_2045_, size_t v_i_2046_, lean_object* v_b_2047_){
_start:
{
lean_object* v_a_2049_; uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_lt(v_i_2046_, v_sz_2045_);
if (v___x_2053_ == 0)
{
return v_b_2047_;
}
else
{
lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2070_; 
v_fst_2054_ = lean_ctor_get(v_b_2047_, 0);
v_snd_2055_ = lean_ctor_get(v_b_2047_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_b_2047_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2057_ = v_b_2047_;
v_isShared_2058_ = v_isSharedCheck_2070_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
lean_dec(v_b_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2070_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_a_2059_; lean_object* v_recArgPos_2060_; uint8_t v___x_2061_; 
v_a_2059_ = lean_array_uget_borrowed(v_as_2044_, v_i_2046_);
v_recArgPos_2060_ = lean_ctor_get(v_a_2059_, 2);
v___x_2061_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2043_, v_recArgPos_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_inc(v_a_2059_);
v___x_2062_ = lean_array_push(v_snd_2055_, v_a_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2062_);
v___x_2064_ = v___x_2057_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_fst_2054_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_a_2049_ = v___x_2064_;
goto v___jp_2048_;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_inc(v_a_2059_);
v___x_2066_ = lean_array_push(v_fst_2054_, v_a_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2066_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_snd_2055_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v_a_2049_ = v___x_2068_;
goto v___jp_2048_;
}
}
}
}
v___jp_2048_:
{
size_t v___x_2050_; size_t v___x_2051_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2046_, v___x_2050_);
v_i_2046_ = v___x_2051_;
v_b_2047_ = v_a_2049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2071_, lean_object* v_as_2072_, lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_b_2075_){
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2071_, v_as_2072_, v_sz_boxed_2076_, v_i_boxed_2077_, v_b_2075_);
lean_dec_ref(v_as_2072_);
lean_dec_ref(v___x_2071_);
return v_res_2078_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_unsigned_to_nat(16u);
v___x_2081_ = lean_mk_array(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_indicesPos_2084_; 
v___x_2082_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2083_ = lean_unsigned_to_nat(0u);
v_indicesPos_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2084_, 0, v___x_2083_);
lean_ctor_set(v_indicesPos_2084_, 1, v___x_2082_);
return v_indicesPos_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2087_){
_start:
{
lean_object* v_indicesPos_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_fst_2094_; lean_object* v_snd_2095_; lean_object* v___x_2096_; 
v_indicesPos_2088_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2089_ = lean_array_size(v_recArgInfos_2087_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2087_, v_sz_2089_, v___x_2090_, v_indicesPos_2088_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Structural_nonIndicesFirst___closed__2));
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2091_, v_recArgInfos_2087_, v_sz_2089_, v___x_2090_, v___x_2092_);
lean_dec_ref(v___x_2091_);
v_fst_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_fst_2094_);
v_snd_2095_ = lean_ctor_get(v___x_2093_, 1);
lean_inc(v_snd_2095_);
lean_dec_ref(v___x_2093_);
v___x_2096_ = l_Array_append___redArg(v_snd_2095_, v_fst_2094_);
lean_dec(v_fst_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2097_);
lean_dec_ref(v_recArgInfos_2097_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2099_, lean_object* v_m_2100_, lean_object* v_a_2101_, lean_object* v_b_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2100_, v_a_2101_, v_b_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2104_, lean_object* v_m_2105_, lean_object* v_a_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2105_, v_a_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2108_, lean_object* v_m_2109_, lean_object* v_a_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2108_, v_m_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_m_2109_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2113_, lean_object* v_a_2114_, lean_object* v_x_2115_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2114_, v_x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2117_, lean_object* v_a_2118_, lean_object* v_x_2119_){
_start:
{
uint8_t v_res_2120_; lean_object* v_r_2121_; 
v_res_2120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2117_, v_a_2118_, v_x_2119_);
lean_dec(v_x_2119_);
lean_dec(v_a_2118_);
v_r_2121_ = lean_box(v_res_2120_);
return v_r_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2122_, lean_object* v_data_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2125_, lean_object* v_i_2126_, lean_object* v_source_2127_, lean_object* v_target_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2126_, v_source_2127_, v_target_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2134_, lean_object* v_a_2135_, lean_object* v_toPure_2136_, uint8_t v_____do__lift_2137_){
_start:
{
if (v_____do__lift_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_array_push(v___y_2134_, v_a_2135_);
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
v___x_2140_ = lean_apply_2(v_toPure_2136_, lean_box(0), v___x_2139_);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_a_2135_);
v___x_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2134_);
v___x_2142_ = lean_apply_2(v_toPure_2136_, lean_box(0), v___x_2141_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2143_, lean_object* v_a_2144_, lean_object* v_toPure_2145_, lean_object* v_____do__lift_2146_){
_start:
{
uint8_t v_____do__lift_159__boxed_2147_; lean_object* v_res_2148_; 
v_____do__lift_159__boxed_2147_ = lean_unbox(v_____do__lift_2146_);
v_res_2148_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2143_, v_a_2144_, v_toPure_2145_, v_____do__lift_159__boxed_2147_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2149_, lean_object* v_a_2150_, lean_object* v_x_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_apply_2(v_eq_2149_, v_x_2151_, v_a_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2153_, lean_object* v___x_2154_, lean_object* v_toBind_2155_, lean_object* v_eq_2156_, lean_object* v_inst_2157_, lean_object* v_a_2158_, lean_object* v_x_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___f_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
lean_inc(v_toPure_2153_);
lean_inc(v_a_2158_);
lean_inc_ref(v___y_2160_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2161_, 0, v___y_2160_);
lean_closure_set(v___f_2161_, 1, v_a_2158_);
lean_closure_set(v___f_2161_, 2, v_toPure_2153_);
v___x_2162_ = lean_array_get_size(v___y_2160_);
v___x_2163_ = lean_nat_dec_lt(v___x_2154_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec_ref(v___y_2160_);
lean_dec(v_a_2158_);
lean_dec_ref(v_inst_2157_);
lean_dec(v_eq_2156_);
v___x_2164_ = lean_box(v___x_2163_);
v___x_2165_ = lean_apply_2(v_toPure_2153_, lean_box(0), v___x_2164_);
v___x_2166_ = lean_apply_4(v_toBind_2155_, lean_box(0), lean_box(0), v___x_2165_, v___f_2161_);
return v___x_2166_;
}
else
{
if (v___x_2163_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec_ref(v___y_2160_);
lean_dec(v_a_2158_);
lean_dec_ref(v_inst_2157_);
lean_dec(v_eq_2156_);
v___x_2167_ = lean_box(v___x_2163_);
v___x_2168_ = lean_apply_2(v_toPure_2153_, lean_box(0), v___x_2167_);
v___x_2169_ = lean_apply_4(v_toBind_2155_, lean_box(0), lean_box(0), v___x_2168_, v___f_2161_);
return v___x_2169_;
}
else
{
lean_object* v___f_2170_; size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec(v_toPure_2153_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2170_, 0, v_eq_2156_);
lean_closure_set(v___f_2170_, 1, v_a_2158_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2162_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2157_, v___f_2170_, v___y_2160_, v___x_2171_, v___x_2172_);
v___x_2174_ = lean_apply_4(v_toBind_2155_, lean_box(0), lean_box(0), v___x_2173_, v___f_2161_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2175_, lean_object* v___x_2176_, lean_object* v_toBind_2177_, lean_object* v_eq_2178_, lean_object* v_inst_2179_, lean_object* v_a_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2175_, v___x_2176_, v_toBind_2177_, v_eq_2178_, v_inst_2179_, v_a_2180_, v_x_2181_, v___y_2182_);
lean_dec(v___x_2176_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2184_, lean_object* v_____s_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_apply_2(v_toPure_2184_, lean_box(0), v_____s_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2189_, lean_object* v_eq_2190_, lean_object* v_xs_2191_){
_start:
{
lean_object* v_toApplicative_2192_; lean_object* v_toBind_2193_; lean_object* v_toPure_2194_; lean_object* v___x_2195_; lean_object* v_ret_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_toApplicative_2192_ = lean_ctor_get(v_inst_2189_, 0);
v_toBind_2193_ = lean_ctor_get(v_inst_2189_, 1);
lean_inc_n(v_toBind_2193_, 2);
v_toPure_2194_ = lean_ctor_get(v_toApplicative_2192_, 1);
v___x_2195_ = lean_unsigned_to_nat(0u);
v_ret_2196_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2189_);
lean_inc_n(v_toPure_2194_, 2);
v___f_2197_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2197_, 0, v_toPure_2194_);
lean_closure_set(v___f_2197_, 1, v___x_2195_);
lean_closure_set(v___f_2197_, 2, v_toBind_2193_);
lean_closure_set(v___f_2197_, 3, v_eq_2190_);
lean_closure_set(v___f_2197_, 4, v_inst_2189_);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2198_, 0, v_toPure_2194_);
v_sz_2199_ = lean_array_size(v_xs_2191_);
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2189_, v_xs_2191_, v___f_2197_, v_sz_2199_, v___x_2200_, v_ret_2196_);
v___x_2202_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2201_, v___f_2198_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2203_, lean_object* v_00_u03b1_2204_, lean_object* v_inst_2205_, lean_object* v_eq_2206_, lean_object* v_xs_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2205_, v_eq_2206_, v_xs_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2209_, size_t v_i_2210_, lean_object* v_bs_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_usize_dec_lt(v_i_2210_, v_sz_2209_);
if (v___x_2212_ == 0)
{
return v_bs_2211_;
}
else
{
lean_object* v_v_2213_; lean_object* v_indGroupInst_2214_; lean_object* v___x_2215_; lean_object* v_bs_x27_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_v_2213_ = lean_array_uget_borrowed(v_bs_2211_, v_i_2210_);
v_indGroupInst_2214_ = lean_ctor_get(v_v_2213_, 4);
lean_inc_ref(v_indGroupInst_2214_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v_bs_x27_2216_ = lean_array_uset(v_bs_2211_, v_i_2210_, v___x_2215_);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2210_, v___x_2217_);
v___x_2219_ = lean_array_uset(v_bs_x27_2216_, v_i_2210_, v_indGroupInst_2214_);
v_i_2210_ = v___x_2218_;
v_bs_2211_ = v___x_2219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_bs_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2224_, v_i_boxed_2225_, v_bs_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2227_, lean_object* v_a_2228_, lean_object* v_as_2229_, size_t v_i_2230_, size_t v_stop_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_usize_dec_eq(v_i_2230_, v_stop_2231_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_array_uget_borrowed(v_as_2229_, v_i_2230_);
lean_inc_ref(v_eq_2227_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v_a_2228_);
lean_inc(v___x_2238_);
v___x_2239_ = lean_apply_7(v_eq_2227_, v___x_2238_, v_a_2228_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, lean_box(0));
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2251_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2251_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2251_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_unbox(v_a_2240_);
if (v___x_2244_ == 0)
{
size_t v___x_2245_; size_t v___x_2246_; 
lean_del_object(v___x_2242_);
lean_dec(v_a_2240_);
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2230_, v___x_2245_);
v_i_2230_ = v___x_2246_;
goto _start;
}
else
{
lean_object* v___x_2249_; 
lean_dec(v_a_2228_);
lean_dec_ref(v_eq_2227_);
if (v_isShared_2243_ == 0)
{
v___x_2249_ = v___x_2242_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2240_);
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
lean_dec(v_a_2228_);
lean_dec_ref(v_eq_2227_);
return v___x_2239_;
}
}
else
{
uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec(v_a_2228_);
lean_dec_ref(v_eq_2227_);
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
uint8_t v_____do__lift_1269__boxed_2289_; lean_object* v_res_2290_; 
v_____do__lift_1269__boxed_2289_ = lean_unbox(v_____do__lift_2283_);
v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2281_, v_a_2282_, v_____do__lift_1269__boxed_2289_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
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
lean_object* v_a_2302_; lean_object* v___y_2307_; uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec_ref(v_eq_2291_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_b_2295_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2328_ = lean_unsigned_to_nat(0u);
v_a_2329_ = lean_array_uget_borrowed(v_as_2292_, v_i_2294_);
v___x_2330_ = lean_array_get_size(v_b_2295_);
v___x_2331_ = lean_nat_dec_lt(v___x_2328_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_inc(v_a_2329_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2295_, v_a_2329_, v___x_2331_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
v___y_2307_ = v___x_2332_;
goto v___jp_2306_;
}
else
{
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; 
lean_inc(v_a_2329_);
v___x_2333_ = lean_array_push(v_b_2295_, v_a_2329_);
v_a_2302_ = v___x_2333_;
goto v___jp_2301_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2330_);
lean_inc(v_a_2329_);
lean_inc_ref(v_eq_2291_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2291_, v_a_2329_, v_b_2295_, v___x_2334_, v___x_2335_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = lean_unbox(v_a_2337_);
lean_dec(v_a_2337_);
lean_inc(v_a_2329_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2295_, v_a_2329_, v___x_2338_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
v___y_2307_ = v___x_2339_;
goto v___jp_2306_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_b_2295_);
lean_dec_ref(v_eq_2291_);
v_a_2340_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2336_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
v___jp_2301_:
{
size_t v___x_2303_; size_t v___x_2304_; 
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = lean_usize_add(v_i_2294_, v___x_2303_);
v_i_2294_ = v___x_2304_;
v_b_2295_ = v_a_2302_;
goto _start;
}
v___jp_2306_:
{
if (lean_obj_tag(v___y_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2317_; 
v_a_2308_ = lean_ctor_get(v___y_2307_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___y_2307_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2310_ = v___y_2307_;
v_isShared_2311_ = v_isSharedCheck_2317_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___y_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2317_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
if (lean_obj_tag(v_a_2308_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; 
lean_dec_ref(v_eq_2291_);
v_a_2312_ = lean_ctor_get(v_a_2308_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v_a_2308_, 1);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v_a_2312_);
v___x_2314_ = v___x_2310_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
else
{
lean_object* v_a_2316_; 
lean_del_object(v___x_2310_);
v_a_2316_ = lean_ctor_get(v_a_2308_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v_a_2308_, 1);
v_a_2302_ = v_a_2316_;
goto v___jp_2301_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_eq_2291_);
v_a_2318_ = lean_ctor_get(v___y_2307_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___y_2307_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___y_2307_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___y_2307_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2348_, lean_object* v_as_2349_, lean_object* v_sz_2350_, lean_object* v_i_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
size_t v_sz_boxed_2358_; size_t v_i_boxed_2359_; lean_object* v_res_2360_; 
v_sz_boxed_2358_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2359_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2348_, v_as_2349_, v_sz_boxed_2358_, v_i_boxed_2359_, v_b_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v_as_2349_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2361_, lean_object* v_xs_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_ret_2368_; size_t v_sz_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v_ret_2368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2369_ = lean_array_size(v_xs_2362_);
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2361_, v_xs_2362_, v_sz_2369_, v___x_2370_, v_ret_2368_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2372_, lean_object* v_xs_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2372_, v_xs_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_xs_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; size_t v_sz_2388_; size_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2387_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2388_ = lean_array_size(v_recArgInfos_2381_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2388_, v___x_2389_, v_recArgInfos_2381_);
v___x_2391_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2387_, v___x_2390_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec_ref(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2399_, lean_object* v_eq_2400_, lean_object* v_xs_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2400_, v_xs_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2408_, lean_object* v_eq_2409_, lean_object* v_xs_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2408_, v_eq_2409_, v_xs_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v_xs_2410_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2417_, lean_object* v_eq_2418_, lean_object* v_a_2419_, lean_object* v_as_2420_, size_t v_i_2421_, size_t v_stop_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2418_, v_a_2419_, v_as_2420_, v_i_2421_, v_stop_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_eq_2430_, lean_object* v_a_2431_, lean_object* v_as_2432_, lean_object* v_i_2433_, lean_object* v_stop_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
size_t v_i_boxed_2440_; size_t v_stop_boxed_2441_; lean_object* v_res_2442_; 
v_i_boxed_2440_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_stop_boxed_2441_ = lean_unbox_usize(v_stop_2434_);
lean_dec(v_stop_2434_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2429_, v_eq_2430_, v_a_2431_, v_as_2432_, v_i_boxed_2440_, v_stop_boxed_2441_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_as_2432_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2443_, lean_object* v_eq_2444_, lean_object* v_as_2445_, size_t v_sz_2446_, size_t v_i_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2444_, v_as_2445_, v_sz_2446_, v_i_2447_, v_b_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_eq_2456_, lean_object* v_as_2457_, lean_object* v_sz_2458_, lean_object* v_i_2459_, lean_object* v_b_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2458_);
lean_dec(v_sz_2458_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2455_, v_eq_2456_, v_as_2457_, v_sz_boxed_2466_, v_i_boxed_2467_, v_b_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_as_2457_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2469_, lean_object* v___y_2470_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Lean_Expr_hasMVar(v_e_2469_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_e_2469_);
return v___x_2473_;
}
else
{
lean_object* v___x_2474_; lean_object* v_mctx_2475_; lean_object* v___x_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; lean_object* v_cache_2480_; lean_object* v_zetaDeltaFVarIds_2481_; lean_object* v_postponed_2482_; lean_object* v_diag_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2492_; 
v___x_2474_ = lean_st_ref_get(v___y_2470_);
v_mctx_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc_ref(v_mctx_2475_);
lean_dec(v___x_2474_);
v___x_2476_ = l_Lean_instantiateMVarsCore(v_mctx_2475_, v_e_2469_);
v_fst_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_fst_2477_);
v_snd_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2476_);
v___x_2479_ = lean_st_ref_take(v___y_2470_);
v_cache_2480_ = lean_ctor_get(v___x_2479_, 1);
v_zetaDeltaFVarIds_2481_ = lean_ctor_get(v___x_2479_, 2);
v_postponed_2482_ = lean_ctor_get(v___x_2479_, 3);
v_diag_2483_ = lean_ctor_get(v___x_2479_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2479_, 0);
lean_dec(v_unused_2493_);
v___x_2485_ = v___x_2479_;
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_diag_2483_);
lean_inc(v_postponed_2482_);
lean_inc(v_zetaDeltaFVarIds_2481_);
lean_inc(v_cache_2480_);
lean_dec(v___x_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2492_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v_snd_2478_);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_snd_2478_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_cache_2480_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_zetaDeltaFVarIds_2481_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_postponed_2482_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_diag_2483_);
v___x_2488_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_st_ref_put(v___y_2470_, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_fst_2477_);
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2494_, v___y_2495_);
lean_dec(v___y_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2498_, v___y_2500_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__2));
v___x_2514_ = lean_unsigned_to_nat(109u);
v___x_2515_ = lean_unsigned_to_nat(216u);
v___x_2516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_2518_ = l_mkPanicMessageWithDecl(v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_, v___x_2513_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2519_, size_t v_sz_2520_, size_t v_i_2521_, lean_object* v_bs_2522_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_lt(v_i_2521_, v_sz_2520_);
if (v___x_2523_ == 0)
{
return v_bs_2522_;
}
else
{
lean_object* v_v_2524_; lean_object* v___x_2525_; lean_object* v_bs_x27_2526_; lean_object* v___y_2528_; lean_object* v___x_2533_; 
v_v_2524_ = lean_array_uget(v_bs_2522_, v_i_2521_);
v___x_2525_ = lean_unsigned_to_nat(0u);
v_bs_x27_2526_ = lean_array_uset(v_bs_2522_, v_i_2521_, v___x_2525_);
v___x_2533_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2519_, v_v_2524_);
lean_dec(v_v_2524_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2535_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2534_);
v___y_2528_ = v___x_2535_;
goto v___jp_2527_;
}
else
{
lean_object* v_val_2536_; 
v_val_2536_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v___x_2533_, 1);
v___y_2528_ = v_val_2536_;
goto v___jp_2527_;
}
v___jp_2527_:
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = lean_usize_add(v_i_2521_, v___x_2529_);
v___x_2531_ = lean_array_uset(v_bs_x27_2526_, v_i_2521_, v___y_2528_);
v_i_2521_ = v___x_2530_;
v_bs_2522_ = v___x_2531_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2537_, lean_object* v_sz_2538_, lean_object* v_i_2539_, lean_object* v_bs_2540_){
_start:
{
size_t v_sz_boxed_2541_; size_t v_i_boxed_2542_; lean_object* v_res_2543_; 
v_sz_boxed_2541_ = lean_unbox_usize(v_sz_2538_);
lean_dec(v_sz_2538_);
v_i_boxed_2542_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2537_, v_sz_boxed_2541_, v_i_boxed_2542_, v_bs_2540_);
lean_dec_ref(v___x_2537_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2544_, size_t v_i_2545_, lean_object* v_bs_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_usize_dec_lt(v_i_2545_, v_sz_2544_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_bs_2546_);
return v___x_2553_;
}
else
{
lean_object* v_v_2554_; lean_object* v___x_2555_; 
v_v_2554_ = lean_array_uget_borrowed(v_bs_2546_, v_i_2545_);
lean_inc(v_v_2554_);
v___x_2555_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2554_, v___y_2548_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v_bs_x27_2558_; size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unsigned_to_nat(0u);
v_bs_x27_2558_ = lean_array_uset(v_bs_2546_, v_i_2545_, v___x_2557_);
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_add(v_i_2545_, v___x_2559_);
v___x_2561_ = lean_array_uset(v_bs_x27_2558_, v_i_2545_, v_a_2556_);
v_i_2545_ = v___x_2560_;
v_bs_2546_ = v___x_2561_;
goto _start;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_bs_2546_);
v_a_2563_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2555_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2555_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2571_, lean_object* v_i_2572_, lean_object* v_bs_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
size_t v_sz_boxed_2579_; size_t v_i_boxed_2580_; lean_object* v_res_2581_; 
v_sz_boxed_2579_ = lean_unbox_usize(v_sz_2571_);
lean_dec(v_sz_2571_);
v_i_boxed_2580_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_res_2581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2579_, v_i_boxed_2580_, v_bs_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2581_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2582_, lean_object* v___x_2583_, lean_object* v_as_2584_, size_t v_i_2585_, size_t v_stop_2586_){
_start:
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_usize_dec_eq(v_i_2585_, v_stop_2586_);
if (v___x_2587_ == 0)
{
uint8_t v___x_2588_; uint8_t v___y_2590_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2588_ = 1;
v___x_2594_ = lean_array_uget_borrowed(v_as_2584_, v_i_2585_);
v___x_2595_ = l_Lean_Expr_isFVar(v___x_2594_);
if (v___x_2595_ == 0)
{
v___y_2590_ = v_a_2582_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_nat_dec_eq(v___x_2583_, v___x_2596_);
v___y_2590_ = v___x_2597_;
goto v___jp_2589_;
}
v___jp_2589_:
{
if (v___y_2590_ == 0)
{
size_t v___x_2591_; size_t v___x_2592_; 
v___x_2591_ = ((size_t)1ULL);
v___x_2592_ = lean_usize_add(v_i_2585_, v___x_2591_);
v_i_2585_ = v___x_2592_;
goto _start;
}
else
{
return v___x_2588_;
}
}
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = 0;
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2599_, lean_object* v___x_2600_, lean_object* v_as_2601_, lean_object* v_i_2602_, lean_object* v_stop_2603_){
_start:
{
uint8_t v_a_7782__boxed_2604_; size_t v_i_boxed_2605_; size_t v_stop_boxed_2606_; uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_a_7782__boxed_2604_ = lean_unbox(v_a_2599_);
v_i_boxed_2605_ = lean_unbox_usize(v_i_2602_);
lean_dec(v_i_2602_);
v_stop_boxed_2606_ = lean_unbox_usize(v_stop_2603_);
lean_dec(v_stop_2603_);
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_7782__boxed_2604_, v___x_2600_, v_as_2601_, v_i_boxed_2605_, v_stop_boxed_2606_);
lean_dec_ref(v_as_2601_);
lean_dec(v___x_2600_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2609_, lean_object* v_ys_2610_, lean_object* v___x_2611_, lean_object* v_recArgInfo_2612_, lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v_group_2615_, lean_object* v___x_2616_, lean_object* v_as_2617_, size_t v_sz_2618_, size_t v_i_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_a_2627_; uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_lt(v_i_2619_, v_sz_2618_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_b_2620_);
return v___x_2632_;
}
else
{
lean_object* v_snd_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2789_; 
v_snd_2633_ = lean_ctor_get(v_b_2620_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_b_2620_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_b_2620_, 0);
lean_dec(v_unused_2790_);
v___x_2635_ = v_b_2620_;
v_isShared_2636_ = v_isSharedCheck_2789_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_snd_2633_);
lean_dec(v_b_2620_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2789_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_next_2637_; lean_object* v_upperBound_2638_; lean_object* v___x_2639_; 
v_next_2637_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc(v_next_2637_);
v_upperBound_2638_ = lean_ctor_get(v_snd_2633_, 1);
v___x_2639_ = lean_box(0);
if (lean_obj_tag(v_next_2637_) == 0)
{
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
goto v___jp_2640_;
}
else
{
lean_object* v_val_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2788_; 
v_val_2645_ = lean_ctor_get(v_next_2637_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_next_2637_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2647_ = v_next_2637_;
v_isShared_2648_ = v_isSharedCheck_2788_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_val_2645_);
lean_dec(v_next_2637_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2788_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_nat_dec_lt(v_val_2645_, v_upperBound_2638_);
if (v___x_2649_ == 0)
{
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
goto v___jp_2640_;
}
else
{
lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2785_; 
lean_inc(v_upperBound_2638_);
lean_del_object(v___x_2635_);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_snd_2633_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; lean_object* v_unused_2787_; 
v_unused_2786_ = lean_ctor_get(v_snd_2633_, 1);
lean_dec(v_unused_2786_);
v_unused_2787_ = lean_ctor_get(v_snd_2633_, 0);
lean_dec(v_unused_2787_);
v___x_2651_ = v_snd_2633_;
v_isShared_2652_ = v_isSharedCheck_2785_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v_snd_2633_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2785_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; 
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc_ref(v___y_2621_);
lean_inc_ref(v___x_2609_);
v___x_2653_ = lean_infer_type(v___x_2609_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = l_Lean_Meta_whnfD(v_a_2654_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_a_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v_a_2657_ = lean_array_uget_borrowed(v_as_2617_, v_i_2619_);
v___x_2658_ = 0;
lean_inc(v_a_2657_);
v___x_2659_ = l_Lean_Meta_forallMetaTelescope(v_a_2657_, v___x_2658_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_snd_2661_; lean_object* v_fst_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2760_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v_snd_2661_ = lean_ctor_get(v_a_2660_, 1);
v_fst_2662_ = lean_ctor_get(v_a_2660_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2664_ = v_a_2660_;
v_isShared_2665_ = v_isSharedCheck_2760_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2661_);
lean_inc(v_fst_2662_);
lean_dec(v_a_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2760_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2758_; 
v_snd_2666_ = lean_ctor_get(v_snd_2661_, 1);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_snd_2661_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v_snd_2661_, 0);
lean_dec(v_unused_2759_);
v___x_2668_ = v_snd_2661_;
v_isShared_2669_ = v_isSharedCheck_2758_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_dec(v_snd_2661_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2758_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2666_, v_a_2656_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_val_2645_, v___x_2672_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2673_);
v___x_2675_ = v___x_2647_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2675_);
v___x_2677_ = v___x_2651_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_upperBound_2638_);
v___x_2677_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_unbox(v_a_2671_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2680_; 
lean_dec(v_a_2671_);
lean_del_object(v___x_2664_);
lean_dec(v_fst_2662_);
lean_dec(v_val_2645_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2677_);
lean_ctor_set(v___x_2668_, 0, v___x_2639_);
v___x_2680_ = v___x_2668_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2677_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v_a_2627_ = v___x_2680_;
goto v___jp_2626_;
}
}
else
{
size_t v_sz_2682_; size_t v___x_2683_; lean_object* v___x_2684_; 
v_sz_2682_ = lean_array_size(v_fst_2662_);
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2682_, v___x_2683_, v_fst_2662_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_array_get_size(v_a_2685_);
v___x_2733_ = lean_nat_dec_lt(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v_a_2671_);
lean_del_object(v___x_2664_);
goto v___jp_2686_;
}
else
{
if (v___x_2733_ == 0)
{
lean_dec(v_a_2671_);
lean_del_object(v___x_2664_);
goto v___jp_2686_;
}
else
{
size_t v___x_2734_; uint8_t v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = lean_usize_of_nat(v___x_2732_);
v___x_2735_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2735_, v___x_2616_, v_a_2685_, v___x_2683_, v___x_2734_);
if (v___x_2736_ == 0)
{
lean_del_object(v___x_2664_);
goto v___jp_2686_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v_a_2685_);
lean_del_object(v___x_2668_);
lean_dec(v_val_2645_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2677_);
lean_ctor_set(v___x_2664_, 0, v___x_2639_);
v___x_2738_ = v___x_2664_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v___x_2677_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
v_a_2627_ = v___x_2738_;
goto v___jp_2626_;
}
}
}
}
v___jp_2686_:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2685_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2689_; 
lean_dec(v_a_2685_);
lean_dec(v_val_2645_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2677_);
lean_ctor_set(v___x_2668_, 0, v___x_2639_);
v___x_2689_ = v___x_2668_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2677_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2627_ = v___x_2689_;
goto v___jp_2626_;
}
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2610_, v_a_2685_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
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
lean_dec_ref_known(v_a_2692_, 1);
lean_del_object(v___x_2694_);
lean_dec(v_a_2685_);
lean_dec(v_val_2645_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2677_);
lean_ctor_set(v___x_2668_, 0, v___x_2639_);
v___x_2697_ = v___x_2668_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2677_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
v_a_2627_ = v___x_2697_;
goto v___jp_2626_;
}
}
else
{
lean_object* v_fnName_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2692_);
lean_dec_ref(v___x_2609_);
v_fnName_2699_ = lean_ctor_get(v_recArgInfo_2612_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_recArgInfo_2612_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; lean_object* v_unused_2720_; lean_object* v_unused_2721_; 
v_unused_2717_ = lean_ctor_get(v_recArgInfo_2612_, 5);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_recArgInfo_2612_, 4);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_recArgInfo_2612_, 3);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_recArgInfo_2612_, 2);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_recArgInfo_2612_, 1);
lean_dec(v_unused_2721_);
v___x_2701_ = v_recArgInfo_2612_;
v_isShared_2702_ = v_isSharedCheck_2716_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fnName_2699_);
lean_dec(v_recArgInfo_2612_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2716_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
size_t v_sz_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v_sz_2703_ = lean_array_size(v_a_2685_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2611_, v_sz_2703_, v___x_2683_, v_a_2685_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 5, v_val_2645_);
lean_ctor_set(v___x_2701_, 4, v_group_2615_);
lean_ctor_set(v___x_2701_, 3, v___x_2704_);
lean_ctor_set(v___x_2701_, 2, v___x_2614_);
lean_ctor_set(v___x_2701_, 1, v___x_2613_);
v___x_2706_ = v___x_2701_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_fnName_2699_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_group_2615_);
lean_ctor_set(v_reuseFailAlloc_2715_, 5, v_val_2645_);
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
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2677_);
lean_ctor_set(v___x_2668_, 0, v___x_2708_);
v___x_2710_ = v___x_2668_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2677_);
v___x_2710_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2712_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2710_);
v___x_2712_ = v___x_2694_;
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
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_a_2685_);
lean_dec_ref(v___x_2677_);
lean_del_object(v___x_2668_);
lean_dec(v_val_2645_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
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
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v___x_2677_);
lean_dec(v_a_2671_);
lean_del_object(v___x_2668_);
lean_del_object(v___x_2664_);
lean_dec(v_val_2645_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v_a_2740_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2684_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2684_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_del_object(v___x_2668_);
lean_del_object(v___x_2664_);
lean_dec(v_fst_2662_);
lean_del_object(v___x_2651_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec(v_upperBound_2638_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v_a_2750_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2670_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2670_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2656_);
lean_del_object(v___x_2651_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec(v_upperBound_2638_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v_a_2761_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2659_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2659_);
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
lean_del_object(v___x_2651_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec(v_upperBound_2638_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v_a_2769_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2655_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2655_);
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
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2651_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec(v_upperBound_2638_);
lean_dec_ref(v_group_2615_);
lean_dec(v___x_2614_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_recArgInfo_2612_);
lean_dec_ref(v___x_2609_);
v_a_2777_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2653_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2653_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
}
v___jp_2640_:
{
lean_object* v___x_2642_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2639_);
v___x_2642_ = v___x_2635_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_snd_2633_);
v___x_2642_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
return v___x_2643_;
}
}
}
}
v___jp_2626_:
{
size_t v___x_2628_; size_t v___x_2629_; 
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2619_, v___x_2628_);
v_i_2619_ = v___x_2629_;
v_b_2620_ = v_a_2627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v___x_2791_ = _args[0];
lean_object* v_ys_2792_ = _args[1];
lean_object* v___x_2793_ = _args[2];
lean_object* v_recArgInfo_2794_ = _args[3];
lean_object* v___x_2795_ = _args[4];
lean_object* v___x_2796_ = _args[5];
lean_object* v_group_2797_ = _args[6];
lean_object* v___x_2798_ = _args[7];
lean_object* v_as_2799_ = _args[8];
lean_object* v_sz_2800_ = _args[9];
lean_object* v_i_2801_ = _args[10];
lean_object* v_b_2802_ = _args[11];
lean_object* v___y_2803_ = _args[12];
lean_object* v___y_2804_ = _args[13];
lean_object* v___y_2805_ = _args[14];
lean_object* v___y_2806_ = _args[15];
lean_object* v___y_2807_ = _args[16];
_start:
{
size_t v_sz_boxed_2808_; size_t v_i_boxed_2809_; lean_object* v_res_2810_; 
v_sz_boxed_2808_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2809_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2791_, v_ys_2792_, v___x_2793_, v_recArgInfo_2794_, v___x_2795_, v___x_2796_, v_group_2797_, v___x_2798_, v_as_2799_, v_sz_boxed_2808_, v_i_boxed_2809_, v_b_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v_as_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v___x_2793_);
lean_dec_ref(v_ys_2792_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v_ys_2813_, lean_object* v___x_2814_, lean_object* v_recArgInfo_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v_group_2818_, lean_object* v_as_2819_, size_t v_sz_2820_, size_t v_i_2821_, lean_object* v_b_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_a_2829_; uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_lt(v_i_2821_, v_sz_2820_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_b_2822_);
return v___x_2834_;
}
else
{
lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2991_; 
v_snd_2835_ = lean_ctor_get(v_b_2822_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_b_2822_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v_b_2822_, 0);
lean_dec(v_unused_2992_);
v___x_2837_ = v_b_2822_;
v_isShared_2838_ = v_isSharedCheck_2991_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_dec(v_b_2822_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2991_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v_next_2839_; lean_object* v_upperBound_2840_; lean_object* v___x_2841_; 
v_next_2839_ = lean_ctor_get(v_snd_2835_, 0);
lean_inc(v_next_2839_);
v_upperBound_2840_ = lean_ctor_get(v_snd_2835_, 1);
v___x_2841_ = lean_box(0);
if (lean_obj_tag(v_next_2839_) == 0)
{
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
goto v___jp_2842_;
}
else
{
lean_object* v_val_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2990_; 
v_val_2847_ = lean_ctor_get(v_next_2839_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_next_2839_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2849_ = v_next_2839_;
v_isShared_2850_ = v_isSharedCheck_2990_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_val_2847_);
lean_dec(v_next_2839_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2990_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_nat_dec_lt(v_val_2847_, v_upperBound_2840_);
if (v___x_2851_ == 0)
{
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
goto v___jp_2842_;
}
else
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2987_; 
lean_inc(v_upperBound_2840_);
lean_del_object(v___x_2837_);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_snd_2835_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2988_ = lean_ctor_get(v_snd_2835_, 1);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_snd_2835_, 0);
lean_dec(v_unused_2989_);
v___x_2853_ = v_snd_2835_;
v_isShared_2854_ = v_isSharedCheck_2987_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v_snd_2835_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2987_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; 
lean_inc(v___y_2826_);
lean_inc_ref(v___y_2825_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc_ref(v___x_2811_);
v___x_2855_ = lean_infer_type(v___x_2811_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = l_Lean_Meta_whnfD(v_a_2856_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_a_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_a_2859_ = lean_array_uget_borrowed(v_as_2819_, v_i_2821_);
v___x_2860_ = 0;
lean_inc(v_a_2859_);
v___x_2861_ = l_Lean_Meta_forallMetaTelescope(v_a_2859_, v___x_2860_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_snd_2863_; lean_object* v_fst_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2962_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_snd_2863_ = lean_ctor_get(v_a_2862_, 1);
v_fst_2864_ = lean_ctor_get(v_a_2862_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2866_ = v_a_2862_;
v_isShared_2867_ = v_isSharedCheck_2962_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_snd_2863_);
lean_inc(v_fst_2864_);
lean_dec(v_a_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2962_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_snd_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2960_; 
v_snd_2868_ = lean_ctor_get(v_snd_2863_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_snd_2863_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_snd_2863_, 0);
lean_dec(v_unused_2961_);
v___x_2870_ = v_snd_2863_;
v_isShared_2871_ = v_isSharedCheck_2960_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_snd_2868_);
lean_dec(v_snd_2863_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2960_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2868_, v_a_2858_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_nat_add(v_val_2847_, v___x_2874_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2875_);
v___x_2877_ = v___x_2849_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2879_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2877_);
v___x_2879_ = v___x_2853_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_upperBound_2840_);
v___x_2879_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_unbox(v_a_2873_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v_a_2873_);
lean_del_object(v___x_2866_);
lean_dec(v_fst_2864_);
lean_dec(v_val_2847_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2879_);
lean_ctor_set(v___x_2870_, 0, v___x_2841_);
v___x_2882_ = v___x_2870_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2879_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
v_a_2829_ = v___x_2882_;
goto v___jp_2828_;
}
}
else
{
size_t v_sz_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v_sz_2884_ = lean_array_size(v_fst_2864_);
v___x_2885_ = ((size_t)0ULL);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2884_, v___x_2885_, v_fst_2864_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_array_get_size(v_a_2887_);
v___x_2935_ = lean_nat_dec_lt(v___x_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec(v_a_2873_);
lean_del_object(v___x_2866_);
goto v___jp_2888_;
}
else
{
if (v___x_2935_ == 0)
{
lean_dec(v_a_2873_);
lean_del_object(v___x_2866_);
goto v___jp_2888_;
}
else
{
size_t v___x_2936_; uint8_t v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = lean_usize_of_nat(v___x_2934_);
v___x_2937_ = lean_unbox(v_a_2873_);
lean_dec(v_a_2873_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2937_, v___x_2812_, v_a_2887_, v___x_2885_, v___x_2936_);
if (v___x_2938_ == 0)
{
lean_del_object(v___x_2866_);
goto v___jp_2888_;
}
else
{
lean_object* v___x_2940_; 
lean_dec(v_a_2887_);
lean_del_object(v___x_2870_);
lean_dec(v_val_2847_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v___x_2879_);
lean_ctor_set(v___x_2866_, 0, v___x_2841_);
v___x_2940_ = v___x_2866_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2879_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
v_a_2829_ = v___x_2940_;
goto v___jp_2828_;
}
}
}
}
v___jp_2888_:
{
uint8_t v___x_2889_; 
v___x_2889_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v_a_2887_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_a_2887_);
lean_dec(v_val_2847_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2879_);
lean_ctor_set(v___x_2870_, 0, v___x_2841_);
v___x_2891_ = v___x_2870_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2879_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
v_a_2829_ = v___x_2891_;
goto v___jp_2828_;
}
}
else
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2813_, v_a_2887_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
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
lean_dec_ref_known(v_a_2894_, 1);
lean_del_object(v___x_2896_);
lean_dec(v_a_2887_);
lean_dec(v_val_2847_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2879_);
lean_ctor_set(v___x_2870_, 0, v___x_2841_);
v___x_2899_ = v___x_2870_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2879_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2829_ = v___x_2899_;
goto v___jp_2828_;
}
}
else
{
lean_object* v_fnName_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2894_);
lean_dec_ref(v___x_2811_);
v_fnName_2901_ = lean_ctor_get(v_recArgInfo_2815_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_recArgInfo_2815_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; 
v_unused_2919_ = lean_ctor_get(v_recArgInfo_2815_, 5);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_recArgInfo_2815_, 4);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_recArgInfo_2815_, 3);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_recArgInfo_2815_, 2);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_recArgInfo_2815_, 1);
lean_dec(v_unused_2923_);
v___x_2903_ = v_recArgInfo_2815_;
v_isShared_2904_ = v_isSharedCheck_2918_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_fnName_2901_);
lean_dec(v_recArgInfo_2815_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2918_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
size_t v_sz_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v_sz_2905_ = lean_array_size(v_a_2887_);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2814_, v_sz_2905_, v___x_2885_, v_a_2887_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 5, v_val_2847_);
lean_ctor_set(v___x_2903_, 4, v_group_2818_);
lean_ctor_set(v___x_2903_, 3, v___x_2906_);
lean_ctor_set(v___x_2903_, 2, v___x_2817_);
lean_ctor_set(v___x_2903_, 1, v___x_2816_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_fnName_2901_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_group_2818_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_val_2847_);
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
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 1, v___x_2879_);
lean_ctor_set(v___x_2870_, 0, v___x_2910_);
v___x_2912_ = v___x_2870_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2879_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2912_);
v___x_2914_ = v___x_2896_;
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
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2887_);
lean_dec_ref(v___x_2879_);
lean_del_object(v___x_2870_);
lean_dec(v_val_2847_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
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
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v___x_2879_);
lean_dec(v_a_2873_);
lean_del_object(v___x_2870_);
lean_del_object(v___x_2866_);
lean_dec(v_val_2847_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v_a_2942_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2886_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2886_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2870_);
lean_del_object(v___x_2866_);
lean_dec(v_fst_2864_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec(v_upperBound_2840_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v_a_2952_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2872_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2872_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_a_2858_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec(v_upperBound_2840_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v_a_2963_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2861_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2861_);
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
lean_del_object(v___x_2853_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec(v_upperBound_2840_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v_a_2971_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2857_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2857_);
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
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2853_);
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec(v_upperBound_2840_);
lean_dec_ref(v_group_2818_);
lean_dec(v___x_2817_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_recArgInfo_2815_);
lean_dec_ref(v___x_2811_);
v_a_2979_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2855_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2855_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
}
v___jp_2842_:
{
lean_object* v___x_2844_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2841_);
v___x_2844_ = v___x_2837_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_snd_2835_);
v___x_2844_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
}
}
}
v___jp_2828_:
{
size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = ((size_t)1ULL);
v___x_2831_ = lean_usize_add(v_i_2821_, v___x_2830_);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2811_, v_ys_2813_, v___x_2814_, v_recArgInfo_2815_, v___x_2816_, v___x_2817_, v_group_2818_, v___x_2812_, v_as_2819_, v_sz_2820_, v___x_2831_, v_a_2829_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object** _args){
lean_object* v___x_2993_ = _args[0];
lean_object* v___x_2994_ = _args[1];
lean_object* v_ys_2995_ = _args[2];
lean_object* v___x_2996_ = _args[3];
lean_object* v_recArgInfo_2997_ = _args[4];
lean_object* v___x_2998_ = _args[5];
lean_object* v___x_2999_ = _args[6];
lean_object* v_group_3000_ = _args[7];
lean_object* v_as_3001_ = _args[8];
lean_object* v_sz_3002_ = _args[9];
lean_object* v_i_3003_ = _args[10];
lean_object* v_b_3004_ = _args[11];
lean_object* v___y_3005_ = _args[12];
lean_object* v___y_3006_ = _args[13];
lean_object* v___y_3007_ = _args[14];
lean_object* v___y_3008_ = _args[15];
lean_object* v___y_3009_ = _args[16];
_start:
{
size_t v_sz_boxed_3010_; size_t v_i_boxed_3011_; lean_object* v_res_3012_; 
v_sz_boxed_3010_ = lean_unbox_usize(v_sz_3002_);
lean_dec(v_sz_3002_);
v_i_boxed_3011_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_2993_, v___x_2994_, v_ys_2995_, v___x_2996_, v_recArgInfo_2997_, v___x_2998_, v___x_2999_, v_group_3000_, v_as_3001_, v_sz_boxed_3010_, v_i_boxed_3011_, v_b_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v_as_3001_);
lean_dec_ref(v___x_2996_);
lean_dec_ref(v_ys_2995_);
lean_dec(v___x_2994_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3013_, lean_object* v_fixedParamPerm_3014_, lean_object* v_xs_3015_, lean_object* v___x_3016_, lean_object* v_recArgPos_3017_, lean_object* v_a_3018_, lean_object* v___x_3019_, lean_object* v___x_3020_, lean_object* v_ys_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_toIndGroupInfo_3028_; lean_object* v_all_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3067_; 
v_toIndGroupInfo_3028_ = lean_ctor_get(v_group_3013_, 0);
lean_inc_ref(v_toIndGroupInfo_3028_);
v_all_3029_ = lean_ctor_get(v_toIndGroupInfo_3028_, 0);
lean_inc_ref(v_ys_3021_);
lean_inc_ref(v_fixedParamPerm_3014_);
v___x_3030_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_3014_, v_xs_3015_, v_ys_3021_);
v___x_3031_ = lean_array_get(v___x_3016_, v___x_3030_, v_recArgPos_3017_);
v___x_3032_ = lean_array_get_size(v_all_3029_);
v___x_3033_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3028_);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_toIndGroupInfo_3028_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; lean_object* v_unused_3069_; 
v_unused_3068_ = lean_ctor_get(v_toIndGroupInfo_3028_, 1);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v_toIndGroupInfo_3028_, 0);
lean_dec(v_unused_3069_);
v___x_3035_ = v_toIndGroupInfo_3028_;
v_isShared_3036_ = v_isSharedCheck_3067_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_toIndGroupInfo_3028_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3067_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3032_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v___x_3033_);
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3033_);
v___x_3039_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; size_t v_sz_3042_; size_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
v_sz_3042_ = lean_array_size(v_a_3018_);
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3031_, v___x_3019_, v_ys_3021_, v___x_3030_, v___x_3020_, v_fixedParamPerm_3014_, v_recArgPos_3017_, v_group_3013_, v_a_3018_, v_sz_3042_, v___x_3043_, v___x_3041_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_ys_3021_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3057_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3057_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3057_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_fst_3049_; 
v_fst_3049_ = lean_ctor_get(v_a_3045_, 0);
lean_inc(v_fst_3049_);
lean_dec(v_a_3045_);
if (lean_obj_tag(v_fst_3049_) == 0)
{
lean_object* v___x_3051_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3040_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3040_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
else
{
lean_object* v_val_3053_; lean_object* v___x_3055_; 
v_val_3053_ = lean_ctor_get(v_fst_3049_, 0);
lean_inc(v_val_3053_);
lean_dec_ref_known(v_fst_3049_, 1);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_val_3053_);
v___x_3055_ = v___x_3047_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3053_);
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
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3044_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3044_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3070_, lean_object* v_fixedParamPerm_3071_, lean_object* v_xs_3072_, lean_object* v___x_3073_, lean_object* v_recArgPos_3074_, lean_object* v_a_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v_ys_3078_, lean_object* v_x_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3070_, v_fixedParamPerm_3071_, v_xs_3072_, v___x_3073_, v_recArgPos_3074_, v_a_3075_, v___x_3076_, v___x_3077_, v_ys_3078_, v_x_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_x_3079_);
lean_dec(v___x_3076_);
lean_dec_ref(v_a_3075_);
lean_dec_ref(v___x_3073_);
lean_dec_ref(v_xs_3072_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3086_, lean_object* v_a_3087_, lean_object* v_xs_3088_, lean_object* v_value_3089_, lean_object* v_as_3090_, size_t v_i_3091_, size_t v_stop_3092_, lean_object* v_b_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_a_3100_; lean_object* v_val_3105_; uint8_t v___x_3107_; 
v___x_3107_ = lean_usize_dec_eq(v_i_3091_, v_stop_3092_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v_fixedParamPerm_3109_; lean_object* v_recArgPos_3110_; lean_object* v_indGroupInst_3111_; lean_object* v___x_3112_; 
v___x_3108_ = lean_array_uget_borrowed(v_as_3090_, v_i_3091_);
v_fixedParamPerm_3109_ = lean_ctor_get(v___x_3108_, 1);
v_recArgPos_3110_ = lean_ctor_get(v___x_3108_, 2);
v_indGroupInst_3111_ = lean_ctor_get(v___x_3108_, 4);
lean_inc_ref(v_indGroupInst_3111_);
lean_inc_ref(v_group_3086_);
v___x_3112_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3086_, v_indGroupInst_3111_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; uint8_t v___x_3114_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = lean_unbox(v_a_3113_);
lean_dec(v_a_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3115_ = lean_array_get_size(v_a_3087_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_nat_dec_eq(v___x_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; 
v___x_3118_ = l_Lean_instInhabitedExpr;
lean_inc(v___x_3108_);
lean_inc_ref(v_a_3087_);
lean_inc(v_recArgPos_3110_);
lean_inc_ref(v_xs_3088_);
lean_inc_ref(v_fixedParamPerm_3109_);
lean_inc_ref(v_group_3086_);
v___f_3119_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3119_, 0, v_group_3086_);
lean_closure_set(v___f_3119_, 1, v_fixedParamPerm_3109_);
lean_closure_set(v___f_3119_, 2, v_xs_3088_);
lean_closure_set(v___f_3119_, 3, v___x_3118_);
lean_closure_set(v___f_3119_, 4, v_recArgPos_3110_);
lean_closure_set(v___f_3119_, 5, v_a_3087_);
lean_closure_set(v___f_3119_, 6, v___x_3115_);
lean_closure_set(v___f_3119_, 7, v___x_3108_);
lean_inc_ref(v_value_3089_);
v___x_3120_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3089_, v___f_3119_, v___x_3117_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
if (lean_obj_tag(v_a_3121_) == 0)
{
v_a_3100_ = v_b_3093_;
goto v___jp_3099_;
}
else
{
lean_object* v_val_3122_; 
v_val_3122_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_a_3121_, 1);
v_val_3105_ = v_val_3122_;
goto v___jp_3104_;
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_b_3093_);
lean_dec_ref(v_value_3089_);
lean_dec_ref(v_xs_3088_);
lean_dec_ref(v_a_3087_);
lean_dec_ref(v_group_3086_);
v_a_3123_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3120_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3120_);
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
v_a_3100_ = v_b_3093_;
goto v___jp_3099_;
}
}
else
{
lean_inc(v___x_3108_);
v_val_3105_ = v___x_3108_;
goto v___jp_3104_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_b_3093_);
lean_dec_ref(v_value_3089_);
lean_dec_ref(v_xs_3088_);
lean_dec_ref(v_a_3087_);
lean_dec_ref(v_group_3086_);
v_a_3131_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3112_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3112_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v___x_3139_; 
lean_dec_ref(v_value_3089_);
lean_dec_ref(v_xs_3088_);
lean_dec_ref(v_a_3087_);
lean_dec_ref(v_group_3086_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v_b_3093_);
return v___x_3139_;
}
v___jp_3099_:
{
size_t v___x_3101_; size_t v___x_3102_; 
v___x_3101_ = ((size_t)1ULL);
v___x_3102_ = lean_usize_add(v_i_3091_, v___x_3101_);
v_i_3091_ = v___x_3102_;
v_b_3093_ = v_a_3100_;
goto _start;
}
v___jp_3104_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_array_push(v_b_3093_, v_val_3105_);
v_a_3100_ = v___x_3106_;
goto v___jp_3099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3140_, lean_object* v_a_3141_, lean_object* v_xs_3142_, lean_object* v_value_3143_, lean_object* v_as_3144_, lean_object* v_i_3145_, lean_object* v_stop_3146_, lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_i_boxed_3153_; size_t v_stop_boxed_3154_; lean_object* v_res_3155_; 
v_i_boxed_3153_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_stop_boxed_3154_ = lean_unbox_usize(v_stop_3146_);
lean_dec(v_stop_3146_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3140_, v_a_3141_, v_xs_3142_, v_value_3143_, v_as_3144_, v_i_boxed_3153_, v_stop_boxed_3154_, v_b_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v_as_3144_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3156_, lean_object* v_a_3157_, lean_object* v_xs_3158_, lean_object* v_value_3159_, lean_object* v_as_3160_, lean_object* v_start_3161_, lean_object* v_stop_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3169_ = lean_nat_dec_lt(v_start_3161_, v_stop_3162_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref(v_value_3159_);
lean_dec_ref(v_xs_3158_);
lean_dec_ref(v_a_3157_);
lean_dec_ref(v_group_3156_);
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
return v___x_3170_;
}
else
{
lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3171_ = lean_array_get_size(v_as_3160_);
v___x_3172_ = lean_nat_dec_le(v_stop_3162_, v___x_3171_);
if (v___x_3172_ == 0)
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_nat_dec_lt(v_start_3161_, v___x_3171_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
lean_dec_ref(v_value_3159_);
lean_dec_ref(v_xs_3158_);
lean_dec_ref(v_a_3157_);
lean_dec_ref(v_group_3156_);
v___x_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3168_);
return v___x_3174_;
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_usize_of_nat(v_start_3161_);
v___x_3176_ = lean_usize_of_nat(v___x_3171_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3156_, v_a_3157_, v_xs_3158_, v_value_3159_, v_as_3160_, v___x_3175_, v___x_3176_, v___x_3168_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
return v___x_3177_;
}
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_usize_of_nat(v_start_3161_);
v___x_3179_ = lean_usize_of_nat(v_stop_3162_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3156_, v_a_3157_, v_xs_3158_, v_value_3159_, v_as_3160_, v___x_3178_, v___x_3179_, v___x_3168_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
return v___x_3180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3181_, lean_object* v_a_3182_, lean_object* v_xs_3183_, lean_object* v_value_3184_, lean_object* v_as_3185_, lean_object* v_start_3186_, lean_object* v_stop_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3181_, v_a_3182_, v_xs_3183_, v_value_3184_, v_as_3185_, v_start_3186_, v_stop_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_stop_3187_);
lean_dec(v_start_3186_);
lean_dec_ref(v_as_3185_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3194_, lean_object* v_xs_3195_, lean_object* v_value_3196_, lean_object* v_recArgInfos_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; 
lean_inc_ref(v_group_3194_);
v___x_3203_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3194_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = lean_array_get_size(v_recArgInfos_3197_);
v___x_3207_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3194_, v_a_3204_, v_xs_3195_, v_value_3196_, v_recArgInfos_3197_, v___x_3205_, v___x_3206_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3207_;
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v_value_3196_);
lean_dec_ref(v_xs_3195_);
lean_dec_ref(v_group_3194_);
v_a_3208_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3203_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3203_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3216_, lean_object* v_xs_3217_, lean_object* v_value_3218_, lean_object* v_recArgInfos_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Elab_Structural_argsInGroup(v_group_3216_, v_xs_3217_, v_value_3218_, v_recArgInfos_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec_ref(v_recArgInfos_3219_);
return v_res_3225_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_unsigned_to_nat(10u);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3229_, lean_object* v_i_3230_, lean_object* v_acc_3231_){
_start:
{
lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = lean_array_get_size(v_xss_3229_);
v___x_3233_ = lean_nat_dec_lt(v_i_3230_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
v___x_3236_ = lean_array_push(v___x_3235_, v_acc_3231_);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3237_ = lean_array_fget_borrowed(v_xss_3229_, v_i_3230_);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3240_ = lean_array_get_size(v___x_3237_);
v___x_3241_ = lean_nat_dec_lt(v___x_3238_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_dec_ref(v_acc_3231_);
return v___x_3239_;
}
else
{
size_t v___x_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_usize_of_nat(v___x_3240_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3230_, v_acc_3231_, v_xss_3229_, v___x_3237_, v___x_3242_, v___x_3243_, v___x_3239_);
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3245_, lean_object* v_acc_3246_, lean_object* v_xss_3247_, lean_object* v_as_3248_, size_t v_i_3249_, size_t v_stop_3250_, lean_object* v_b_3251_){
_start:
{
uint8_t v___x_3252_; 
v___x_3252_ = lean_usize_dec_eq(v_i_3249_, v_stop_3250_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; size_t v___x_3259_; size_t v___x_3260_; 
v___x_3253_ = lean_array_uget_borrowed(v_as_3248_, v_i_3249_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_nat_add(v_i_3245_, v___x_3254_);
lean_inc(v___x_3253_);
lean_inc_ref(v_acc_3246_);
v___x_3256_ = lean_array_push(v_acc_3246_, v___x_3253_);
v___x_3257_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3247_, v___x_3255_, v___x_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = l_Array_append___redArg(v_b_3251_, v___x_3257_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3249_, v___x_3259_);
v_i_3249_ = v___x_3260_;
v_b_3251_ = v___x_3258_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3246_);
return v_b_3251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3262_, lean_object* v_acc_3263_, lean_object* v_xss_3264_, lean_object* v_as_3265_, lean_object* v_i_3266_, lean_object* v_stop_3267_, lean_object* v_b_3268_){
_start:
{
size_t v_i_boxed_3269_; size_t v_stop_boxed_3270_; lean_object* v_res_3271_; 
v_i_boxed_3269_ = lean_unbox_usize(v_i_3266_);
lean_dec(v_i_3266_);
v_stop_boxed_3270_ = lean_unbox_usize(v_stop_3267_);
lean_dec(v_stop_3267_);
v_res_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3262_, v_acc_3263_, v_xss_3264_, v_as_3265_, v_i_boxed_3269_, v_stop_boxed_3270_, v_b_3268_);
lean_dec_ref(v_as_3265_);
lean_dec_ref(v_xss_3264_);
lean_dec(v_i_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3272_, lean_object* v_i_3273_, lean_object* v_acc_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3272_, v_i_3273_, v_acc_3274_);
lean_dec(v_i_3273_);
lean_dec_ref(v_xss_3272_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3276_, lean_object* v_xss_3277_, lean_object* v_i_3278_, lean_object* v_acc_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3277_, v_i_3278_, v_acc_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_xss_3282_, lean_object* v_i_3283_, lean_object* v_acc_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3281_, v_xss_3282_, v_i_3283_, v_acc_3284_);
lean_dec(v_i_3283_);
lean_dec_ref(v_xss_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3286_, lean_object* v_i_3287_, lean_object* v_acc_3288_, lean_object* v_xss_3289_, lean_object* v_as_3290_, size_t v_i_3291_, size_t v_stop_3292_, lean_object* v_b_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3287_, v_acc_3288_, v_xss_3289_, v_as_3290_, v_i_3291_, v_stop_3292_, v_b_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_i_3296_, lean_object* v_acc_3297_, lean_object* v_xss_3298_, lean_object* v_as_3299_, lean_object* v_i_3300_, lean_object* v_stop_3301_, lean_object* v_b_3302_){
_start:
{
size_t v_i_boxed_3303_; size_t v_stop_boxed_3304_; lean_object* v_res_3305_; 
v_i_boxed_3303_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_stop_boxed_3304_ = lean_unbox_usize(v_stop_3301_);
lean_dec(v_stop_3301_);
v_res_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3295_, v_i_3296_, v_acc_3297_, v_xss_3298_, v_as_3299_, v_i_boxed_3303_, v_stop_boxed_3304_, v_b_3302_);
lean_dec_ref(v_as_3299_);
lean_dec_ref(v_xss_3298_);
lean_dec(v_i_3296_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3306_, size_t v_i_3307_, size_t v_stop_3308_, lean_object* v_b_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_usize_dec_eq(v_i_3307_, v_stop_3308_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; size_t v___x_3314_; size_t v___x_3315_; 
v___x_3311_ = lean_array_uget_borrowed(v_as_3306_, v_i_3307_);
v___x_3312_ = lean_array_get_size(v___x_3311_);
v___x_3313_ = lean_nat_mul(v_b_3309_, v___x_3312_);
lean_dec(v_b_3309_);
v___x_3314_ = ((size_t)1ULL);
v___x_3315_ = lean_usize_add(v_i_3307_, v___x_3314_);
v_i_3307_ = v___x_3315_;
v_b_3309_ = v___x_3313_;
goto _start;
}
else
{
return v_b_3309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3317_, lean_object* v_i_3318_, lean_object* v_stop_3319_, lean_object* v_b_3320_){
_start:
{
size_t v_i_boxed_3321_; size_t v_stop_boxed_3322_; lean_object* v_res_3323_; 
v_i_boxed_3321_ = lean_unbox_usize(v_i_3318_);
lean_dec(v_i_3318_);
v_stop_boxed_3322_ = lean_unbox_usize(v_stop_3319_);
lean_dec(v_stop_3319_);
v_res_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3317_, v_i_boxed_3321_, v_stop_boxed_3322_, v_b_3320_);
lean_dec_ref(v_as_3317_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___y_3329_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3325_ = lean_unsigned_to_nat(10u);
v___x_3326_ = lean_unsigned_to_nat(1u);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_array_get_size(v_xss_3324_);
v___x_3336_ = lean_nat_dec_lt(v___x_3327_, v___x_3335_);
if (v___x_3336_ == 0)
{
v___y_3329_ = v___x_3326_;
goto v___jp_3328_;
}
else
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
if (v___x_3337_ == 0)
{
if (v___x_3336_ == 0)
{
v___y_3329_ = v___x_3326_;
goto v___jp_3328_;
}
else
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)0ULL);
v___x_3339_ = lean_usize_of_nat(v___x_3335_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3324_, v___x_3338_, v___x_3339_, v___x_3326_);
v___y_3329_ = v___x_3340_;
goto v___jp_3328_;
}
}
else
{
size_t v___x_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = lean_usize_of_nat(v___x_3335_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3324_, v___x_3341_, v___x_3342_, v___x_3326_);
v___y_3329_ = v___x_3343_;
goto v___jp_3328_;
}
}
v___jp_3328_:
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_nat_dec_lt(v___x_3325_, v___y_3329_);
lean_dec(v___y_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3332_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3324_, v___x_3327_, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_box(0);
return v___x_3334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3344_);
lean_dec_ref(v_xss_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3346_, lean_object* v_xss_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3349_, lean_object* v_xss_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3349_, v_xss_3350_);
lean_dec_ref(v_xss_3350_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3352_, lean_object* v_as_3353_, size_t v_i_3354_, size_t v_stop_3355_, lean_object* v_b_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3353_, v_i_3354_, v_stop_3355_, v_b_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3358_, lean_object* v_as_3359_, lean_object* v_i_3360_, lean_object* v_stop_3361_, lean_object* v_b_3362_){
_start:
{
size_t v_i_boxed_3363_; size_t v_stop_boxed_3364_; lean_object* v_res_3365_; 
v_i_boxed_3363_ = lean_unbox_usize(v_i_3360_);
lean_dec(v_i_3360_);
v_stop_boxed_3364_ = lean_unbox_usize(v_stop_3361_);
lean_dec(v_stop_3361_);
v_res_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3358_, v_as_3359_, v_i_boxed_3363_, v_stop_boxed_3364_, v_b_3362_);
lean_dec_ref(v_as_3359_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(lean_object* v_as_3366_, size_t v_i_3367_, size_t v_stop_3368_, lean_object* v_b_3369_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_usize_dec_eq(v_i_3367_, v_stop_3368_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; size_t v___x_3373_; size_t v___x_3374_; 
v___x_3371_ = lean_array_uget_borrowed(v_as_3366_, v_i_3367_);
v___x_3372_ = l_Array_append___redArg(v_b_3369_, v___x_3371_);
v___x_3373_ = ((size_t)1ULL);
v___x_3374_ = lean_usize_add(v_i_3367_, v___x_3373_);
v_i_3367_ = v___x_3374_;
v_b_3369_ = v___x_3372_;
goto _start;
}
else
{
return v_b_3369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(lean_object* v_as_3376_, lean_object* v_i_3377_, lean_object* v_stop_3378_, lean_object* v_b_3379_){
_start:
{
size_t v_i_boxed_3380_; size_t v_stop_boxed_3381_; lean_object* v_res_3382_; 
v_i_boxed_3380_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_stop_boxed_3381_ = lean_unbox_usize(v_stop_3378_);
lean_dec(v_stop_3378_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_3376_, v_i_boxed_3380_, v_stop_boxed_3381_, v_b_3379_);
lean_dec_ref(v_as_3376_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
if (lean_obj_tag(v_a_3383_) == 0)
{
lean_object* v___x_3385_; 
v___x_3385_ = l_List_reverse___redArg(v_a_3384_);
return v___x_3385_;
}
else
{
lean_object* v_head_3386_; lean_object* v_tail_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3397_; 
v_head_3386_ = lean_ctor_get(v_a_3383_, 0);
v_tail_3387_ = lean_ctor_get(v_a_3383_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3389_ = v_a_3383_;
v_isShared_3390_ = v_isSharedCheck_3397_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_tail_3387_);
lean_inc(v_head_3386_);
lean_dec(v_a_3383_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3397_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3391_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_3386_);
v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 1, v_a_3384_);
lean_ctor_set(v___x_3389_, 0, v___x_3392_);
v___x_3394_ = v___x_3389_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_a_3384_);
v___x_3394_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
v_a_3383_ = v_tail_3387_;
v_a_3384_ = v___x_3394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(size_t v_sz_3398_, size_t v_i_3399_, lean_object* v_bs_3400_){
_start:
{
uint8_t v___x_3401_; 
v___x_3401_ = lean_usize_dec_lt(v_i_3399_, v_sz_3398_);
if (v___x_3401_ == 0)
{
return v_bs_3400_;
}
else
{
lean_object* v_v_3402_; lean_object* v___x_3403_; lean_object* v_bs_x27_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; 
v_v_3402_ = lean_array_uget(v_bs_3400_, v_i_3399_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v_bs_x27_3404_ = lean_array_uset(v_bs_3400_, v_i_3399_, v___x_3403_);
v___x_3405_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_3402_);
lean_dec(v_v_3402_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3399_, v___x_3406_);
v___x_3408_ = lean_array_uset(v_bs_x27_3404_, v_i_3399_, v___x_3405_);
v_i_3399_ = v___x_3407_;
v_bs_3400_ = v___x_3408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_bs_3412_){
_start:
{
size_t v_sz_boxed_3413_; size_t v_i_boxed_3414_; lean_object* v_res_3415_; 
v_sz_boxed_3413_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3414_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_3413_, v_i_boxed_3414_, v_bs_3412_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(lean_object* v_xs_3416_, lean_object* v_as_3417_, size_t v_sz_3418_, size_t v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_usize_dec_lt(v_i_3419_, v_sz_3418_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v_xs_3416_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_b_3420_);
return v___x_3427_;
}
else
{
lean_object* v_snd_3428_; lean_object* v_snd_3429_; lean_object* v_snd_3430_; lean_object* v_snd_3431_; lean_object* v_fst_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3576_; 
v_snd_3428_ = lean_ctor_get(v_b_3420_, 1);
lean_inc(v_snd_3428_);
v_snd_3429_ = lean_ctor_get(v_snd_3428_, 1);
lean_inc(v_snd_3429_);
v_snd_3430_ = lean_ctor_get(v_snd_3429_, 1);
lean_inc(v_snd_3430_);
v_snd_3431_ = lean_ctor_get(v_snd_3430_, 1);
lean_inc(v_snd_3431_);
v_fst_3432_ = lean_ctor_get(v_b_3420_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_b_3420_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; 
v_unused_3577_ = lean_ctor_get(v_b_3420_, 1);
lean_dec(v_unused_3577_);
v___x_3434_ = v_b_3420_;
v_isShared_3435_ = v_isSharedCheck_3576_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_fst_3432_);
lean_dec(v_b_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3576_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_fst_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3574_; 
v_fst_3436_ = lean_ctor_get(v_snd_3428_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_snd_3428_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v_snd_3428_, 1);
lean_dec(v_unused_3575_);
v___x_3438_ = v_snd_3428_;
v_isShared_3439_ = v_isSharedCheck_3574_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_fst_3436_);
lean_dec(v_snd_3428_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3574_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3572_; 
v_fst_3440_ = lean_ctor_get(v_snd_3429_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_snd_3429_, 1);
lean_dec(v_unused_3573_);
v___x_3442_ = v_snd_3429_;
v_isShared_3443_ = v_isSharedCheck_3572_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_fst_3440_);
lean_dec(v_snd_3429_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3572_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_fst_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3570_; 
v_fst_3444_ = lean_ctor_get(v_snd_3430_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_snd_3430_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_snd_3430_, 1);
lean_dec(v_unused_3571_);
v___x_3446_ = v_snd_3430_;
v_isShared_3447_ = v_isSharedCheck_3570_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_fst_3444_);
lean_dec(v_snd_3430_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3570_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_array_3448_; lean_object* v_start_3449_; lean_object* v_stop_3450_; uint8_t v___x_3451_; 
v_array_3448_ = lean_ctor_get(v_snd_3431_, 0);
v_start_3449_ = lean_ctor_get(v_snd_3431_, 1);
v_stop_3450_ = lean_ctor_get(v_snd_3431_, 2);
v___x_3451_ = lean_nat_dec_lt(v_start_3449_, v_stop_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3453_; 
lean_dec_ref(v_xs_3416_);
if (v_isShared_3447_ == 0)
{
v___x_3453_ = v___x_3446_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3444_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3431_);
v___x_3453_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3453_);
v___x_3455_ = v___x_3442_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3455_);
v___x_3457_ = v___x_3438_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3459_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3457_);
v___x_3459_ = v___x_3434_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
}
}
}
else
{
lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3566_; 
lean_inc(v_stop_3450_);
lean_inc(v_start_3449_);
lean_inc_ref(v_array_3448_);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_snd_3431_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; lean_object* v_unused_3568_; lean_object* v_unused_3569_; 
v_unused_3567_ = lean_ctor_get(v_snd_3431_, 2);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v_snd_3431_, 1);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_snd_3431_, 0);
lean_dec(v_unused_3569_);
v___x_3466_ = v_snd_3431_;
v_isShared_3467_ = v_isSharedCheck_3566_;
goto v_resetjp_3465_;
}
else
{
lean_dec(v_snd_3431_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3566_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_array_3468_; lean_object* v_start_3469_; lean_object* v_stop_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v_array_3468_ = lean_ctor_get(v_fst_3444_, 0);
v_start_3469_ = lean_ctor_get(v_fst_3444_, 1);
v_stop_3470_ = lean_ctor_get(v_fst_3444_, 2);
v___x_3471_ = lean_array_fget(v_array_3448_, v_start_3449_);
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v_start_3449_, v___x_3472_);
lean_dec(v_start_3449_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v___x_3473_);
v___x_3475_ = v___x_3466_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_array_3448_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_stop_3450_);
v___x_3475_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_nat_dec_lt(v_start_3469_, v_stop_3470_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3478_; 
lean_dec(v___x_3471_);
lean_dec_ref(v_xs_3416_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3475_);
v___x_3478_ = v___x_3446_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3444_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3475_);
v___x_3478_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3478_);
v___x_3480_ = v___x_3442_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3482_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3480_);
v___x_3482_ = v___x_3438_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3482_);
v___x_3484_ = v___x_3434_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
}
}
}
else
{
lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3561_; 
lean_inc(v_stop_3470_);
lean_inc(v_start_3469_);
lean_inc_ref(v_array_3468_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_fst_3444_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; 
v_unused_3562_ = lean_ctor_get(v_fst_3444_, 2);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_fst_3444_, 1);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_fst_3444_, 0);
lean_dec(v_unused_3564_);
v___x_3491_ = v_fst_3444_;
v_isShared_3492_ = v_isSharedCheck_3561_;
goto v_resetjp_3490_;
}
else
{
lean_dec(v_fst_3444_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3561_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v_array_3493_; lean_object* v_start_3494_; lean_object* v_stop_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v_array_3493_ = lean_ctor_get(v_fst_3440_, 0);
v_start_3494_ = lean_ctor_get(v_fst_3440_, 1);
v_stop_3495_ = lean_ctor_get(v_fst_3440_, 2);
v___x_3496_ = lean_array_fget(v_array_3468_, v_start_3469_);
v___x_3497_ = lean_nat_add(v_start_3469_, v___x_3472_);
lean_dec(v_start_3469_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v___x_3497_);
v___x_3499_ = v___x_3491_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_array_3468_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_stop_3470_);
v___x_3499_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
uint8_t v___x_3500_; 
v___x_3500_ = lean_nat_dec_lt(v_start_3494_, v_stop_3495_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v___x_3496_);
lean_dec(v___x_3471_);
lean_dec_ref(v_xs_3416_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3475_);
lean_ctor_set(v___x_3446_, 0, v___x_3499_);
v___x_3502_ = v___x_3446_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v___x_3475_);
v___x_3502_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3502_);
v___x_3504_ = v___x_3442_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3504_);
v___x_3506_ = v___x_3438_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_fst_3436_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3508_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3506_);
v___x_3508_ = v___x_3434_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_fst_3432_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
return v___x_3509_;
}
}
}
}
}
else
{
lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3556_; 
lean_inc(v_stop_3495_);
lean_inc(v_start_3494_);
lean_inc_ref(v_array_3493_);
lean_del_object(v___x_3434_);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_fst_3440_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; lean_object* v_unused_3558_; lean_object* v_unused_3559_; 
v_unused_3557_ = lean_ctor_get(v_fst_3440_, 2);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_fst_3440_, 1);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_fst_3440_, 0);
lean_dec(v_unused_3559_);
v___x_3515_ = v_fst_3440_;
v_isShared_3516_ = v_isSharedCheck_3556_;
goto v_resetjp_3514_;
}
else
{
lean_dec(v_fst_3440_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3556_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_a_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_a_3517_ = lean_array_uget_borrowed(v_as_3417_, v_i_3419_);
v___x_3518_ = lean_array_fget_borrowed(v_array_3493_, v_start_3494_);
lean_inc(v___x_3518_);
lean_inc_ref(v_xs_3416_);
lean_inc(v_a_3517_);
v___x_3519_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_3517_, v___x_3471_, v_xs_3416_, v___x_3518_, v___x_3496_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3547_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v_fst_3521_ = lean_ctor_get(v_a_3520_, 0);
v_snd_3522_ = lean_ctor_get(v_a_3520_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3524_ = v_a_3520_;
v_isShared_3525_ = v_isSharedCheck_3547_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_a_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3547_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_nat_add(v_start_3494_, v___x_3472_);
lean_dec(v_start_3494_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3526_);
v___x_3528_ = v___x_3515_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_array_3493_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_stop_3495_);
v___x_3528_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_fst_3432_);
lean_ctor_set(v___x_3529_, 1, v_snd_3522_);
v___x_3530_ = lean_array_push(v_fst_3436_, v_fst_3521_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3475_);
lean_ctor_set(v___x_3524_, 0, v___x_3499_);
v___x_3532_ = v___x_3524_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3475_);
v___x_3532_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3534_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3532_);
lean_ctor_set(v___x_3446_, 0, v___x_3528_);
v___x_3534_ = v___x_3446_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 1, v___x_3534_);
lean_ctor_set(v___x_3442_, 0, v___x_3530_);
v___x_3536_ = v___x_3442_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3536_);
lean_ctor_set(v___x_3438_, 0, v___x_3529_);
v___x_3538_ = v___x_3438_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
size_t v___x_3539_; size_t v___x_3540_; 
v___x_3539_ = ((size_t)1ULL);
v___x_3540_ = lean_usize_add(v_i_3419_, v___x_3539_);
v_i_3419_ = v___x_3540_;
v_b_3420_ = v___x_3538_;
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
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3515_);
lean_dec_ref(v___x_3499_);
lean_dec(v_stop_3495_);
lean_dec(v_start_3494_);
lean_dec_ref(v_array_3493_);
lean_dec_ref(v___x_3475_);
lean_del_object(v___x_3446_);
lean_del_object(v___x_3442_);
lean_del_object(v___x_3438_);
lean_dec(v_fst_3436_);
lean_dec(v_fst_3432_);
lean_dec_ref(v_xs_3416_);
v_a_3548_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3519_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3519_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(lean_object* v_xs_3578_, lean_object* v_as_3579_, lean_object* v_sz_3580_, lean_object* v_i_3581_, lean_object* v_b_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_sz_boxed_3588_; size_t v_i_boxed_3589_; lean_object* v_res_3590_; 
v_sz_boxed_3588_ = lean_unbox_usize(v_sz_3580_);
lean_dec(v_sz_3580_);
v_i_boxed_3589_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3578_, v_as_3579_, v_sz_boxed_3588_, v_i_boxed_3589_, v_b_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v_as_3579_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
if (lean_obj_tag(v_a_3591_) == 0)
{
lean_object* v___x_3593_; 
v___x_3593_ = l_List_reverse___redArg(v_a_3592_);
return v___x_3593_;
}
else
{
lean_object* v_head_3594_; lean_object* v_tail_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3604_; 
v_head_3594_ = lean_ctor_get(v_a_3591_, 0);
v_tail_3595_ = lean_ctor_get(v_a_3591_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3591_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3597_ = v_a_3591_;
v_isShared_3598_ = v_isSharedCheck_3604_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_tail_3595_);
lean_inc(v_head_3594_);
lean_dec(v_a_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3604_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_3594_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v_a_3592_);
lean_ctor_set(v___x_3597_, 0, v___x_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_a_3592_);
v___x_3601_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3591_ = v_tail_3595_;
v_a_3592_ = v___x_3601_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(lean_object* v_as_3605_, lean_object* v_j_3606_){
_start:
{
lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = lean_array_get_size(v_as_3605_);
v___x_3608_ = lean_nat_dec_lt(v_j_3606_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec(v_j_3606_);
v___x_3609_ = lean_box(0);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3610_ = lean_array_fget_borrowed(v_as_3605_, v_j_3606_);
v___x_3611_ = lean_array_get_size(v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = lean_nat_dec_eq(v___x_3611_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3615_ = lean_nat_add(v_j_3606_, v___x_3614_);
lean_dec(v_j_3606_);
v_j_3606_ = v___x_3615_;
goto _start;
}
else
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3617_, 0, v_j_3606_);
return v___x_3617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(lean_object* v_as_3618_, lean_object* v_j_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_as_3618_, v_j_3619_);
lean_dec_ref(v_as_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(lean_object* v_a_3621_, lean_object* v_as_3622_, size_t v_sz_3623_, size_t v_i_3624_, lean_object* v_b_3625_){
_start:
{
uint8_t v___x_3627_; 
v___x_3627_ = lean_usize_dec_lt(v_i_3624_, v_sz_3623_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; 
lean_dec_ref(v_a_3621_);
v___x_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3628_, 0, v_b_3625_);
return v___x_3628_;
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; 
v_a_3629_ = lean_array_uget_borrowed(v_as_3622_, v_i_3624_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3621_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v_a_3621_);
lean_ctor_set(v___x_3630_, 1, v_a_3629_);
v___x_3631_ = lean_array_push(v_b_3625_, v___x_3630_);
v___x_3632_ = ((size_t)1ULL);
v___x_3633_ = lean_usize_add(v_i_3624_, v___x_3632_);
v_i_3624_ = v___x_3633_;
v_b_3625_ = v___x_3631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(lean_object* v_a_3635_, lean_object* v_as_3636_, lean_object* v_sz_3637_, lean_object* v_i_3638_, lean_object* v_b_3639_, lean_object* v___y_3640_){
_start:
{
size_t v_sz_boxed_3641_; size_t v_i_boxed_3642_; lean_object* v_res_3643_; 
v_sz_boxed_3641_ = lean_unbox_usize(v_sz_3637_);
lean_dec(v_sz_3637_);
v_i_boxed_3642_ = lean_unbox_usize(v_i_3638_);
lean_dec(v_i_3638_);
v_res_3643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3635_, v_as_3636_, v_sz_boxed_3641_, v_i_boxed_3642_, v_b_3639_);
lean_dec_ref(v_as_3636_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(lean_object* v_a_3644_, lean_object* v_xs_3645_, lean_object* v_as_3646_, size_t v_sz_3647_, size_t v_i_3648_, lean_object* v_b_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_usize_dec_lt(v_i_3648_, v_sz_3647_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; 
lean_dec_ref(v_xs_3645_);
lean_dec_ref(v_a_3644_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_b_3649_);
return v___x_3656_;
}
else
{
lean_object* v_snd_3657_; lean_object* v_fst_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3701_; 
v_snd_3657_ = lean_ctor_get(v_b_3649_, 1);
v_fst_3658_ = lean_ctor_get(v_b_3649_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_b_3649_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3660_ = v_b_3649_;
v_isShared_3661_ = v_isSharedCheck_3701_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_snd_3657_);
lean_inc(v_fst_3658_);
lean_dec(v_b_3649_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3701_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_array_3662_; lean_object* v_start_3663_; lean_object* v_stop_3664_; uint8_t v___x_3665_; 
v_array_3662_ = lean_ctor_get(v_snd_3657_, 0);
v_start_3663_ = lean_ctor_get(v_snd_3657_, 1);
v_stop_3664_ = lean_ctor_get(v_snd_3657_, 2);
v___x_3665_ = lean_nat_dec_lt(v_start_3663_, v_stop_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3667_; 
lean_dec_ref(v_xs_3645_);
lean_dec_ref(v_a_3644_);
if (v_isShared_3661_ == 0)
{
v___x_3667_ = v___x_3660_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_fst_3658_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_snd_3657_);
v___x_3667_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
else
{
lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3697_; 
lean_inc(v_stop_3664_);
lean_inc(v_start_3663_);
lean_inc_ref(v_array_3662_);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_snd_3657_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3698_ = lean_ctor_get(v_snd_3657_, 2);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_snd_3657_, 1);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_snd_3657_, 0);
lean_dec(v_unused_3700_);
v___x_3671_ = v_snd_3657_;
v_isShared_3672_ = v_isSharedCheck_3697_;
goto v_resetjp_3670_;
}
else
{
lean_dec(v_snd_3657_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3697_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_a_3673_ = lean_array_uget_borrowed(v_as_3646_, v_i_3648_);
v___x_3674_ = lean_array_fget_borrowed(v_array_3662_, v_start_3663_);
lean_inc(v_a_3673_);
lean_inc_ref(v_xs_3645_);
lean_inc_ref(v_a_3644_);
v___x_3675_ = l_Lean_Elab_Structural_argsInGroup(v_a_3644_, v_xs_3645_, v_a_3673_, v___x_3674_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v___x_3675_, 1);
v___x_3677_ = lean_unsigned_to_nat(1u);
v___x_3678_ = lean_nat_add(v_start_3663_, v___x_3677_);
lean_dec(v_start_3663_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v___x_3678_);
v___x_3680_ = v___x_3671_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_array_3662_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_stop_3664_);
v___x_3680_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_array_push(v_fst_3658_, v_a_3676_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 1, v___x_3680_);
lean_ctor_set(v___x_3660_, 0, v___x_3681_);
v___x_3683_ = v___x_3660_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3680_);
v___x_3683_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
size_t v___x_3684_; size_t v___x_3685_; 
v___x_3684_ = ((size_t)1ULL);
v___x_3685_ = lean_usize_add(v_i_3648_, v___x_3684_);
v_i_3648_ = v___x_3685_;
v_b_3649_ = v___x_3683_;
goto _start;
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_del_object(v___x_3671_);
lean_dec(v_stop_3664_);
lean_dec(v_start_3663_);
lean_dec_ref(v_array_3662_);
lean_del_object(v___x_3660_);
lean_dec(v_fst_3658_);
lean_dec_ref(v_xs_3645_);
lean_dec_ref(v_a_3644_);
v_a_3689_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3675_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3675_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(lean_object* v_a_3702_, lean_object* v_xs_3703_, lean_object* v_as_3704_, lean_object* v_sz_3705_, lean_object* v_i_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
size_t v_sz_boxed_3713_; size_t v_i_boxed_3714_; lean_object* v_res_3715_; 
v_sz_boxed_3713_ = lean_unbox_usize(v_sz_3705_);
lean_dec(v_sz_3705_);
v_i_boxed_3714_ = lean_unbox_usize(v_i_3706_);
lean_dec(v_i_3706_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3702_, v_xs_3703_, v_as_3704_, v_sz_boxed_3713_, v_i_boxed_3714_, v_b_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v_as_3704_);
return v_res_3715_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1));
v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5));
v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7));
v___x_3729_ = l_Lean_stringToMessageData(v___x_3728_);
return v___x_3729_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10(void){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9));
v___x_3732_ = l_Lean_stringToMessageData(v___x_3731_);
return v___x_3732_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11));
v___x_3735_ = l_Lean_stringToMessageData(v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(lean_object* v___x_3736_, lean_object* v_values_3737_, lean_object* v_xs_3738_, lean_object* v_fnNames_3739_, lean_object* v_as_3740_, size_t v_sz_3741_, size_t v_i_3742_, lean_object* v_b_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_a_3750_; uint8_t v___x_3754_; 
v___x_3754_ = lean_usize_dec_lt(v_i_3742_, v_sz_3741_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; 
lean_dec_ref(v_xs_3738_);
lean_dec_ref(v___x_3736_);
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_b_3743_);
return v___x_3755_;
}
else
{
lean_object* v___x_3756_; lean_object* v_recArgInfoss_3757_; lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; size_t v_sz_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v___x_3756_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3758_ = lean_array_uget_borrowed(v_as_3740_, v_i_3742_);
v___x_3759_ = lean_array_get_size(v___x_3736_);
lean_inc_ref(v___x_3736_);
v___x_3760_ = l_Array_toSubarray___redArg(v___x_3736_, v___x_3756_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_recArgInfoss_3757_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v_sz_3762_ = lean_array_size(v_values_3737_);
v___x_3763_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3738_);
lean_inc(v_a_3758_);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3758_, v_xs_3738_, v_values_3737_, v_sz_3762_, v___x_3763_, v___x_3761_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v_fst_3766_; lean_object* v_snd_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3825_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v_fst_3766_ = lean_ctor_get(v_b_3743_, 0);
v_snd_3767_ = lean_ctor_get(v_b_3743_, 1);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_b_3743_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3769_ = v_b_3743_;
v_isShared_3770_ = v_isSharedCheck_3825_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_snd_3767_);
lean_inc(v_fst_3766_);
lean_dec(v_b_3743_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3825_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_fst_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3823_; 
v_fst_3771_ = lean_ctor_get(v_a_3765_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3823_ == 0)
{
lean_object* v_unused_3824_; 
v_unused_3824_ = lean_ctor_get(v_a_3765_, 1);
lean_dec(v_unused_3824_);
v___x_3773_ = v_a_3765_;
v_isShared_3774_ = v_isSharedCheck_3823_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_fst_3771_);
lean_dec(v_a_3765_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3823_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3771_, v___x_3756_);
if (lean_obj_tag(v___x_3775_) == 1)
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
lean_dec(v_fst_3771_);
v_val_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = lean_box(0);
v___x_3778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3758_);
v___x_3779_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3758_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set_tag(v___x_3769_, 7);
lean_ctor_set(v___x_3769_, 1, v___x_3779_);
lean_ctor_set(v___x_3769_, 0, v___x_3778_);
v___x_3781_ = v___x_3769_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_array_get_borrowed(v___x_3777_, v_fnNames_3739_, v_val_3776_);
lean_dec(v_val_3776_);
lean_inc(v___x_3784_);
v___x_3785_ = l_Lean_MessageData_ofName(v___x_3784_);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3783_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v_fst_3766_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_snd_3767_);
lean_ctor_set(v___x_3773_, 0, v___x_3789_);
v___x_3791_ = v___x_3773_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_snd_3767_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v_a_3750_ = v___x_3791_;
goto v___jp_3749_;
}
}
}
else
{
lean_object* v___x_3794_; 
lean_dec(v___x_3775_);
v___x_3794_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3771_);
lean_dec(v_fst_3771_);
if (lean_obj_tag(v___x_3794_) == 1)
{
lean_object* v_val_3795_; size_t v_sz_3796_; lean_object* v___x_3797_; 
lean_del_object(v___x_3769_);
v_val_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_val_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v_sz_3796_ = lean_array_size(v_val_3795_);
lean_inc(v_a_3758_);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3758_, v_val_3795_, v_sz_3796_, v___x_3763_, v_snd_3767_);
lean_dec(v_val_3795_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_a_3798_);
lean_ctor_set(v___x_3773_, 0, v_fst_3766_);
v___x_3800_ = v___x_3773_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_fst_3766_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_a_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
v_a_3750_ = v___x_3800_;
goto v___jp_3749_;
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_del_object(v___x_3773_);
lean_dec(v_fst_3766_);
lean_dec_ref(v_xs_3738_);
lean_dec_ref(v___x_3736_);
v_a_3802_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3797_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3797_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
lean_dec(v___x_3794_);
v___x_3810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3758_);
v___x_3811_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3758_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set_tag(v___x_3769_, 7);
lean_ctor_set(v___x_3769_, 1, v___x_3811_);
lean_ctor_set(v___x_3769_, 0, v___x_3810_);
v___x_3813_ = v___x_3769_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_fst_3766_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v_snd_3767_);
lean_ctor_set(v___x_3773_, 0, v___x_3818_);
v___x_3820_ = v___x_3773_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_snd_3767_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
v_a_3750_ = v___x_3820_;
goto v___jp_3749_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_b_3743_);
lean_dec_ref(v_xs_3738_);
lean_dec_ref(v___x_3736_);
v_a_3826_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3764_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3764_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
v___jp_3749_:
{
size_t v___x_3751_; size_t v___x_3752_; 
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3742_, v___x_3751_);
v_i_3742_ = v___x_3752_;
v_b_3743_ = v_a_3750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(lean_object* v___x_3834_, lean_object* v_values_3835_, lean_object* v_xs_3836_, lean_object* v_fnNames_3837_, lean_object* v_as_3838_, lean_object* v_sz_3839_, lean_object* v_i_3840_, lean_object* v_b_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3839_);
lean_dec(v_sz_3839_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3840_);
lean_dec(v_i_3840_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3834_, v_values_3835_, v_xs_3836_, v_fnNames_3837_, v_as_3838_, v_sz_boxed_3847_, v_i_boxed_3848_, v_b_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v_as_3838_);
lean_dec_ref(v_fnNames_3837_);
lean_dec_ref(v_values_3835_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(lean_object* v_xs_3850_, lean_object* v___x_3851_, lean_object* v_values_3852_, lean_object* v_fnNames_3853_, lean_object* v_as_3854_, size_t v_sz_3855_, size_t v_i_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_a_3864_; uint8_t v___x_3868_; 
v___x_3868_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec_ref(v___x_3851_);
lean_dec_ref(v_xs_3850_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_b_3857_);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v_recArgInfoss_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; size_t v_sz_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3870_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v_a_3872_ = lean_array_uget_borrowed(v_as_3854_, v_i_3856_);
v___x_3873_ = lean_array_get_size(v___x_3851_);
lean_inc_ref(v___x_3851_);
v___x_3874_ = l_Array_toSubarray___redArg(v___x_3851_, v___x_3870_, v___x_3873_);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v_recArgInfoss_3871_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v_sz_3876_ = lean_array_size(v_values_3852_);
v___x_3877_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3850_);
lean_inc(v_a_3872_);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_3872_, v_xs_3850_, v_values_3852_, v_sz_3876_, v___x_3877_, v___x_3875_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_fst_3880_; lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3939_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v_fst_3880_ = lean_ctor_get(v_b_3857_, 0);
v_snd_3881_ = lean_ctor_get(v_b_3857_, 1);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_b_3857_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3883_ = v_b_3857_;
v_isShared_3884_ = v_isSharedCheck_3939_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_inc(v_fst_3880_);
lean_dec(v_b_3857_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3939_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_fst_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3937_; 
v_fst_3885_ = lean_ctor_get(v_a_3879_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_a_3879_, 1);
lean_dec(v_unused_3938_);
v___x_3887_ = v_a_3879_;
v_isShared_3888_ = v_isSharedCheck_3937_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_fst_3885_);
lean_dec(v_a_3879_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3937_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_3885_, v___x_3870_);
if (lean_obj_tag(v___x_3889_) == 1)
{
lean_object* v_val_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
lean_dec(v_fst_3885_);
v_val_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_val_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
lean_inc(v_a_3872_);
v___x_3893_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3872_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 7);
lean_ctor_set(v___x_3883_, 1, v___x_3893_);
lean_ctor_set(v___x_3883_, 0, v___x_3892_);
v___x_3895_ = v___x_3883_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_array_get_borrowed(v___x_3891_, v_fnNames_3853_, v_val_3890_);
lean_dec(v_val_3890_);
lean_inc(v___x_3898_);
v___x_3899_ = l_Lean_MessageData_ofName(v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3897_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_fst_3880_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_snd_3881_);
lean_ctor_set(v___x_3887_, 0, v___x_3903_);
v___x_3905_ = v___x_3887_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_snd_3881_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
v_a_3864_ = v___x_3905_;
goto v___jp_3863_;
}
}
}
else
{
lean_object* v___x_3908_; 
lean_dec(v___x_3889_);
v___x_3908_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3885_);
lean_dec(v_fst_3885_);
if (lean_obj_tag(v___x_3908_) == 1)
{
lean_object* v_val_3909_; size_t v_sz_3910_; lean_object* v___x_3911_; 
lean_del_object(v___x_3883_);
v_val_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v_sz_3910_ = lean_array_size(v_val_3909_);
lean_inc(v_a_3872_);
v___x_3911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_3872_, v_val_3909_, v_sz_3910_, v___x_3877_, v_snd_3881_);
lean_dec(v_val_3909_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_a_3912_);
lean_ctor_set(v___x_3887_, 0, v_fst_3880_);
v___x_3914_ = v___x_3887_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_fst_3880_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_a_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
v_a_3864_ = v___x_3914_;
goto v___jp_3863_;
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_del_object(v___x_3887_);
lean_dec(v_fst_3880_);
lean_dec_ref(v___x_3851_);
lean_dec_ref(v_xs_3850_);
v_a_3916_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3911_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3911_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
lean_dec(v___x_3908_);
v___x_3924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
lean_inc(v_a_3872_);
v___x_3925_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3872_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 7);
lean_ctor_set(v___x_3883_, 1, v___x_3925_);
lean_ctor_set(v___x_3883_, 0, v___x_3924_);
v___x_3927_ = v___x_3883_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v_fst_3880_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_snd_3881_);
lean_ctor_set(v___x_3887_, 0, v___x_3932_);
v___x_3934_ = v___x_3887_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_snd_3881_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
v_a_3864_ = v___x_3934_;
goto v___jp_3863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v_b_3857_);
lean_dec_ref(v___x_3851_);
lean_dec_ref(v_xs_3850_);
v_a_3940_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3878_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3878_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
v___jp_3863_:
{
size_t v___x_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_add(v_i_3856_, v___x_3865_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_3851_, v_values_3852_, v_xs_3850_, v_fnNames_3853_, v_as_3854_, v_sz_3855_, v___x_3866_, v_a_3864_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(lean_object* v_xs_3948_, lean_object* v___x_3949_, lean_object* v_values_3950_, lean_object* v_fnNames_3951_, lean_object* v_as_3952_, lean_object* v_sz_3953_, lean_object* v_i_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
size_t v_sz_boxed_3961_; size_t v_i_boxed_3962_; lean_object* v_res_3963_; 
v_sz_boxed_3961_ = lean_unbox_usize(v_sz_3953_);
lean_dec(v_sz_3953_);
v_i_boxed_3962_ = lean_unbox_usize(v_i_3954_);
lean_dec(v_i_3954_);
v_res_3963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3948_, v___x_3949_, v_values_3950_, v_fnNames_3951_, v_as_3952_, v_sz_boxed_3961_, v_i_boxed_3962_, v_b_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec_ref(v_as_3952_);
lean_dec_ref(v_fnNames_3951_);
lean_dec_ref(v_values_3950_);
return v_res_3963_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__1));
v___x_3968_ = l_Lean_MessageData_ofFormat(v___x_3967_);
return v___x_3968_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__3));
v___x_3971_ = l_Lean_stringToMessageData(v___x_3970_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7(void){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__6));
v___x_3976_ = l_Lean_stringToMessageData(v___x_3975_);
return v___x_3976_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8(void){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_box(1);
v___x_3978_ = l_Lean_MessageData_ofFormat(v___x_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_findRecArgCandidates(lean_object* v_fnNames_3979_, lean_object* v_fixedParamPerms_3980_, lean_object* v_xs_3981_, lean_object* v_values_3982_, lean_object* v_termMeasure_x3fs_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v___x_3989_; lean_object* v_recArgInfoss_3990_; lean_object* v___x_3991_; lean_object* v_perms_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_report_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; size_t v_sz_4003_; size_t v___x_4004_; lean_object* v___x_4005_; 
v___x_3989_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0));
v___x_3991_ = lean_array_get_size(v_values_3982_);
v_perms_3992_ = lean_ctor_get(v_fixedParamPerms_3980_, 1);
lean_inc_ref(v_perms_3992_);
lean_dec_ref(v_fixedParamPerms_3980_);
lean_inc_ref(v_values_3982_);
v___x_3993_ = l_Array_toSubarray___redArg(v_values_3982_, v___x_3989_, v___x_3991_);
v___x_3994_ = lean_array_get_size(v_termMeasure_x3fs_3983_);
v_report_3995_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_3996_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_3983_, v___x_3989_, v___x_3994_);
v___x_3997_ = lean_array_get_size(v_perms_3992_);
v___x_3998_ = l_Array_toSubarray___redArg(v_perms_3992_, v___x_3989_, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3996_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3993_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v_recArgInfoss_3990_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v_report_3995_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v_sz_4003_ = lean_array_size(v_fnNames_3979_);
v___x_4004_ = ((size_t)0ULL);
lean_inc_ref(v_xs_3981_);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_3981_, v_fnNames_3979_, v_sz_4003_, v___x_4004_, v___x_4002_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v_snd_4007_; lean_object* v_options_4008_; lean_object* v_fst_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4146_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v_snd_4007_ = lean_ctor_get(v_a_4006_, 1);
lean_inc(v_snd_4007_);
v_options_4008_ = lean_ctor_get(v_a_3986_, 2);
v_fst_4009_ = lean_ctor_get(v_a_4006_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_a_4006_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_a_4006_, 1);
lean_dec(v_unused_4147_);
v___x_4011_ = v_a_4006_;
v_isShared_4012_ = v_isSharedCheck_4146_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_fst_4009_);
lean_dec(v_a_4006_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4146_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v_fst_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4144_; 
v_fst_4013_ = lean_ctor_get(v_snd_4007_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_snd_4007_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_snd_4007_, 1);
lean_dec(v_unused_4145_);
v___x_4015_ = v_snd_4007_;
v_isShared_4016_ = v_isSharedCheck_4144_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_fst_4013_);
lean_dec(v_snd_4007_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4144_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v_inheritedTraceOptions_4017_; uint8_t v_hasTrace_4018_; size_t v_sz_4019_; lean_object* v___x_4020_; lean_object* v___y_4022_; lean_object* v_report_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___x_4070_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; 
v_inheritedTraceOptions_4017_ = lean_ctor_get(v_a_3986_, 13);
v_hasTrace_4018_ = lean_ctor_get_uint8(v_options_4008_, sizeof(void*)*1);
v_sz_4019_ = lean_array_size(v_fst_4013_);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_4019_, v___x_4004_, v_fst_4013_);
v___x_4070_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
if (v_hasTrace_4018_ == 0)
{
v___y_4109_ = v_a_3984_;
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4017_, v_options_4008_, v___x_4118_);
if (v___x_4119_ == 0)
{
v___y_4109_ = v_a_3984_;
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4120_; lean_object* v___y_4122_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4120_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__7, &l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7);
v___x_4139_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4140_ = lean_array_get_size(v___x_4020_);
v___x_4141_ = lean_nat_dec_lt(v___x_3989_, v___x_4140_);
if (v___x_4141_ == 0)
{
v___y_4122_ = v___x_4139_;
goto v___jp_4121_;
}
else
{
size_t v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_usize_of_nat(v___x_4140_);
v___x_4143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4020_, v___x_4004_, v___x_4142_, v___x_4139_);
v___y_4122_ = v___x_4143_;
goto v___jp_4121_;
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4123_ = lean_array_to_list(v___y_4122_);
v___x_4124_ = lean_box(0);
v___x_4125_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(v___x_4123_, v___x_4124_);
v___x_4126_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__8, &l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8);
v___x_4127_ = l_Lean_MessageData_joinSep(v___x_4125_, v___x_4126_);
v___x_4128_ = l_Lean_indentD(v___x_4127_);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4120_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4070_, v___x_4129_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_dec_ref_known(v___x_4130_, 1);
v___y_4109_ = v_a_3984_;
v___y_4110_ = v_a_3985_;
v___y_4111_ = v_a_3986_;
v___y_4112_ = v_a_3987_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_4011_);
lean_dec(v_fst_4009_);
lean_dec_ref(v_values_3982_);
lean_dec_ref(v_xs_3981_);
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
}
v___jp_4021_:
{
lean_object* v___x_4029_; 
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v_recArgInfoss_3990_);
lean_ctor_set(v___x_4015_, 0, v_report_4023_);
v___x_4029_ = v___x_4015_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_report_4023_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v_recArgInfoss_3990_);
v___x_4029_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
size_t v_sz_4030_; lean_object* v___x_4031_; 
v_sz_4030_ = lean_array_size(v___y_4022_);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_3981_, v___x_4020_, v_values_3982_, v_fnNames_3979_, v___y_4022_, v_sz_4030_, v___x_4004_, v___x_4029_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec_ref(v___y_4022_);
lean_dec_ref(v_values_3982_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4048_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4048_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4048_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v_fst_4036_; lean_object* v_snd_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4047_; 
v_fst_4036_ = lean_ctor_get(v_a_4032_, 0);
v_snd_4037_ = lean_ctor_get(v_a_4032_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_a_4032_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4039_ = v_a_4032_;
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_snd_4037_);
lean_inc(v_fst_4036_);
lean_dec(v_a_4032_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v_fst_4036_);
lean_ctor_set(v___x_4039_, 0, v_snd_4037_);
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_snd_4037_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_fst_4036_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4042_);
v___x_4044_ = v___x_4034_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4031_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4031_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
v___jp_4058_:
{
lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4064_ = lean_array_get_size(v___y_4059_);
v___x_4065_ = lean_nat_dec_eq(v___x_4064_, v___x_3989_);
if (v___x_4065_ == 0)
{
lean_del_object(v___x_4011_);
v___y_4022_ = v___y_4059_;
v_report_4023_ = v_fst_4009_;
v___y_4024_ = v___y_4060_;
v___y_4025_ = v___y_4061_;
v___y_4026_ = v___y_4062_;
v___y_4027_ = v___y_4063_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__2, &l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2);
if (v_isShared_4012_ == 0)
{
lean_ctor_set_tag(v___x_4011_, 7);
lean_ctor_set(v___x_4011_, 1, v___x_4066_);
v___x_4068_ = v___x_4011_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_fst_4009_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
v___y_4022_ = v___y_4059_;
v_report_4023_ = v___x_4068_;
v___y_4024_ = v___y_4060_;
v___y_4025_ = v___y_4061_;
v___y_4026_ = v___y_4062_;
v___y_4027_ = v___y_4063_;
goto v___jp_4021_;
}
}
}
v___jp_4071_:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4076_, v___y_4073_, v___y_4075_, v___y_4072_, v___y_4074_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_options_4078_; uint8_t v_hasTrace_4079_; 
v_options_4078_ = lean_ctor_get(v___y_4072_, 2);
v_hasTrace_4079_ = lean_ctor_get_uint8(v_options_4078_, sizeof(void*)*1);
if (v_hasTrace_4079_ == 0)
{
lean_object* v_a_4080_; 
v_a_4080_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4077_, 1);
v___y_4059_ = v_a_4080_;
v___y_4060_ = v___y_4073_;
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4072_;
v___y_4063_ = v___y_4074_;
goto v___jp_4058_;
}
else
{
lean_object* v_a_4081_; lean_object* v_inheritedTraceOptions_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v_a_4081_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4077_, 1);
v_inheritedTraceOptions_4082_ = lean_ctor_get(v___y_4072_, 13);
v___x_4083_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12);
v___x_4084_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4082_, v_options_4078_, v___x_4083_);
if (v___x_4084_ == 0)
{
v___y_4059_ = v_a_4081_;
v___y_4060_ = v___y_4073_;
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4072_;
v___y_4063_ = v___y_4074_;
goto v___jp_4058_;
}
else
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4085_ = lean_obj_once(&l_Lean_Elab_Structural_findRecArgCandidates___closed__4, &l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once, _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4);
lean_inc(v_a_4081_);
v___x_4086_ = lean_array_to_list(v_a_4081_);
v___x_4087_ = lean_box(0);
v___x_4088_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_4086_, v___x_4087_);
v___x_4089_ = l_Lean_MessageData_ofList(v___x_4088_);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4085_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_4070_, v___x_4090_, v___y_4073_, v___y_4075_, v___y_4072_, v___y_4074_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_dec_ref_known(v___x_4091_, 1);
v___y_4059_ = v_a_4081_;
v___y_4060_ = v___y_4073_;
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4072_;
v___y_4063_ = v___y_4074_;
goto v___jp_4058_;
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_a_4081_);
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_4011_);
lean_dec(v_fst_4009_);
lean_dec_ref(v_values_3982_);
lean_dec_ref(v_xs_3981_);
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_4011_);
lean_dec(v_fst_4009_);
lean_dec_ref(v_values_3982_);
lean_dec_ref(v_xs_3981_);
v_a_4100_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4077_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4077_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
v___jp_4108_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Structural_findRecArgCandidates___closed__5));
v___x_4114_ = lean_array_get_size(v___x_4020_);
v___x_4115_ = lean_nat_dec_lt(v___x_3989_, v___x_4114_);
if (v___x_4115_ == 0)
{
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4109_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4110_;
v___y_4076_ = v___x_4113_;
goto v___jp_4071_;
}
else
{
size_t v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_usize_of_nat(v___x_4114_);
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_4020_, v___x_4004_, v___x_4116_, v___x_4113_);
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4109_;
v___y_4074_ = v___y_4112_;
v___y_4075_ = v___y_4110_;
v___y_4076_ = v___x_4117_;
goto v___jp_4071_;
}
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v_values_3982_);
lean_dec_ref(v_xs_3981_);
v_a_4148_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4005_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4005_);
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
lean_dec_ref_known(v___x_4229_, 1);
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
lean_dec_ref_known(v___x_4231_, 1);
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
lean_dec_ref_known(v___x_4301_, 1);
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
lean_dec_ref_known(v___x_4309_, 1);
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
uint8_t v___x_4291__boxed_4338_; lean_object* v_res_4339_; 
v___x_4291__boxed_4338_ = lean_unbox(v___x_4329_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_4328_, v___x_4291__boxed_4338_, v_group_4330_, v_k_4331_, v_comb_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
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
lean_dec_ref_known(v___x_4395_, 1);
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
lean_dec_ref_known(v___x_4497_, 1);
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
lean_dec_ref_known(v_fst_4479_, 1);
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
