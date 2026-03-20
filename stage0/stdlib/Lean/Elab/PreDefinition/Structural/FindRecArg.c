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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_numMotives(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInst_toMessageData(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "tryAllArgs report:\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Cannot use "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "the type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = " does not have a `.brecOn` recursor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Skipping arguments of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", as "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " has no compatible argument.\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Too many possible combinations of parameters of type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " (or "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "please indicate the recursive argument explicitly using `termination_by structural`).\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "failed to infer structural recursion:\n"};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tryAllArgs:\n"};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "no parameters suitable for structural recursion"};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6;
static const lean_string_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inductive groups: "};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8;
static const lean_array_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_Structural_tryAllArgs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "recArgInfos:"};
static const lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_a_28_);
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
lean_dec_ref(v_a_28_);
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
lean_dec_ref(v_a_28_);
return v___x_48_;
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
lean_dec_ref(v_a_28_);
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
lean_dec(v_i_58_);
lean_dec_ref(v_xs_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(lean_object* v_k_65_, lean_object* v_b_66_, lean_object* v_c_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_7(v_k_65_, v_b_66_, v_c_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(lean_object* v_k_74_, lean_object* v_b_75_, lean_object* v_c_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_74_, v_b_75_, v_c_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
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
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
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
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
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
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
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
lean_inc(v___y_196_);
lean_inc_ref(v___y_195_);
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
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
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
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
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v___x_648_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
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
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
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
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
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
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v___x_711_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
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
lean_object* v___f_969_; lean_object* v___x_6921__overap_970_; lean_object* v___x_971_; 
v___f_969_ = ((lean_object*)(l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0));
v___x_6921__overap_970_ = lean_panic_fn(v___f_969_, v_msg_963_);
v___x_971_ = lean_apply_5(v___x_6921__overap_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, lean_box(0));
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v_msg_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
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
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
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
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
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
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v___x_1207_;
}
v___jp_1208_:
{
uint8_t v___x_1220_; 
v___x_1220_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v___y_1217_);
if (v___x_1220_ == 0)
{
lean_object* v_name_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1212_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v_name_1221_ = lean_ctor_get(v___y_1210_, 0);
lean_inc(v_name_1221_);
lean_dec_ref(v___y_1210_);
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__3, &l_Lean_Elab_Structural_getRecArgInfo___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3);
v___x_1223_ = l_Lean_MessageData_ofName(v_name_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__5, &l_Lean_Elab_Structural_getRecArgInfo___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_indentExpr(v___y_1215_);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1228_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1209_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_1193_, v_xs_1194_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1209_);
v___x_1231_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_1230_, v___y_1217_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_1230_, v___y_1219_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
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
lean_dec_ref(v___y_1215_);
v_name_1238_ = lean_ctor_get(v___y_1210_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___y_1210_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v___y_1210_, 2);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v___y_1210_, 1);
lean_dec(v_unused_1260_);
v___x_1240_ = v___y_1210_;
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_name_1238_);
lean_dec(v___y_1210_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_array_mk(v___y_1214_);
v___x_1243_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(v___x_1242_, v_name_1238_);
lean_dec(v_name_1238_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec(v___y_1218_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1209_);
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1243_);
v_sz_1245_ = lean_array_size(v___y_1217_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_1194_, v_sz_1245_, v___x_1246_, v___y_1217_);
v___x_1248_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_1212_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 2, v___y_1219_);
lean_ctor_set(v___x_1240_, 1, v___y_1216_);
lean_ctor_set(v___x_1240_, 0, v___x_1248_);
v___x_1250_ = v___x_1240_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___y_1216_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___y_1219_);
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
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1212_);
lean_dec(v_i_1195_);
lean_dec_ref(v_fixedParamPerm_1193_);
lean_dec(v_fnName_1192_);
v___x_1256_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfo___closed__7, &l_Lean_Elab_Structural_getRecArgInfo___closed__7_once, _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7);
v___x_1257_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(v___x_1256_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
return v___x_1257_;
}
}
}
else
{
lean_object* v_val_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1236_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1210_);
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
v___x_1268_ = l_Lean_indentExpr(v___y_1215_);
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
v___x_1281_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1280_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1209_);
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
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
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
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1212_);
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
v_name_1299_ = lean_ctor_get(v___y_1210_, 0);
lean_inc(v_name_1299_);
lean_dec_ref(v___y_1210_);
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
v___x_1306_ = l_Lean_indentExpr(v___y_1215_);
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
v___x_1316_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1315_, v___y_1209_, v___y_1218_, v___y_1211_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1209_);
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
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
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
v___x_1342_ = l_Array_toSubarray___redArg(v___y_1330_, v_lower_1340_, v_upper_1341_);
v___x_1343_ = l_Subarray_copy___redArg(v___x_1342_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_nat_dec_lt(v___y_1331_, v___x_1344_);
lean_dec(v___y_1331_);
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1329_;
v___y_1211_ = v___y_1333_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1332_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___x_1343_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
if (v___x_1345_ == 0)
{
v___y_1209_ = v___y_1328_;
v___y_1210_ = v___y_1329_;
v___y_1211_ = v___y_1333_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1332_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___x_1343_;
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
v___y_1210_ = v___y_1329_;
v___y_1211_ = v___y_1333_;
v___y_1212_ = v___y_1334_;
v___y_1213_ = v___y_1335_;
v___y_1214_ = v___y_1336_;
v___y_1215_ = v___y_1332_;
v___y_1216_ = v___y_1337_;
v___y_1217_ = v___x_1343_;
v___y_1218_ = v___y_1338_;
v___y_1219_ = v___y_1339_;
goto v___jp_1208_;
}
else
{
lean_object* v_name_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1334_);
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
v___x_1355_ = l_Lean_indentExpr(v___y_1332_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_1356_, v___y_1328_, v___y_1338_, v___y_1333_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1328_);
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
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
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
v___y_1328_ = v___y_1360_;
v___y_1329_ = v_toConstantVal_1376_;
v___y_1330_ = v___x_1384_;
v___y_1331_ = v___x_1385_;
v___y_1332_ = v_a_1366_;
v___y_1333_ = v___y_1362_;
v___y_1334_ = v_val_1375_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v_all_1378_;
v___y_1337_ = v_us_1369_;
v___y_1338_ = v___y_1361_;
v___y_1339_ = v___x_1387_;
v_lower_1340_ = v_numParams_1377_;
v_upper_1341_ = v___x_1388_;
goto v___jp_1327_;
}
else
{
v___y_1328_ = v___y_1360_;
v___y_1329_ = v_toConstantVal_1376_;
v___y_1330_ = v___x_1384_;
v___y_1331_ = v___x_1385_;
v___y_1332_ = v_a_1366_;
v___y_1333_ = v___y_1362_;
v___y_1334_ = v_val_1375_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v_all_1378_;
v___y_1337_ = v_us_1369_;
v___y_1338_ = v___y_1361_;
v___y_1339_ = v___x_1387_;
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
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
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
lean_inc_ref(v___y_1399_);
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
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
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
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
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
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
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
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
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
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
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
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
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
lean_inc_ref(v___y_1581_);
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
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
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
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
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
lean_object* v_val_1752_; lean_object* v_ref_1753_; lean_object* v_fileName_1754_; lean_object* v_fileMap_1755_; lean_object* v_options_1756_; lean_object* v_currRecDepth_1757_; lean_object* v_maxRecDepth_1758_; lean_object* v_ref_1759_; lean_object* v_currNamespace_1760_; lean_object* v_openDecls_1761_; lean_object* v_initHeartbeats_1762_; lean_object* v_maxHeartbeats_1763_; lean_object* v_quotContext_1764_; lean_object* v_currMacroScope_1765_; uint8_t v_diag_1766_; lean_object* v_cancelTk_x3f_1767_; uint8_t v_suppressElabErrors_1768_; lean_object* v_inheritedTraceOptions_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1802_; 
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
v_isSharedCheck_1802_ = !lean_is_exclusive(v___y_1749_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1771_ = v___y_1749_;
v_isShared_1772_ = v_isSharedCheck_1802_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_inheritedTraceOptions_1769_);
lean_inc(v_cancelTk_x3f_1767_);
lean_inc(v_currMacroScope_1765_);
lean_inc(v_quotContext_1764_);
lean_inc(v_maxHeartbeats_1763_);
lean_inc(v_initHeartbeats_1762_);
lean_inc(v_openDecls_1761_);
lean_inc(v_currNamespace_1760_);
lean_inc(v_ref_1759_);
lean_inc(v_maxRecDepth_1758_);
lean_inc(v_currRecDepth_1757_);
lean_inc(v_options_1756_);
lean_inc(v_fileMap_1755_);
lean_inc(v_fileName_1754_);
lean_dec(v___y_1749_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1802_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___f_1773_; lean_object* v_args_1774_; lean_object* v___f_1775_; lean_object* v_ref_1776_; lean_object* v___x_1778_; 
v___f_1773_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2);
lean_inc_ref(v_fixedParamPerm_1742_);
v_args_1774_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1742_, v_xs_1743_, v_ys_1745_);
v___f_1775_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1775_, 0, v_val_1752_);
lean_closure_set(v___f_1775_, 1, v_fnName_1744_);
lean_closure_set(v___f_1775_, 2, v_fixedParamPerm_1742_);
lean_closure_set(v___f_1775_, 3, v_args_1774_);
v_ref_1776_ = l_Lean_replaceRef(v_ref_1753_, v_ref_1759_);
lean_dec(v_ref_1759_);
lean_dec(v_ref_1753_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 5, v_ref_1776_);
v___x_1778_ = v___x_1771_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_fileName_1754_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_fileMap_1755_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_options_1756_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_currRecDepth_1757_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_maxRecDepth_1758_);
lean_ctor_set(v_reuseFailAlloc_1801_, 5, v_ref_1776_);
lean_ctor_set(v_reuseFailAlloc_1801_, 6, v_currNamespace_1760_);
lean_ctor_set(v_reuseFailAlloc_1801_, 7, v_openDecls_1761_);
lean_ctor_set(v_reuseFailAlloc_1801_, 8, v_initHeartbeats_1762_);
lean_ctor_set(v_reuseFailAlloc_1801_, 9, v_maxHeartbeats_1763_);
lean_ctor_set(v_reuseFailAlloc_1801_, 10, v_quotContext_1764_);
lean_ctor_set(v_reuseFailAlloc_1801_, 11, v_currMacroScope_1765_);
lean_ctor_set(v_reuseFailAlloc_1801_, 12, v_cancelTk_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1801_, 13, v_inheritedTraceOptions_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1801_, sizeof(void*)*14, v_diag_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1801_, sizeof(void*)*14 + 1, v_suppressElabErrors_1768_);
v___x_1778_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1775_, v___f_1773_, v___y_1747_, v___y_1748_, v___x_1778_, v___y_1750_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1792_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_mk_empty_array_with_capacity(v___x_1784_);
v___x_1786_ = lean_array_push(v___x_1785_, v_a_1780_);
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1788_);
v___x_1790_ = v___x_1782_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1779_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1779_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
else
{
lean_object* v_args_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v_termMeasure_x3f_1741_);
lean_inc_ref(v_fixedParamPerm_1742_);
v_args_1803_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_1742_, v_xs_1743_, v_ys_1745_);
v___x_1804_ = lean_array_get_size(v_args_1803_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
v___x_1807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(v___x_1804_, v_fnName_1744_, v_fixedParamPerm_1742_, v_args_1803_, v___x_1805_, v___x_1806_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v_args_1803_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1840_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_1810_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg(v___x_1809_, v___y_1749_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1840_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1840_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1839_; 
v_fst_1815_ = lean_ctor_get(v_a_1808_, 0);
v_snd_1816_ = lean_ctor_get(v_a_1808_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1808_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1818_ = v_a_1808_;
v_isShared_1819_ = v_isSharedCheck_1839_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_inc(v_fst_1815_);
lean_dec(v_a_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1839_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_unbox(v_a_1811_);
lean_dec(v_a_1811_);
if (v___x_1827_ == 0)
{
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
goto v___jp_1820_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11);
lean_inc(v_snd_1816_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_snd_1816_);
v___x_1830_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(v___x_1809_, v___x_1829_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_dec_ref(v___x_1830_);
goto v___jp_1820_;
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_fst_1815_);
lean_del_object(v___x_1813_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; 
if (v_isShared_1819_ == 0)
{
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_snd_1816_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1822_);
v___x_1824_ = v___x_1813_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
}
else
{
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(lean_object* v_termMeasure_x3f_1841_, lean_object* v_fixedParamPerm_1842_, lean_object* v_xs_1843_, lean_object* v_fnName_1844_, lean_object* v_ys_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(v_termMeasure_x3f_1841_, v_fixedParamPerm_1842_, v_xs_1843_, v_fnName_1844_, v_ys_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec_ref(v_x_1846_);
lean_dec_ref(v_xs_1843_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos(lean_object* v_fnName_1853_, lean_object* v_fixedParamPerm_1854_, lean_object* v_xs_1855_, lean_object* v_value_1856_, lean_object* v_termMeasure_x3f_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___f_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1863_, 0, v_termMeasure_x3f_1857_);
lean_closure_set(v___f_1863_, 1, v_fixedParamPerm_1854_);
lean_closure_set(v___f_1863_, 2, v_xs_1855_);
lean_closure_set(v___f_1863_, 3, v_fnName_1853_);
v___x_1864_ = 0;
v___x_1865_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_1856_, v___f_1863_, v___x_1864_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getRecArgInfos___boxed(lean_object* v_fnName_1866_, lean_object* v_fixedParamPerm_1867_, lean_object* v_xs_1868_, lean_object* v_value_1869_, lean_object* v_termMeasure_x3f_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Elab_Structural_getRecArgInfos(v_fnName_1866_, v_fixedParamPerm_1867_, v_xs_1868_, v_value_1869_, v_termMeasure_x3f_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2(lean_object* v_upperBound_1877_, lean_object* v_fnName_1878_, lean_object* v_fixedParamPerm_1879_, lean_object* v_args_1880_, lean_object* v_inst_1881_, lean_object* v_R_1882_, lean_object* v_a_1883_, lean_object* v_b_1884_, lean_object* v_c_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg(v_upperBound_1877_, v_fnName_1878_, v_fixedParamPerm_1879_, v_args_1880_, v_a_1883_, v_b_1884_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___boxed(lean_object* v_upperBound_1892_, lean_object* v_fnName_1893_, lean_object* v_fixedParamPerm_1894_, lean_object* v_args_1895_, lean_object* v_inst_1896_, lean_object* v_R_1897_, lean_object* v_a_1898_, lean_object* v_b_1899_, lean_object* v_c_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2(v_upperBound_1892_, v_fnName_1893_, v_fixedParamPerm_1894_, v_args_1895_, v_inst_1896_, v_R_1897_, v_a_1898_, v_b_1899_, v_c_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec_ref(v_args_1895_);
lean_dec(v_upperBound_1892_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
return v_x_1907_;
}
else
{
lean_object* v_key_1909_; lean_object* v_value_1910_; lean_object* v_tail_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1934_; 
v_key_1909_ = lean_ctor_get(v_x_1908_, 0);
v_value_1910_ = lean_ctor_get(v_x_1908_, 1);
v_tail_1911_ = lean_ctor_get(v_x_1908_, 2);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1913_ = v_x_1908_;
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_tail_1911_);
lean_inc(v_value_1910_);
lean_inc(v_key_1909_);
lean_dec(v_x_1908_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; uint64_t v___x_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v_fold_1919_; uint64_t v___x_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1915_ = lean_array_get_size(v_x_1907_);
v___x_1916_ = lean_uint64_of_nat(v_key_1909_);
v___x_1917_ = 32ULL;
v___x_1918_ = lean_uint64_shift_right(v___x_1916_, v___x_1917_);
v_fold_1919_ = lean_uint64_xor(v___x_1916_, v___x_1918_);
v___x_1920_ = 16ULL;
v___x_1921_ = lean_uint64_shift_right(v_fold_1919_, v___x_1920_);
v___x_1922_ = lean_uint64_xor(v_fold_1919_, v___x_1921_);
v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
v___x_1924_ = lean_usize_of_nat(v___x_1915_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_sub(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_usize_land(v___x_1923_, v___x_1926_);
v___x_1928_ = lean_array_uget_borrowed(v_x_1907_, v___x_1927_);
lean_inc(v___x_1928_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 2, v___x_1928_);
v___x_1930_ = v___x_1913_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_key_1909_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_value_1910_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_array_uset(v_x_1907_, v___x_1927_, v___x_1930_);
v_x_1907_ = v___x_1931_;
v_x_1908_ = v_tail_1911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1935_, lean_object* v_source_1936_, lean_object* v_target_1937_){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_get_size(v_source_1936_);
v___x_1939_ = lean_nat_dec_lt(v_i_1935_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec_ref(v_source_1936_);
lean_dec(v_i_1935_);
return v_target_1937_;
}
else
{
lean_object* v_es_1940_; lean_object* v___x_1941_; lean_object* v_source_1942_; lean_object* v_target_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_es_1940_ = lean_array_fget(v_source_1936_, v_i_1935_);
v___x_1941_ = lean_box(0);
v_source_1942_ = lean_array_fset(v_source_1936_, v_i_1935_, v___x_1941_);
v_target_1943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_1937_, v_es_1940_);
v___x_1944_ = lean_unsigned_to_nat(1u);
v___x_1945_ = lean_nat_add(v_i_1935_, v___x_1944_);
lean_dec(v_i_1935_);
v_i_1935_ = v___x_1945_;
v_source_1936_ = v_source_1942_;
v_target_1937_ = v_target_1943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(lean_object* v_data_1947_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_nbuckets_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1948_ = lean_array_get_size(v_data_1947_);
v___x_1949_ = lean_unsigned_to_nat(2u);
v_nbuckets_1950_ = lean_nat_mul(v___x_1948_, v___x_1949_);
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_mk_array(v_nbuckets_1950_, v___x_1952_);
v___x_1954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_1951_, v_data_1947_, v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(lean_object* v_a_1955_, lean_object* v_x_1956_){
_start:
{
if (lean_obj_tag(v_x_1956_) == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = 0;
return v___x_1957_;
}
else
{
lean_object* v_key_1958_; lean_object* v_tail_1959_; uint8_t v___x_1960_; 
v_key_1958_ = lean_ctor_get(v_x_1956_, 0);
v_tail_1959_ = lean_ctor_get(v_x_1956_, 2);
v___x_1960_ = lean_nat_dec_eq(v_key_1958_, v_a_1955_);
if (v___x_1960_ == 0)
{
v_x_1956_ = v_tail_1959_;
goto _start;
}
else
{
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(lean_object* v_a_1962_, lean_object* v_x_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1962_, v_x_1963_);
lean_dec(v_x_1963_);
lean_dec(v_a_1962_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(lean_object* v_m_1966_, lean_object* v_a_1967_, lean_object* v_b_1968_){
_start:
{
lean_object* v_size_1969_; lean_object* v_buckets_1970_; lean_object* v___x_1971_; uint64_t v___x_1972_; uint64_t v___x_1973_; uint64_t v___x_1974_; uint64_t v_fold_1975_; uint64_t v___x_1976_; uint64_t v___x_1977_; uint64_t v___x_1978_; size_t v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; lean_object* v_bkt_1984_; uint8_t v___x_1985_; 
v_size_1969_ = lean_ctor_get(v_m_1966_, 0);
v_buckets_1970_ = lean_ctor_get(v_m_1966_, 1);
v___x_1971_ = lean_array_get_size(v_buckets_1970_);
v___x_1972_ = lean_uint64_of_nat(v_a_1967_);
v___x_1973_ = 32ULL;
v___x_1974_ = lean_uint64_shift_right(v___x_1972_, v___x_1973_);
v_fold_1975_ = lean_uint64_xor(v___x_1972_, v___x_1974_);
v___x_1976_ = 16ULL;
v___x_1977_ = lean_uint64_shift_right(v_fold_1975_, v___x_1976_);
v___x_1978_ = lean_uint64_xor(v_fold_1975_, v___x_1977_);
v___x_1979_ = lean_uint64_to_usize(v___x_1978_);
v___x_1980_ = lean_usize_of_nat(v___x_1971_);
v___x_1981_ = ((size_t)1ULL);
v___x_1982_ = lean_usize_sub(v___x_1980_, v___x_1981_);
v___x_1983_ = lean_usize_land(v___x_1979_, v___x_1982_);
v_bkt_1984_ = lean_array_uget_borrowed(v_buckets_1970_, v___x_1983_);
v___x_1985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_1967_, v_bkt_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2006_; 
lean_inc_ref(v_buckets_1970_);
lean_inc(v_size_1969_);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_m_1966_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2007_ = lean_ctor_get(v_m_1966_, 1);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_m_1966_, 0);
lean_dec(v_unused_2008_);
v___x_1987_ = v_m_1966_;
v_isShared_1988_ = v_isSharedCheck_2006_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_m_1966_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2006_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v_size_x27_1990_; lean_object* v___x_1991_; lean_object* v_buckets_x27_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v_size_x27_1990_ = lean_nat_add(v_size_1969_, v___x_1989_);
lean_dec(v_size_1969_);
lean_inc(v_bkt_1984_);
v___x_1991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1991_, 0, v_a_1967_);
lean_ctor_set(v___x_1991_, 1, v_b_1968_);
lean_ctor_set(v___x_1991_, 2, v_bkt_1984_);
v_buckets_x27_1992_ = lean_array_uset(v_buckets_1970_, v___x_1983_, v___x_1991_);
v___x_1993_ = lean_unsigned_to_nat(4u);
v___x_1994_ = lean_nat_mul(v_size_x27_1990_, v___x_1993_);
v___x_1995_ = lean_unsigned_to_nat(3u);
v___x_1996_ = lean_nat_div(v___x_1994_, v___x_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_array_get_size(v_buckets_x27_1992_);
v___x_1998_ = lean_nat_dec_le(v___x_1996_, v___x_1997_);
lean_dec(v___x_1996_);
if (v___x_1998_ == 0)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; 
v_val_1999_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_1992_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_val_1999_);
lean_ctor_set(v___x_1987_, 0, v_size_x27_1990_);
v___x_2001_ = v___x_1987_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_size_x27_1990_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_val_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v___x_2004_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_buckets_x27_1992_);
lean_ctor_set(v___x_1987_, 0, v_size_x27_1990_);
v___x_2004_ = v___x_1987_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_size_x27_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_buckets_x27_1992_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_dec(v_b_1968_);
lean_dec(v_a_1967_);
return v_m_1966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2013_ == 0)
{
return v_b_2012_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v_a_2014_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
v___x_2015_ = lean_box(0);
lean_inc(v_a_2014_);
v___x_2016_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_2012_, v_a_2014_, v___x_2015_);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2011_, v___x_2017_);
v_i_2011_ = v___x_2018_;
v_b_2012_ = v___x_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_){
_start:
{
size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_2020_, v_sz_boxed_2024_, v_i_boxed_2025_, v_b_2023_);
lean_dec_ref(v_as_2020_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(lean_object* v_as_2027_, size_t v_sz_2028_, size_t v_i_2029_, lean_object* v_b_2030_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_lt(v_i_2029_, v_sz_2028_);
if (v___x_2031_ == 0)
{
return v_b_2030_;
}
else
{
lean_object* v_a_2032_; lean_object* v_indicesPos_2033_; size_t v_sz_2034_; size_t v___x_2035_; lean_object* v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; 
v_a_2032_ = lean_array_uget_borrowed(v_as_2027_, v_i_2029_);
v_indicesPos_2033_ = lean_ctor_get(v_a_2032_, 3);
v_sz_2034_ = lean_array_size(v_indicesPos_2033_);
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_2033_, v_sz_2034_, v___x_2035_, v_b_2030_);
v___x_2037_ = ((size_t)1ULL);
v___x_2038_ = lean_usize_add(v_i_2029_, v___x_2037_);
v_i_2029_ = v___x_2038_;
v_b_2030_ = v___x_2036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(lean_object* v_as_2040_, lean_object* v_sz_2041_, lean_object* v_i_2042_, lean_object* v_b_2043_){
_start:
{
size_t v_sz_boxed_2044_; size_t v_i_boxed_2045_; lean_object* v_res_2046_; 
v_sz_boxed_2044_ = lean_unbox_usize(v_sz_2041_);
lean_dec(v_sz_2041_);
v_i_boxed_2045_ = lean_unbox_usize(v_i_2042_);
lean_dec(v_i_2042_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_2040_, v_sz_boxed_2044_, v_i_boxed_2045_, v_b_2043_);
lean_dec_ref(v_as_2040_);
return v_res_2046_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(lean_object* v_m_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_buckets_2049_; lean_object* v___x_2050_; uint64_t v___x_2051_; uint64_t v___x_2052_; uint64_t v___x_2053_; uint64_t v_fold_2054_; uint64_t v___x_2055_; uint64_t v___x_2056_; uint64_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_buckets_2049_ = lean_ctor_get(v_m_2047_, 1);
v___x_2050_ = lean_array_get_size(v_buckets_2049_);
v___x_2051_ = lean_uint64_of_nat(v_a_2048_);
v___x_2052_ = 32ULL;
v___x_2053_ = lean_uint64_shift_right(v___x_2051_, v___x_2052_);
v_fold_2054_ = lean_uint64_xor(v___x_2051_, v___x_2053_);
v___x_2055_ = 16ULL;
v___x_2056_ = lean_uint64_shift_right(v_fold_2054_, v___x_2055_);
v___x_2057_ = lean_uint64_xor(v_fold_2054_, v___x_2056_);
v___x_2058_ = lean_uint64_to_usize(v___x_2057_);
v___x_2059_ = lean_usize_of_nat(v___x_2050_);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_sub(v___x_2059_, v___x_2060_);
v___x_2062_ = lean_usize_land(v___x_2058_, v___x_2061_);
v___x_2063_ = lean_array_uget_borrowed(v_buckets_2049_, v___x_2062_);
v___x_2064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2048_, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(lean_object* v_m_2065_, lean_object* v_a_2066_){
_start:
{
uint8_t v_res_2067_; lean_object* v_r_2068_; 
v_res_2067_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_m_2065_);
v_r_2068_ = lean_box(v_res_2067_);
return v_r_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(lean_object* v___x_2069_, lean_object* v_as_2070_, size_t v_sz_2071_, size_t v_i_2072_, lean_object* v_b_2073_){
_start:
{
lean_object* v_a_2075_; uint8_t v___x_2079_; 
v___x_2079_ = lean_usize_dec_lt(v_i_2072_, v_sz_2071_);
if (v___x_2079_ == 0)
{
return v_b_2073_;
}
else
{
lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2096_; 
v_fst_2080_ = lean_ctor_get(v_b_2073_, 0);
v_snd_2081_ = lean_ctor_get(v_b_2073_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_b_2073_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2083_ = v_b_2073_;
v_isShared_2084_ = v_isSharedCheck_2096_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_inc(v_fst_2080_);
lean_dec(v_b_2073_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2096_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_a_2085_; lean_object* v_recArgPos_2086_; uint8_t v___x_2087_; 
v_a_2085_ = lean_array_uget_borrowed(v_as_2070_, v_i_2072_);
v_recArgPos_2086_ = lean_ctor_get(v_a_2085_, 2);
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_2069_, v_recArgPos_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_inc(v_a_2085_);
v___x_2088_ = lean_array_push(v_snd_2081_, v_a_2085_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2088_);
v___x_2090_ = v___x_2083_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_fst_2080_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_a_2075_ = v___x_2090_;
goto v___jp_2074_;
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
lean_inc(v_a_2085_);
v___x_2092_ = lean_array_push(v_fst_2080_, v_a_2085_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2092_);
v___x_2094_ = v___x_2083_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_snd_2081_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
v_a_2075_ = v___x_2094_;
goto v___jp_2074_;
}
}
}
}
v___jp_2074_:
{
size_t v___x_2076_; size_t v___x_2077_; 
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2072_, v___x_2076_);
v_i_2072_ = v___x_2077_;
v_b_2073_ = v_a_2075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(lean_object* v___x_2097_, lean_object* v_as_2098_, lean_object* v_sz_2099_, lean_object* v_i_2100_, lean_object* v_b_2101_){
_start:
{
size_t v_sz_boxed_2102_; size_t v_i_boxed_2103_; lean_object* v_res_2104_; 
v_sz_boxed_2102_ = lean_unbox_usize(v_sz_2099_);
lean_dec(v_sz_2099_);
v_i_boxed_2103_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_res_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2097_, v_as_2098_, v_sz_boxed_2102_, v_i_boxed_2103_, v_b_2101_);
lean_dec_ref(v_as_2098_);
lean_dec_ref(v___x_2097_);
return v_res_2104_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_unsigned_to_nat(16u);
v___x_2107_ = lean_mk_array(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_indicesPos_2110_; 
v___x_2108_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__0, &l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0);
v___x_2109_ = lean_unsigned_to_nat(0u);
v_indicesPos_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_indicesPos_2110_, 0, v___x_2109_);
lean_ctor_set(v_indicesPos_2110_, 1, v___x_2108_);
return v_indicesPos_2110_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__2(void){
_start:
{
lean_object* v_bs_2111_; lean_object* v___x_2112_; 
v_bs_2111_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_bs_2111_);
lean_ctor_set(v___x_2112_, 1, v_bs_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst(lean_object* v_recArgInfos_2113_){
_start:
{
lean_object* v_indicesPos_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_fst_2120_; lean_object* v_snd_2121_; lean_object* v___x_2122_; 
v_indicesPos_2114_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__1, &l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1);
v_sz_2115_ = lean_array_size(v_recArgInfos_2113_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_2113_, v_sz_2115_, v___x_2116_, v_indicesPos_2114_);
v___x_2118_ = lean_obj_once(&l_Lean_Elab_Structural_nonIndicesFirst___closed__2, &l_Lean_Elab_Structural_nonIndicesFirst___closed__2_once, _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__2);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_2117_, v_recArgInfos_2113_, v_sz_2115_, v___x_2116_, v___x_2118_);
lean_dec_ref(v___x_2117_);
v_fst_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_fst_2120_);
v_snd_2121_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_snd_2121_);
lean_dec_ref(v___x_2119_);
v___x_2122_ = l_Array_append___redArg(v_snd_2121_, v_fst_2120_);
lean_dec(v_fst_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_nonIndicesFirst___boxed(lean_object* v_recArgInfos_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_2123_);
lean_dec_ref(v_recArgInfos_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(lean_object* v_00_u03b2_2125_, lean_object* v_m_2126_, lean_object* v_a_2127_, lean_object* v_b_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_2126_, v_a_2127_, v_b_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(lean_object* v_00_u03b2_2130_, lean_object* v_m_2131_, lean_object* v_a_2132_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_2131_, v_a_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_m_2135_, lean_object* v_a_2136_){
_start:
{
uint8_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_2134_, v_m_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_m_2135_);
v_r_2138_ = lean_box(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(lean_object* v_00_u03b2_2139_, lean_object* v_a_2140_, lean_object* v_x_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_2140_, v_x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_2143_, v_a_2144_, v_x_2145_);
lean_dec(v_x_2145_);
lean_dec(v_a_2144_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(lean_object* v_00_u03b2_2148_, lean_object* v_data_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2151_, lean_object* v_i_2152_, lean_object* v_source_2153_, lean_object* v_target_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_2152_, v_source_2153_, v_target_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_2157_, v_x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(lean_object* v___y_2160_, lean_object* v_a_2161_, lean_object* v_toPure_2162_, uint8_t v_____do__lift_2163_){
_start:
{
if (v_____do__lift_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_array_push(v___y_2160_, v_a_2161_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_apply_2(v_toPure_2162_, lean_box(0), v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_a_2161_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2160_);
v___x_2168_ = lean_apply_2(v_toPure_2162_, lean_box(0), v___x_2167_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(lean_object* v___y_2169_, lean_object* v_a_2170_, lean_object* v_toPure_2171_, lean_object* v_____do__lift_2172_){
_start:
{
uint8_t v_____do__lift_192__boxed_2173_; lean_object* v_res_2174_; 
v_____do__lift_192__boxed_2173_ = lean_unbox(v_____do__lift_2172_);
v_res_2174_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_2169_, v_a_2170_, v_toPure_2171_, v_____do__lift_192__boxed_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(lean_object* v_eq_2175_, lean_object* v_a_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_apply_2(v_eq_2175_, v_x_2177_, v_a_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(lean_object* v_toPure_2179_, lean_object* v___x_2180_, lean_object* v_toBind_2181_, lean_object* v_eq_2182_, lean_object* v_inst_2183_, lean_object* v_a_2184_, lean_object* v_x_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___f_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
lean_inc(v_toPure_2179_);
lean_inc(v_a_2184_);
lean_inc_ref(v___y_2186_);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2187_, 0, v___y_2186_);
lean_closure_set(v___f_2187_, 1, v_a_2184_);
lean_closure_set(v___f_2187_, 2, v_toPure_2179_);
v___x_2188_ = lean_array_get_size(v___y_2186_);
v___x_2189_ = lean_nat_dec_lt(v___x_2180_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v___y_2186_);
lean_dec(v_a_2184_);
lean_dec_ref(v_inst_2183_);
lean_dec(v_eq_2182_);
v___x_2190_ = lean_box(v___x_2189_);
v___x_2191_ = lean_apply_2(v_toPure_2179_, lean_box(0), v___x_2190_);
v___x_2192_ = lean_apply_4(v_toBind_2181_, lean_box(0), lean_box(0), v___x_2191_, v___f_2187_);
return v___x_2192_;
}
else
{
if (v___x_2189_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec_ref(v___y_2186_);
lean_dec(v_a_2184_);
lean_dec_ref(v_inst_2183_);
lean_dec(v_eq_2182_);
v___x_2193_ = lean_box(v___x_2189_);
v___x_2194_ = lean_apply_2(v_toPure_2179_, lean_box(0), v___x_2193_);
v___x_2195_ = lean_apply_4(v_toBind_2181_, lean_box(0), lean_box(0), v___x_2194_, v___f_2187_);
return v___x_2195_;
}
else
{
lean_object* v___f_2196_; size_t v___x_2197_; size_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v_toPure_2179_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2196_, 0, v_eq_2182_);
lean_closure_set(v___f_2196_, 1, v_a_2184_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = lean_usize_of_nat(v___x_2188_);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2183_, v___f_2196_, v___y_2186_, v___x_2197_, v___x_2198_);
v___x_2200_ = lean_apply_4(v_toBind_2181_, lean_box(0), lean_box(0), v___x_2199_, v___f_2187_);
return v___x_2200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(lean_object* v_toPure_2201_, lean_object* v___x_2202_, lean_object* v_toBind_2203_, lean_object* v_eq_2204_, lean_object* v_inst_2205_, lean_object* v_a_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_2201_, v___x_2202_, v_toBind_2203_, v_eq_2204_, v_inst_2205_, v_a_2206_, v_x_2207_, v___y_2208_);
lean_dec(v___x_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(lean_object* v_toPure_2210_, lean_object* v_____s_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_apply_2(v_toPure_2210_, lean_box(0), v_____s_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(lean_object* v_inst_2215_, lean_object* v_eq_2216_, lean_object* v_xs_2217_){
_start:
{
lean_object* v_toApplicative_2218_; lean_object* v_toBind_2219_; lean_object* v_toPure_2220_; lean_object* v___x_2221_; lean_object* v_ret_2222_; lean_object* v___f_2223_; lean_object* v___f_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_toApplicative_2218_ = lean_ctor_get(v_inst_2215_, 0);
v_toBind_2219_ = lean_ctor_get(v_inst_2215_, 1);
lean_inc(v_toBind_2219_);
v_toPure_2220_ = lean_ctor_get(v_toApplicative_2218_, 1);
v___x_2221_ = lean_unsigned_to_nat(0u);
v_ret_2222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
lean_inc_ref(v_inst_2215_);
lean_inc(v_toBind_2219_);
lean_inc(v_toPure_2220_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2223_, 0, v_toPure_2220_);
lean_closure_set(v___f_2223_, 1, v___x_2221_);
lean_closure_set(v___f_2223_, 2, v_toBind_2219_);
lean_closure_set(v___f_2223_, 3, v_eq_2216_);
lean_closure_set(v___f_2223_, 4, v_inst_2215_);
lean_inc(v_toPure_2220_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2224_, 0, v_toPure_2220_);
v_sz_2225_ = lean_array_size(v_xs_2217_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2215_, v_xs_2217_, v___f_2223_, v_sz_2225_, v___x_2226_, v_ret_2222_);
v___x_2228_ = lean_apply_4(v_toBind_2219_, lean_box(0), lean_box(0), v___x_2227_, v___f_2224_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(lean_object* v_m_2229_, lean_object* v_00_u03b1_2230_, lean_object* v_inst_2231_, lean_object* v_eq_2232_, lean_object* v_xs_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_2231_, v_eq_2232_, v_xs_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_bs_2237_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_usize_dec_lt(v_i_2236_, v_sz_2235_);
if (v___x_2238_ == 0)
{
return v_bs_2237_;
}
else
{
lean_object* v_v_2239_; lean_object* v_indGroupInst_2240_; lean_object* v___x_2241_; lean_object* v_bs_x27_2242_; size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v_v_2239_ = lean_array_uget_borrowed(v_bs_2237_, v_i_2236_);
v_indGroupInst_2240_ = lean_ctor_get(v_v_2239_, 4);
lean_inc_ref(v_indGroupInst_2240_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v_bs_x27_2242_ = lean_array_uset(v_bs_2237_, v_i_2236_, v___x_2241_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2236_, v___x_2243_);
v___x_2245_ = lean_array_uset(v_bs_x27_2242_, v_i_2236_, v_indGroupInst_2240_);
v_i_2236_ = v___x_2244_;
v_bs_2237_ = v___x_2245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_bs_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_2250_, v_i_boxed_2251_, v_bs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(lean_object* v_eq_2253_, lean_object* v_a_2254_, lean_object* v_as_2255_, size_t v_i_2256_, size_t v_stop_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_usize_dec_eq(v_i_2256_, v_stop_2257_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_array_uget_borrowed(v_as_2255_, v_i_2256_);
lean_inc_ref(v_eq_2253_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc(v___y_2259_);
lean_inc_ref(v___y_2258_);
lean_inc(v_a_2254_);
lean_inc(v___x_2264_);
v___x_2265_ = lean_apply_7(v_eq_2253_, v___x_2264_, v_a_2254_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, lean_box(0));
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2277_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_unbox(v_a_2266_);
if (v___x_2270_ == 0)
{
size_t v___x_2271_; size_t v___x_2272_; 
lean_del_object(v___x_2268_);
lean_dec(v_a_2266_);
v___x_2271_ = ((size_t)1ULL);
v___x_2272_ = lean_usize_add(v_i_2256_, v___x_2271_);
v_i_2256_ = v___x_2272_;
goto _start;
}
else
{
lean_object* v___x_2275_; 
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_a_2254_);
lean_dec_ref(v_eq_2253_);
if (v_isShared_2269_ == 0)
{
v___x_2275_ = v___x_2268_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2266_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_a_2254_);
lean_dec_ref(v_eq_2253_);
return v___x_2265_;
}
}
else
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_a_2254_);
lean_dec_ref(v_eq_2253_);
v___x_2278_ = 0;
v___x_2279_ = lean_box(v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(lean_object* v_eq_2281_, lean_object* v_a_2282_, lean_object* v_as_2283_, lean_object* v_i_2284_, lean_object* v_stop_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
size_t v_i_boxed_2291_; size_t v_stop_boxed_2292_; lean_object* v_res_2293_; 
v_i_boxed_2291_ = lean_unbox_usize(v_i_2284_);
lean_dec(v_i_2284_);
v_stop_boxed_2292_ = lean_unbox_usize(v_stop_2285_);
lean_dec(v_stop_2285_);
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2281_, v_a_2282_, v_as_2283_, v_i_boxed_2291_, v_stop_boxed_2292_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec_ref(v_as_2283_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(lean_object* v_b_2294_, lean_object* v_a_2295_, uint8_t v_____do__lift_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
if (v_____do__lift_2296_ == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_array_push(v_b_2294_, v_a_2295_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_a_2295_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_b_2294_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_b_2307_, lean_object* v_a_2308_, lean_object* v_____do__lift_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v_____do__lift_1296__boxed_2315_; lean_object* v_res_2316_; 
v_____do__lift_1296__boxed_2315_ = lean_unbox(v_____do__lift_2309_);
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2307_, v_a_2308_, v_____do__lift_1296__boxed_2315_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(lean_object* v_eq_2317_, lean_object* v_as_2318_, size_t v_sz_2319_, size_t v_i_2320_, lean_object* v_b_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_a_2328_; lean_object* v___y_2333_; uint8_t v___x_2352_; 
v___x_2352_ = lean_usize_dec_lt(v_i_2320_, v_sz_2319_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_eq_2317_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_b_2321_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v_a_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2354_ = lean_unsigned_to_nat(0u);
v_a_2355_ = lean_array_uget_borrowed(v_as_2318_, v_i_2320_);
v___x_2356_ = lean_array_get_size(v_b_2321_);
v___x_2357_ = lean_nat_dec_lt(v___x_2354_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_inc(v_a_2355_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2321_, v_a_2355_, v___x_2357_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
v___y_2333_ = v___x_2358_;
goto v___jp_2332_;
}
else
{
if (v___x_2357_ == 0)
{
lean_object* v___x_2359_; 
lean_inc(v_a_2355_);
v___x_2359_ = lean_array_push(v_b_2321_, v_a_2355_);
v_a_2328_ = v___x_2359_;
goto v___jp_2327_;
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = lean_usize_of_nat(v___x_2356_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
lean_inc(v___y_2323_);
lean_inc_ref(v___y_2322_);
lean_inc(v_a_2355_);
lean_inc_ref(v_eq_2317_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2317_, v_a_2355_, v_b_2321_, v___x_2360_, v___x_2361_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = lean_unbox(v_a_2363_);
lean_dec(v_a_2363_);
lean_inc(v_a_2355_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_2321_, v_a_2355_, v___x_2364_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
v___y_2333_ = v___x_2365_;
goto v___jp_2332_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_b_2321_);
lean_dec_ref(v_eq_2317_);
v_a_2366_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2362_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
v___jp_2327_:
{
size_t v___x_2329_; size_t v___x_2330_; 
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2320_, v___x_2329_);
v_i_2320_ = v___x_2330_;
v_b_2321_ = v_a_2328_;
goto _start;
}
v___jp_2332_:
{
if (lean_obj_tag(v___y_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2343_; 
v_a_2334_ = lean_ctor_get(v___y_2333_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___y_2333_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2336_ = v___y_2333_;
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___y_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2343_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
if (lean_obj_tag(v_a_2334_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_eq_2317_);
v_a_2338_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v_a_2334_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v_a_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v_a_2342_; 
lean_del_object(v___x_2336_);
v_a_2342_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v_a_2334_);
v_a_2328_ = v_a_2342_;
goto v___jp_2327_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_eq_2317_);
v_a_2344_ = lean_ctor_get(v___y_2333_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___y_2333_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___y_2333_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___y_2333_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(lean_object* v_eq_2374_, lean_object* v_as_2375_, lean_object* v_sz_2376_, lean_object* v_i_2377_, lean_object* v_b_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
size_t v_sz_boxed_2384_; size_t v_i_boxed_2385_; lean_object* v_res_2386_; 
v_sz_boxed_2384_ = lean_unbox_usize(v_sz_2376_);
lean_dec(v_sz_2376_);
v_i_boxed_2385_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_res_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2374_, v_as_2375_, v_sz_boxed_2384_, v_i_boxed_2385_, v_b_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec_ref(v_as_2375_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(lean_object* v_eq_2387_, lean_object* v_xs_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_ret_2394_; size_t v_sz_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v_ret_2394_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v_sz_2395_ = lean_array_size(v_xs_2388_);
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2387_, v_xs_2388_, v_sz_2395_, v___x_2396_, v_ret_2394_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(lean_object* v_eq_2398_, lean_object* v_xs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2398_, v_xs_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v_xs_2399_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups(lean_object* v_recArgInfos_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; size_t v_sz_2414_; size_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Structural_inductiveGroups___closed__0));
v_sz_2414_ = lean_array_size(v_recArgInfos_2407_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_2414_, v___x_2415_, v_recArgInfos_2407_);
v___x_2417_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_2413_, v___x_2416_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec_ref(v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inductiveGroups___boxed(lean_object* v_recArgInfos_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Elab_Structural_inductiveGroups(v_recArgInfos_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(lean_object* v_00_u03b1_2425_, lean_object* v_eq_2426_, lean_object* v_xs_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_2426_, v_xs_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_eq_2435_, lean_object* v_xs_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_2434_, v_eq_2435_, v_xs_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec_ref(v_xs_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(lean_object* v_00_u03b1_2443_, lean_object* v_eq_2444_, lean_object* v_a_2445_, lean_object* v_as_2446_, size_t v_i_2447_, size_t v_stop_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_2444_, v_a_2445_, v_as_2446_, v_i_2447_, v_stop_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_eq_2456_, lean_object* v_a_2457_, lean_object* v_as_2458_, lean_object* v_i_2459_, lean_object* v_stop_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
size_t v_i_boxed_2466_; size_t v_stop_boxed_2467_; lean_object* v_res_2468_; 
v_i_boxed_2466_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_stop_boxed_2467_ = lean_unbox_usize(v_stop_2460_);
lean_dec(v_stop_2460_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_2455_, v_eq_2456_, v_a_2457_, v_as_2458_, v_i_boxed_2466_, v_stop_boxed_2467_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec_ref(v_as_2458_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(lean_object* v_00_u03b1_2469_, lean_object* v_eq_2470_, lean_object* v_as_2471_, size_t v_sz_2472_, size_t v_i_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_2470_, v_as_2471_, v_sz_2472_, v_i_2473_, v_b_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2481_, lean_object* v_eq_2482_, lean_object* v_as_2483_, lean_object* v_sz_2484_, lean_object* v_i_2485_, lean_object* v_b_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
size_t v_sz_boxed_2492_; size_t v_i_boxed_2493_; lean_object* v_res_2494_; 
v_sz_boxed_2492_ = lean_unbox_usize(v_sz_2484_);
lean_dec(v_sz_2484_);
v_i_boxed_2493_ = lean_unbox_usize(v_i_2485_);
lean_dec(v_i_2485_);
v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_2481_, v_eq_2482_, v_as_2483_, v_sz_boxed_2492_, v_i_boxed_2493_, v_b_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec_ref(v_as_2483_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(lean_object* v_e_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = l_Lean_Expr_hasMVar(v_e_2495_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_e_2495_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; lean_object* v_mctx_2501_; lean_object* v___x_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2505_; lean_object* v_cache_2506_; lean_object* v_zetaDeltaFVarIds_2507_; lean_object* v_postponed_2508_; lean_object* v_diag_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2518_; 
v___x_2500_ = lean_st_ref_get(v___y_2496_);
v_mctx_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc_ref(v_mctx_2501_);
lean_dec(v___x_2500_);
v___x_2502_ = l_Lean_instantiateMVarsCore(v_mctx_2501_, v_e_2495_);
v_fst_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_fst_2503_);
v_snd_2504_ = lean_ctor_get(v___x_2502_, 1);
lean_inc(v_snd_2504_);
lean_dec_ref(v___x_2502_);
v___x_2505_ = lean_st_ref_take(v___y_2496_);
v_cache_2506_ = lean_ctor_get(v___x_2505_, 1);
v_zetaDeltaFVarIds_2507_ = lean_ctor_get(v___x_2505_, 2);
v_postponed_2508_ = lean_ctor_get(v___x_2505_, 3);
v_diag_2509_ = lean_ctor_get(v___x_2505_, 4);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v___x_2505_, 0);
lean_dec(v_unused_2519_);
v___x_2511_ = v___x_2505_;
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_diag_2509_);
lean_inc(v_postponed_2508_);
lean_inc(v_zetaDeltaFVarIds_2507_);
lean_inc(v_cache_2506_);
lean_dec(v___x_2505_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_snd_2504_);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_snd_2504_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_cache_2506_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_zetaDeltaFVarIds_2507_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_postponed_2508_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_diag_2509_);
v___x_2514_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_st_ref_set(v___y_2496_, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_fst_2503_);
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(lean_object* v_e_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2520_, v___y_2521_);
lean_dec(v___y_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(lean_object* v_e_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_e_2524_, v___y_2526_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(lean_object* v_e_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(v_e_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2537_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2));
v___x_2540_ = lean_unsigned_to_nat(113u);
v___x_2541_ = lean_unsigned_to_nat(214u);
v___x_2542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0));
v___x_2543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0));
v___x_2544_ = l_mkPanicMessageWithDecl(v___x_2543_, v___x_2542_, v___x_2541_, v___x_2540_, v___x_2539_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(lean_object* v___x_2545_, size_t v_sz_2546_, size_t v_i_2547_, lean_object* v_bs_2548_){
_start:
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_usize_dec_lt(v_i_2547_, v_sz_2546_);
if (v___x_2549_ == 0)
{
return v_bs_2548_;
}
else
{
lean_object* v_v_2550_; lean_object* v___x_2551_; lean_object* v_bs_x27_2552_; lean_object* v___y_2554_; lean_object* v___x_2559_; 
v_v_2550_ = lean_array_uget(v_bs_2548_, v_i_2547_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v_bs_x27_2552_ = lean_array_uset(v_bs_2548_, v_i_2547_, v___x_2551_);
v___x_2559_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_2545_, v_v_2550_);
lean_dec(v_v_2550_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
v___x_2561_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(v___x_2560_);
v___y_2554_ = v___x_2561_;
goto v___jp_2553_;
}
else
{
lean_object* v_val_2562_; 
v_val_2562_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2562_);
lean_dec_ref(v___x_2559_);
v___y_2554_ = v_val_2562_;
goto v___jp_2553_;
}
v___jp_2553_:
{
size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((size_t)1ULL);
v___x_2556_ = lean_usize_add(v_i_2547_, v___x_2555_);
v___x_2557_ = lean_array_uset(v_bs_x27_2552_, v_i_2547_, v___y_2554_);
v_i_2547_ = v___x_2556_;
v_bs_2548_ = v___x_2557_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(lean_object* v___x_2563_, lean_object* v_sz_2564_, lean_object* v_i_2565_, lean_object* v_bs_2566_){
_start:
{
size_t v_sz_boxed_2567_; size_t v_i_boxed_2568_; lean_object* v_res_2569_; 
v_sz_boxed_2567_ = lean_unbox_usize(v_sz_2564_);
lean_dec(v_sz_2564_);
v_i_boxed_2568_ = lean_unbox_usize(v_i_2565_);
lean_dec(v_i_2565_);
v_res_2569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2563_, v_sz_boxed_2567_, v_i_boxed_2568_, v_bs_2566_);
lean_dec_ref(v___x_2563_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(size_t v_sz_2570_, size_t v_i_2571_, lean_object* v_bs_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_lt(v_i_2571_, v_sz_2570_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_bs_2572_);
return v___x_2579_;
}
else
{
lean_object* v_v_2580_; lean_object* v___x_2581_; 
v_v_2580_ = lean_array_uget_borrowed(v_bs_2572_, v_i_2571_);
lean_inc(v_v_2580_);
v___x_2581_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_2580_, v___y_2574_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v_bs_x27_2584_; size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
v___x_2583_ = lean_unsigned_to_nat(0u);
v_bs_x27_2584_ = lean_array_uset(v_bs_2572_, v_i_2571_, v___x_2583_);
v___x_2585_ = ((size_t)1ULL);
v___x_2586_ = lean_usize_add(v_i_2571_, v___x_2585_);
v___x_2587_ = lean_array_uset(v_bs_x27_2584_, v_i_2571_, v_a_2582_);
v_i_2571_ = v___x_2586_;
v_bs_2572_ = v___x_2587_;
goto _start;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_bs_2572_);
v_a_2589_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2581_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2581_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(lean_object* v_sz_2597_, lean_object* v_i_2598_, lean_object* v_bs_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
size_t v_sz_boxed_2605_; size_t v_i_boxed_2606_; lean_object* v_res_2607_; 
v_sz_boxed_2605_ = lean_unbox_usize(v_sz_2597_);
lean_dec(v_sz_2597_);
v_i_boxed_2606_ = lean_unbox_usize(v_i_2598_);
lean_dec(v_i_2598_);
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_2605_, v_i_boxed_2606_, v_bs_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2607_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(uint8_t v_a_2608_, lean_object* v___x_2609_, lean_object* v_as_2610_, size_t v_i_2611_, size_t v_stop_2612_){
_start:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_usize_dec_eq(v_i_2611_, v_stop_2612_);
if (v___x_2613_ == 0)
{
uint8_t v___x_2614_; uint8_t v___y_2616_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2614_ = 1;
v___x_2620_ = lean_array_uget_borrowed(v_as_2610_, v_i_2611_);
v___x_2621_ = l_Lean_Expr_isFVar(v___x_2620_);
if (v___x_2621_ == 0)
{
v___y_2616_ = v_a_2608_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_nat_dec_eq(v___x_2609_, v___x_2622_);
v___y_2616_ = v___x_2623_;
goto v___jp_2615_;
}
v___jp_2615_:
{
if (v___y_2616_ == 0)
{
size_t v___x_2617_; size_t v___x_2618_; 
v___x_2617_ = ((size_t)1ULL);
v___x_2618_ = lean_usize_add(v_i_2611_, v___x_2617_);
v_i_2611_ = v___x_2618_;
goto _start;
}
else
{
return v___x_2614_;
}
}
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = 0;
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(lean_object* v_a_2625_, lean_object* v___x_2626_, lean_object* v_as_2627_, lean_object* v_i_2628_, lean_object* v_stop_2629_){
_start:
{
uint8_t v_a_10186__boxed_2630_; size_t v_i_boxed_2631_; size_t v_stop_boxed_2632_; uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_a_10186__boxed_2630_ = lean_unbox(v_a_2625_);
v_i_boxed_2631_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_stop_boxed_2632_ = lean_unbox_usize(v_stop_2629_);
lean_dec(v_stop_2629_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_10186__boxed_2630_, v___x_2626_, v_as_2627_, v_i_boxed_2631_, v_stop_boxed_2632_);
lean_dec_ref(v_as_2627_);
lean_dec(v___x_2626_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(lean_object* v___x_2635_, lean_object* v___x_2636_, lean_object* v_ys_2637_, lean_object* v___x_2638_, lean_object* v_recArgInfo_2639_, lean_object* v___x_2640_, lean_object* v_group_2641_, lean_object* v_as_2642_, size_t v_sz_2643_, size_t v_i_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_a_2652_; uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_lt(v_i_2644_, v_sz_2643_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_b_2645_);
return v___x_2657_;
}
else
{
lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2816_; 
v_snd_2658_ = lean_ctor_get(v_b_2645_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_b_2645_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v_b_2645_, 0);
lean_dec(v_unused_2817_);
v___x_2660_ = v_b_2645_;
v_isShared_2661_ = v_isSharedCheck_2816_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_dec(v_b_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2816_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_next_2662_; lean_object* v_upperBound_2663_; lean_object* v___x_2664_; 
v_next_2662_ = lean_ctor_get(v_snd_2658_, 0);
lean_inc(v_next_2662_);
v_upperBound_2663_ = lean_ctor_get(v_snd_2658_, 1);
v___x_2664_ = lean_box(0);
if (lean_obj_tag(v_next_2662_) == 0)
{
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
goto v___jp_2665_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2815_; 
v_val_2670_ = lean_ctor_get(v_next_2662_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_next_2662_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2672_ = v_next_2662_;
v_isShared_2673_ = v_isSharedCheck_2815_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_dec(v_next_2662_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2815_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_nat_dec_lt(v_val_2670_, v_upperBound_2663_);
if (v___x_2674_ == 0)
{
lean_del_object(v___x_2672_);
lean_dec(v_val_2670_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
goto v___jp_2665_;
}
else
{
lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2812_; 
lean_inc(v_upperBound_2663_);
lean_del_object(v___x_2660_);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_snd_2658_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; lean_object* v_unused_2814_; 
v_unused_2813_ = lean_ctor_get(v_snd_2658_, 1);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_snd_2658_, 0);
lean_dec(v_unused_2814_);
v___x_2676_ = v_snd_2658_;
v_isShared_2677_ = v_isSharedCheck_2812_;
goto v_resetjp_2675_;
}
else
{
lean_dec(v_snd_2658_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2812_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; 
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc_ref(v___x_2635_);
v___x_2678_ = lean_infer_type(v___x_2635_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
v___x_2680_ = l_Lean_Meta_whnfD(v_a_2679_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v_a_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2680_);
v_a_2682_ = lean_array_uget_borrowed(v_as_2642_, v_i_2644_);
v___x_2683_ = 0;
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v_a_2682_);
v___x_2684_ = l_Lean_Meta_forallMetaTelescope(v_a_2682_, v___x_2683_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v_snd_2686_; lean_object* v_fst_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2787_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v___x_2684_);
v_snd_2686_ = lean_ctor_get(v_a_2685_, 1);
v_fst_2687_ = lean_ctor_get(v_a_2685_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_a_2685_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2689_ = v_a_2685_;
v_isShared_2690_ = v_isSharedCheck_2787_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snd_2686_);
lean_inc(v_fst_2687_);
lean_dec(v_a_2685_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2787_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_snd_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2785_; 
v_snd_2691_ = lean_ctor_get(v_snd_2686_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_snd_2686_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_snd_2686_, 0);
lean_dec(v_unused_2786_);
v___x_2693_ = v_snd_2686_;
v_isShared_2694_ = v_isSharedCheck_2785_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snd_2691_);
lean_dec(v_snd_2686_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2785_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; 
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
v___x_2695_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2691_, v_a_2681_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_val_2670_, v___x_2697_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2698_);
v___x_2700_ = v___x_2672_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2700_);
v___x_2702_ = v___x_2676_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_upperBound_2663_);
v___x_2702_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_unbox(v_a_2696_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_a_2696_);
lean_del_object(v___x_2689_);
lean_dec(v_fst_2687_);
lean_dec(v_val_2670_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2702_);
lean_ctor_set(v___x_2693_, 0, v___x_2664_);
v___x_2705_ = v___x_2693_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2702_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
v_a_2652_ = v___x_2705_;
goto v___jp_2651_;
}
}
else
{
size_t v_sz_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v_sz_2707_ = lean_array_size(v_fst_2687_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2707_, v___x_2708_, v_fst_2687_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_nat_dec_eq(v___x_2636_, v___x_2715_);
v___x_2762_ = lean_array_get_size(v_a_2710_);
v___x_2763_ = lean_nat_dec_lt(v___x_2715_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_dec(v_a_2696_);
goto v___jp_2717_;
}
else
{
if (v___x_2763_ == 0)
{
lean_dec(v_a_2696_);
goto v___jp_2717_;
}
else
{
size_t v___x_2764_; uint8_t v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = lean_usize_of_nat(v___x_2762_);
v___x_2765_ = lean_unbox(v_a_2696_);
lean_dec(v_a_2696_);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2765_, v___x_2636_, v_a_2710_, v___x_2708_, v___x_2764_);
if (v___x_2766_ == 0)
{
goto v___jp_2717_;
}
else
{
if (v___x_2716_ == 0)
{
lean_dec(v_a_2710_);
lean_del_object(v___x_2689_);
lean_dec(v_val_2670_);
goto v___jp_2711_;
}
else
{
goto v___jp_2717_;
}
}
}
}
v___jp_2711_:
{
lean_object* v___x_2713_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2702_);
lean_ctor_set(v___x_2693_, 0, v___x_2664_);
v___x_2713_ = v___x_2693_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2702_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
v_a_2652_ = v___x_2713_;
goto v___jp_2651_;
}
}
v___jp_2717_:
{
if (v___x_2716_ == 0)
{
uint8_t v___x_2718_; 
lean_del_object(v___x_2693_);
v___x_2718_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2710_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2720_; 
lean_dec(v_a_2710_);
lean_dec(v_val_2670_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2702_);
lean_ctor_set(v___x_2689_, 0, v___x_2664_);
v___x_2720_ = v___x_2689_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2702_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
v_a_2652_ = v___x_2720_;
goto v___jp_2651_;
}
}
else
{
lean_object* v___x_2722_; 
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
v___x_2722_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2637_, v_a_2710_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2753_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2753_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2753_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
if (lean_obj_tag(v_a_2723_) == 1)
{
lean_object* v___x_2728_; 
lean_dec_ref(v_a_2723_);
lean_del_object(v___x_2725_);
lean_dec(v_a_2710_);
lean_dec(v_val_2670_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2702_);
lean_ctor_set(v___x_2689_, 0, v___x_2664_);
v___x_2728_ = v___x_2689_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2702_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
v_a_2652_ = v___x_2728_;
goto v___jp_2651_;
}
}
else
{
lean_object* v_fnName_2730_; lean_object* v_fixedParamPerm_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2723_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v___x_2635_);
v_fnName_2730_ = lean_ctor_get(v_recArgInfo_2639_, 0);
v_fixedParamPerm_2731_ = lean_ctor_get(v_recArgInfo_2639_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_recArgInfo_2639_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2749_ = lean_ctor_get(v_recArgInfo_2639_, 5);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_recArgInfo_2639_, 4);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_recArgInfo_2639_, 3);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_recArgInfo_2639_, 2);
lean_dec(v_unused_2752_);
v___x_2733_ = v_recArgInfo_2639_;
v_isShared_2734_ = v_isSharedCheck_2748_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_fixedParamPerm_2731_);
lean_inc(v_fnName_2730_);
lean_dec(v_recArgInfo_2639_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2748_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
size_t v_sz_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v_sz_2735_ = lean_array_size(v_a_2710_);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2638_, v_sz_2735_, v___x_2708_, v_a_2710_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 5, v_val_2670_);
lean_ctor_set(v___x_2733_, 4, v_group_2641_);
lean_ctor_set(v___x_2733_, 3, v___x_2736_);
lean_ctor_set(v___x_2733_, 2, v___x_2640_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_fnName_2730_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_fixedParamPerm_2731_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_group_2641_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_val_2670_);
v___x_2738_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2702_);
lean_ctor_set(v___x_2689_, 0, v___x_2740_);
v___x_2742_ = v___x_2689_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2702_);
v___x_2742_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2744_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2742_);
v___x_2744_ = v___x_2725_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___x_2702_);
lean_del_object(v___x_2689_);
lean_dec(v_val_2670_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2754_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2722_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2722_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
else
{
lean_dec(v_a_2710_);
lean_del_object(v___x_2689_);
lean_dec(v_val_2670_);
goto v___jp_2711_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v___x_2702_);
lean_dec(v_a_2696_);
lean_del_object(v___x_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_val_2670_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2767_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2709_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2709_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_fst_2687_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
lean_dec(v_val_2670_);
lean_dec(v_upperBound_2663_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2777_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2695_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2695_);
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
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2681_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
lean_dec(v_val_2670_);
lean_dec(v_upperBound_2663_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2788_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2684_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2684_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
lean_dec(v_val_2670_);
lean_dec(v_upperBound_2663_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2796_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2680_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2680_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
lean_dec(v_val_2670_);
lean_dec(v_upperBound_2663_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_group_2641_);
lean_dec(v___x_2640_);
lean_dec_ref(v_recArgInfo_2639_);
lean_dec_ref(v___x_2635_);
v_a_2804_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2678_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2678_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
}
v___jp_2665_:
{
lean_object* v___x_2667_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2664_);
v___x_2667_ = v___x_2660_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_snd_2658_);
v___x_2667_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
return v___x_2668_;
}
}
}
}
v___jp_2651_:
{
size_t v___x_2653_; size_t v___x_2654_; 
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2644_, v___x_2653_);
v_i_2644_ = v___x_2654_;
v_b_2645_ = v_a_2652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_ys_2820_, lean_object* v___x_2821_, lean_object* v_recArgInfo_2822_, lean_object* v___x_2823_, lean_object* v_group_2824_, lean_object* v_as_2825_, lean_object* v_sz_2826_, lean_object* v_i_2827_, lean_object* v_b_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2826_);
lean_dec(v_sz_2826_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2818_, v___x_2819_, v_ys_2820_, v___x_2821_, v_recArgInfo_2822_, v___x_2823_, v_group_2824_, v_as_2825_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec_ref(v_as_2825_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_ys_2820_);
lean_dec(v___x_2819_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v_ys_2840_, lean_object* v_recArgInfo_2841_, lean_object* v___x_2842_, lean_object* v_group_2843_, lean_object* v_as_2844_, size_t v_sz_2845_, size_t v_i_2846_, lean_object* v_b_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_a_2854_; uint8_t v___x_2858_; 
v___x_2858_ = lean_usize_dec_lt(v_i_2846_, v_sz_2845_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_b_2847_);
return v___x_2859_;
}
else
{
lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_3018_; 
v_snd_2860_ = lean_ctor_get(v_b_2847_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_b_2847_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_b_2847_, 0);
lean_dec(v_unused_3019_);
v___x_2862_ = v_b_2847_;
v_isShared_2863_ = v_isSharedCheck_3018_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_dec(v_b_2847_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_3018_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v_next_2864_; lean_object* v_upperBound_2865_; lean_object* v___x_2866_; 
v_next_2864_ = lean_ctor_get(v_snd_2860_, 0);
lean_inc(v_next_2864_);
v_upperBound_2865_ = lean_ctor_get(v_snd_2860_, 1);
v___x_2866_ = lean_box(0);
if (lean_obj_tag(v_next_2864_) == 0)
{
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
goto v___jp_2867_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_3017_; 
v_val_2872_ = lean_ctor_get(v_next_2864_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_next_2864_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2874_ = v_next_2864_;
v_isShared_2875_ = v_isSharedCheck_3017_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_val_2872_);
lean_dec(v_next_2864_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_3017_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_nat_dec_lt(v_val_2872_, v_upperBound_2865_);
if (v___x_2876_ == 0)
{
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
goto v___jp_2867_;
}
else
{
lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_3014_; 
lean_inc(v_upperBound_2865_);
lean_del_object(v___x_2862_);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_snd_2860_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; lean_object* v_unused_3016_; 
v_unused_3015_ = lean_ctor_get(v_snd_2860_, 1);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_snd_2860_, 0);
lean_dec(v_unused_3016_);
v___x_2878_ = v_snd_2860_;
v_isShared_2879_ = v_isSharedCheck_3014_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v_snd_2860_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_3014_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; 
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v___x_2837_);
v___x_2880_ = lean_infer_type(v___x_2837_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
v___x_2882_ = l_Lean_Meta_whnfD(v_a_2881_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_a_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v_a_2884_ = lean_array_uget_borrowed(v_as_2844_, v_i_2846_);
v___x_2885_ = 0;
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc(v_a_2884_);
v___x_2886_ = l_Lean_Meta_forallMetaTelescope(v_a_2884_, v___x_2885_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v_snd_2888_; lean_object* v_fst_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2989_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2886_);
v_snd_2888_ = lean_ctor_get(v_a_2887_, 1);
v_fst_2889_ = lean_ctor_get(v_a_2887_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_a_2887_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2891_ = v_a_2887_;
v_isShared_2892_ = v_isSharedCheck_2989_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snd_2888_);
lean_inc(v_fst_2889_);
lean_dec(v_a_2887_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2989_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_snd_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2987_; 
v_snd_2893_ = lean_ctor_get(v_snd_2888_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_snd_2888_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_snd_2888_, 0);
lean_dec(v_unused_2988_);
v___x_2895_ = v_snd_2888_;
v_isShared_2896_ = v_isSharedCheck_2987_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_snd_2893_);
lean_dec(v_snd_2888_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2987_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; 
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
v___x_2897_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_2893_, v_a_2883_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_unsigned_to_nat(1u);
v___x_2900_ = lean_nat_add(v_val_2872_, v___x_2899_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2900_);
v___x_2902_ = v___x_2874_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2904_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2902_);
v___x_2904_ = v___x_2878_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_upperBound_2865_);
v___x_2904_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_unbox(v_a_2898_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2907_; 
lean_dec(v_a_2898_);
lean_del_object(v___x_2891_);
lean_dec(v_fst_2889_);
lean_dec(v_val_2872_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v___x_2904_);
lean_ctor_set(v___x_2895_, 0, v___x_2866_);
v___x_2907_ = v___x_2895_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2904_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v_a_2854_ = v___x_2907_;
goto v___jp_2853_;
}
}
else
{
size_t v_sz_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v_sz_2909_ = lean_array_size(v_fst_2889_);
v___x_2910_ = ((size_t)0ULL);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_2909_, v___x_2910_, v_fst_2889_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = lean_nat_dec_eq(v___x_2838_, v___x_2917_);
v___x_2964_ = lean_array_get_size(v_a_2912_);
v___x_2965_ = lean_nat_dec_lt(v___x_2917_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec(v_a_2898_);
goto v___jp_2919_;
}
else
{
if (v___x_2965_ == 0)
{
lean_dec(v_a_2898_);
goto v___jp_2919_;
}
else
{
size_t v___x_2966_; uint8_t v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = lean_usize_of_nat(v___x_2964_);
v___x_2967_ = lean_unbox(v_a_2898_);
lean_dec(v_a_2898_);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_2967_, v___x_2838_, v_a_2912_, v___x_2910_, v___x_2966_);
if (v___x_2968_ == 0)
{
goto v___jp_2919_;
}
else
{
if (v___x_2918_ == 0)
{
lean_dec(v_a_2912_);
lean_del_object(v___x_2891_);
lean_dec(v_val_2872_);
goto v___jp_2913_;
}
else
{
goto v___jp_2919_;
}
}
}
}
v___jp_2913_:
{
lean_object* v___x_2915_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v___x_2904_);
lean_ctor_set(v___x_2895_, 0, v___x_2866_);
v___x_2915_ = v___x_2895_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2904_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v_a_2854_ = v___x_2915_;
goto v___jp_2853_;
}
}
v___jp_2919_:
{
if (v___x_2918_ == 0)
{
uint8_t v___x_2920_; 
lean_del_object(v___x_2895_);
v___x_2920_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_a_2912_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2922_; 
lean_dec(v_a_2912_);
lean_dec(v_val_2872_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2904_);
lean_ctor_set(v___x_2891_, 0, v___x_2866_);
v___x_2922_ = v___x_2891_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2904_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
v_a_2854_ = v___x_2922_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2924_; 
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
v___x_2924_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_2840_, v_a_2912_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2955_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2955_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2955_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
if (lean_obj_tag(v_a_2925_) == 1)
{
lean_object* v___x_2930_; 
lean_dec_ref(v_a_2925_);
lean_del_object(v___x_2927_);
lean_dec(v_a_2912_);
lean_dec(v_val_2872_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2904_);
lean_ctor_set(v___x_2891_, 0, v___x_2866_);
v___x_2930_ = v___x_2891_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2904_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
v_a_2854_ = v___x_2930_;
goto v___jp_2853_;
}
}
else
{
lean_object* v_fnName_2932_; lean_object* v_fixedParamPerm_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_a_2925_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v___x_2837_);
v_fnName_2932_ = lean_ctor_get(v_recArgInfo_2841_, 0);
v_fixedParamPerm_2933_ = lean_ctor_get(v_recArgInfo_2841_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_recArgInfo_2841_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; lean_object* v_unused_2954_; 
v_unused_2951_ = lean_ctor_get(v_recArgInfo_2841_, 5);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_recArgInfo_2841_, 4);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_recArgInfo_2841_, 3);
lean_dec(v_unused_2953_);
v_unused_2954_ = lean_ctor_get(v_recArgInfo_2841_, 2);
lean_dec(v_unused_2954_);
v___x_2935_ = v_recArgInfo_2841_;
v_isShared_2936_ = v_isSharedCheck_2950_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_fixedParamPerm_2933_);
lean_inc(v_fnName_2932_);
lean_dec(v_recArgInfo_2841_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2950_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
size_t v_sz_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v_sz_2937_ = lean_array_size(v_a_2912_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_2839_, v_sz_2937_, v___x_2910_, v_a_2912_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 5, v_val_2872_);
lean_ctor_set(v___x_2935_, 4, v_group_2843_);
lean_ctor_set(v___x_2935_, 3, v___x_2938_);
lean_ctor_set(v___x_2935_, 2, v___x_2842_);
v___x_2940_ = v___x_2935_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_fnName_2932_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_fixedParamPerm_2933_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2949_, 3, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2949_, 4, v_group_2843_);
lean_ctor_set(v_reuseFailAlloc_2949_, 5, v_val_2872_);
v___x_2940_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2904_);
lean_ctor_set(v___x_2891_, 0, v___x_2942_);
v___x_2944_ = v___x_2891_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2904_);
v___x_2944_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2946_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2944_);
v___x_2946_ = v___x_2927_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
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
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2912_);
lean_dec_ref(v___x_2904_);
lean_del_object(v___x_2891_);
lean_dec(v_val_2872_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_2956_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2924_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2924_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
else
{
lean_dec(v_a_2912_);
lean_del_object(v___x_2891_);
lean_dec(v_val_2872_);
goto v___jp_2913_;
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v___x_2904_);
lean_dec(v_a_2898_);
lean_del_object(v___x_2895_);
lean_del_object(v___x_2891_);
lean_dec(v_val_2872_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_2969_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2911_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2911_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2895_);
lean_del_object(v___x_2891_);
lean_dec(v_fst_2889_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_upperBound_2865_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_2979_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2897_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2897_);
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
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_a_2883_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_upperBound_2865_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_2990_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2886_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2886_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_upperBound_2865_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_2998_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2882_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2882_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_upperBound_2865_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_group_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_recArgInfo_2841_);
lean_dec_ref(v___x_2837_);
v_a_3006_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2880_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2880_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
}
v___jp_2867_:
{
lean_object* v___x_2869_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2866_);
v___x_2869_ = v___x_2862_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_snd_2860_);
v___x_2869_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
}
v___jp_2853_:
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_add(v_i_2846_, v___x_2855_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_2837_, v___x_2838_, v_ys_2840_, v___x_2839_, v_recArgInfo_2841_, v___x_2842_, v_group_2843_, v_as_2844_, v_sz_2845_, v___x_2856_, v_a_2854_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(lean_object* v___x_3020_, lean_object* v___x_3021_, lean_object* v___x_3022_, lean_object* v_ys_3023_, lean_object* v_recArgInfo_3024_, lean_object* v___x_3025_, lean_object* v_group_3026_, lean_object* v_as_3027_, lean_object* v_sz_3028_, lean_object* v_i_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
size_t v_sz_boxed_3036_; size_t v_i_boxed_3037_; lean_object* v_res_3038_; 
v_sz_boxed_3036_ = lean_unbox_usize(v_sz_3028_);
lean_dec(v_sz_3028_);
v_i_boxed_3037_ = lean_unbox_usize(v_i_3029_);
lean_dec(v_i_3029_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3020_, v___x_3021_, v___x_3022_, v_ys_3023_, v_recArgInfo_3024_, v___x_3025_, v_group_3026_, v_as_3027_, v_sz_boxed_3036_, v_i_boxed_3037_, v_b_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec_ref(v_as_3027_);
lean_dec_ref(v_ys_3023_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(lean_object* v_group_3039_, lean_object* v_xs_3040_, lean_object* v_recArgPos_3041_, lean_object* v_a_3042_, lean_object* v___x_3043_, lean_object* v___x_3044_, lean_object* v_ys_3045_, lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_toIndGroupInfo_3052_; lean_object* v_all_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3092_; 
v_toIndGroupInfo_3052_ = lean_ctor_get(v_group_3039_, 0);
lean_inc_ref(v_toIndGroupInfo_3052_);
v_all_3053_ = lean_ctor_get(v_toIndGroupInfo_3052_, 0);
v___x_3054_ = l_Lean_instInhabitedExpr;
v___x_3055_ = l_Array_append___redArg(v_xs_3040_, v_ys_3045_);
v___x_3056_ = lean_array_get(v___x_3054_, v___x_3055_, v_recArgPos_3041_);
v___x_3057_ = lean_array_get_size(v_all_3053_);
v___x_3058_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_3052_);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_toIndGroupInfo_3052_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; lean_object* v_unused_3094_; 
v_unused_3093_ = lean_ctor_get(v_toIndGroupInfo_3052_, 1);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_toIndGroupInfo_3052_, 0);
lean_dec(v_unused_3094_);
v___x_3060_ = v_toIndGroupInfo_3052_;
v_isShared_3061_ = v_isSharedCheck_3092_;
goto v_resetjp_3059_;
}
else
{
lean_dec(v_toIndGroupInfo_3052_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3092_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3057_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 1, v___x_3058_);
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3058_);
v___x_3064_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; size_t v_sz_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___x_3064_);
v_sz_3067_ = lean_array_size(v_a_3042_);
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_3056_, v___x_3043_, v___x_3055_, v_ys_3045_, v___x_3044_, v_recArgPos_3041_, v_group_3039_, v_a_3042_, v_sz_3067_, v___x_3068_, v___x_3066_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec_ref(v___x_3055_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3082_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_fst_3074_; 
v_fst_3074_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_fst_3074_);
lean_dec(v_a_3070_);
if (lean_obj_tag(v_fst_3074_) == 0)
{
lean_object* v___x_3076_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3065_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3065_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
else
{
lean_object* v_val_3078_; lean_object* v___x_3080_; 
v_val_3078_ = lean_ctor_get(v_fst_3074_, 0);
lean_inc(v_val_3078_);
lean_dec_ref(v_fst_3074_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_val_3078_);
v___x_3080_ = v___x_3072_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_val_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
v_a_3083_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3069_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3069_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(lean_object* v_group_3095_, lean_object* v_xs_3096_, lean_object* v_recArgPos_3097_, lean_object* v_a_3098_, lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v_ys_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_3095_, v_xs_3096_, v_recArgPos_3097_, v_a_3098_, v___x_3099_, v___x_3100_, v_ys_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec_ref(v_x_3102_);
lean_dec_ref(v_ys_3101_);
lean_dec(v___x_3099_);
lean_dec_ref(v_a_3098_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(lean_object* v_group_3109_, lean_object* v_a_3110_, lean_object* v_xs_3111_, lean_object* v_value_3112_, lean_object* v_as_3113_, size_t v_i_3114_, size_t v_stop_3115_, lean_object* v_b_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_a_3123_; lean_object* v_val_3128_; uint8_t v___x_3130_; 
v___x_3130_ = lean_usize_dec_eq(v_i_3114_, v_stop_3115_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v_recArgPos_3132_; lean_object* v_indGroupInst_3133_; lean_object* v___x_3134_; 
v___x_3131_ = lean_array_uget_borrowed(v_as_3113_, v_i_3114_);
v_recArgPos_3132_ = lean_ctor_get(v___x_3131_, 2);
v_indGroupInst_3133_ = lean_ctor_get(v___x_3131_, 4);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
lean_inc(v___y_3118_);
lean_inc_ref(v___y_3117_);
lean_inc_ref(v_indGroupInst_3133_);
lean_inc_ref(v_group_3109_);
v___x_3134_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(v_group_3109_, v_indGroupInst_3133_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; uint8_t v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v___x_3136_ = lean_unbox(v_a_3135_);
lean_dec(v_a_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = lean_array_get_size(v_a_3110_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_nat_dec_eq(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___f_3140_; lean_object* v___x_3141_; 
lean_inc(v___x_3131_);
lean_inc_ref(v_a_3110_);
lean_inc(v_recArgPos_3132_);
lean_inc_ref(v_xs_3111_);
lean_inc_ref(v_group_3109_);
v___f_3140_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3140_, 0, v_group_3109_);
lean_closure_set(v___f_3140_, 1, v_xs_3111_);
lean_closure_set(v___f_3140_, 2, v_recArgPos_3132_);
lean_closure_set(v___f_3140_, 3, v_a_3110_);
lean_closure_set(v___f_3140_, 4, v___x_3137_);
lean_closure_set(v___f_3140_, 5, v___x_3131_);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
lean_inc(v___y_3118_);
lean_inc_ref(v___y_3117_);
lean_inc_ref(v_value_3112_);
v___x_3141_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_3112_, v___f_3140_, v___x_3139_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref(v___x_3141_);
if (lean_obj_tag(v_a_3142_) == 0)
{
v_a_3123_ = v_b_3116_;
goto v___jp_3122_;
}
else
{
lean_object* v_val_3143_; 
v_val_3143_ = lean_ctor_get(v_a_3142_, 0);
lean_inc(v_val_3143_);
lean_dec_ref(v_a_3142_);
v_val_3128_ = v_val_3143_;
goto v___jp_3127_;
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v_b_3116_);
lean_dec_ref(v_value_3112_);
lean_dec_ref(v_xs_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_group_3109_);
v_a_3144_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3141_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3141_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
v_a_3123_ = v_b_3116_;
goto v___jp_3122_;
}
}
else
{
lean_inc(v___x_3131_);
v_val_3128_ = v___x_3131_;
goto v___jp_3127_;
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v_b_3116_);
lean_dec_ref(v_value_3112_);
lean_dec_ref(v_xs_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_group_3109_);
v_a_3152_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3134_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3134_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v___x_3160_; 
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v_value_3112_);
lean_dec_ref(v_xs_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_group_3109_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_b_3116_);
return v___x_3160_;
}
v___jp_3122_:
{
size_t v___x_3124_; size_t v___x_3125_; 
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_add(v_i_3114_, v___x_3124_);
v_i_3114_ = v___x_3125_;
v_b_3116_ = v_a_3123_;
goto _start;
}
v___jp_3127_:
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_array_push(v_b_3116_, v_val_3128_);
v_a_3123_ = v___x_3129_;
goto v___jp_3122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(lean_object* v_group_3161_, lean_object* v_a_3162_, lean_object* v_xs_3163_, lean_object* v_value_3164_, lean_object* v_as_3165_, lean_object* v_i_3166_, lean_object* v_stop_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
size_t v_i_boxed_3174_; size_t v_stop_boxed_3175_; lean_object* v_res_3176_; 
v_i_boxed_3174_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_stop_boxed_3175_ = lean_unbox_usize(v_stop_3167_);
lean_dec(v_stop_3167_);
v_res_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3161_, v_a_3162_, v_xs_3163_, v_value_3164_, v_as_3165_, v_i_boxed_3174_, v_stop_boxed_3175_, v_b_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec_ref(v_as_3165_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(lean_object* v_group_3177_, lean_object* v_a_3178_, lean_object* v_xs_3179_, lean_object* v_value_3180_, lean_object* v_as_3181_, lean_object* v_start_3182_, lean_object* v_stop_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4));
v___x_3190_ = lean_nat_dec_lt(v_start_3182_, v_stop_3183_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v_value_3180_);
lean_dec_ref(v_xs_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v_group_3177_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_array_get_size(v_as_3181_);
v___x_3193_ = lean_nat_dec_le(v_stop_3183_, v___x_3192_);
if (v___x_3193_ == 0)
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_nat_dec_lt(v_start_3182_, v___x_3192_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v_value_3180_);
lean_dec_ref(v_xs_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v_group_3177_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3189_);
return v___x_3195_;
}
else
{
size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = lean_usize_of_nat(v_start_3182_);
v___x_3197_ = lean_usize_of_nat(v___x_3192_);
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3177_, v_a_3178_, v_xs_3179_, v_value_3180_, v_as_3181_, v___x_3196_, v___x_3197_, v___x_3189_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3198_;
}
}
else
{
size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_usize_of_nat(v_start_3182_);
v___x_3200_ = lean_usize_of_nat(v_stop_3183_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_3177_, v_a_3178_, v_xs_3179_, v_value_3180_, v_as_3181_, v___x_3199_, v___x_3200_, v___x_3189_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(lean_object* v_group_3202_, lean_object* v_a_3203_, lean_object* v_xs_3204_, lean_object* v_value_3205_, lean_object* v_as_3206_, lean_object* v_start_3207_, lean_object* v_stop_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3202_, v_a_3203_, v_xs_3204_, v_value_3205_, v_as_3206_, v_start_3207_, v_stop_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v_stop_3208_);
lean_dec(v_start_3207_);
lean_dec_ref(v_as_3206_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup(lean_object* v_group_3215_, lean_object* v_xs_3216_, lean_object* v_value_3217_, lean_object* v_recArgInfos_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3224_; 
lean_inc(v_a_3222_);
lean_inc_ref(v_a_3221_);
lean_inc(v_a_3220_);
lean_inc_ref(v_a_3219_);
lean_inc_ref(v_group_3215_);
v___x_3224_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(v_group_3215_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref(v___x_3224_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = lean_array_get_size(v_recArgInfos_3218_);
v___x_3228_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(v_group_3215_, v_a_3225_, v_xs_3216_, v_value_3217_, v_recArgInfos_3218_, v___x_3226_, v___x_3227_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
return v___x_3228_;
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec_ref(v_value_3217_);
lean_dec_ref(v_xs_3216_);
lean_dec_ref(v_group_3215_);
v_a_3229_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3224_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3224_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_argsInGroup___boxed(lean_object* v_group_3237_, lean_object* v_xs_3238_, lean_object* v_value_3239_, lean_object* v_recArgInfos_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Elab_Structural_argsInGroup(v_group_3237_, v_xs_3238_, v_value_3239_, v_recArgInfos_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec_ref(v_recArgInfos_3240_);
return v_res_3246_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_maxCombinationSize(void){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_unsigned_to_nat(10u);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(lean_object* v_xss_3250_, lean_object* v_i_3251_, lean_object* v_acc_3252_){
_start:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = lean_array_get_size(v_xss_3250_);
v___x_3254_ = lean_nat_dec_lt(v_i_3251_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = lean_unsigned_to_nat(1u);
v___x_3256_ = lean_mk_empty_array_with_capacity(v___x_3255_);
v___x_3257_ = lean_array_push(v___x_3256_, v_acc_3252_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3258_ = lean_array_fget_borrowed(v_xss_3250_, v_i_3251_);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0));
v___x_3261_ = lean_array_get_size(v___x_3258_);
v___x_3262_ = lean_nat_dec_lt(v___x_3259_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_dec_ref(v_acc_3252_);
return v___x_3260_;
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_le(v___x_3261_, v___x_3261_);
if (v___x_3263_ == 0)
{
if (v___x_3262_ == 0)
{
lean_dec_ref(v_acc_3252_);
return v___x_3260_;
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = lean_usize_of_nat(v___x_3261_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3251_, v_acc_3252_, v_xss_3250_, v___x_3258_, v___x_3264_, v___x_3265_, v___x_3260_);
return v___x_3266_;
}
}
else
{
size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = ((size_t)0ULL);
v___x_3268_ = lean_usize_of_nat(v___x_3261_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3251_, v_acc_3252_, v_xss_3250_, v___x_3258_, v___x_3267_, v___x_3268_, v___x_3260_);
return v___x_3269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(lean_object* v_i_3270_, lean_object* v_acc_3271_, lean_object* v_xss_3272_, lean_object* v_as_3273_, size_t v_i_3274_, size_t v_stop_3275_, lean_object* v_b_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_usize_dec_eq(v_i_3274_, v_stop_3275_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; 
v___x_3278_ = lean_array_uget_borrowed(v_as_3273_, v_i_3274_);
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = lean_nat_add(v_i_3270_, v___x_3279_);
lean_inc(v___x_3278_);
lean_inc_ref(v_acc_3271_);
v___x_3281_ = lean_array_push(v_acc_3271_, v___x_3278_);
v___x_3282_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3272_, v___x_3280_, v___x_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = l_Array_append___redArg(v_b_3276_, v___x_3282_);
lean_dec_ref(v___x_3282_);
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3274_, v___x_3284_);
v_i_3274_ = v___x_3285_;
v_b_3276_ = v___x_3283_;
goto _start;
}
else
{
lean_dec_ref(v_acc_3271_);
return v_b_3276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(lean_object* v_i_3287_, lean_object* v_acc_3288_, lean_object* v_xss_3289_, lean_object* v_as_3290_, lean_object* v_i_3291_, lean_object* v_stop_3292_, lean_object* v_b_3293_){
_start:
{
size_t v_i_boxed_3294_; size_t v_stop_boxed_3295_; lean_object* v_res_3296_; 
v_i_boxed_3294_ = lean_unbox_usize(v_i_3291_);
lean_dec(v_i_3291_);
v_stop_boxed_3295_ = lean_unbox_usize(v_stop_3292_);
lean_dec(v_stop_3292_);
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3287_, v_acc_3288_, v_xss_3289_, v_as_3290_, v_i_boxed_3294_, v_stop_boxed_3295_, v_b_3293_);
lean_dec_ref(v_as_3290_);
lean_dec_ref(v_xss_3289_);
lean_dec(v_i_3287_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(lean_object* v_xss_3297_, lean_object* v_i_3298_, lean_object* v_acc_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3297_, v_i_3298_, v_acc_3299_);
lean_dec(v_i_3298_);
lean_dec_ref(v_xss_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(lean_object* v_00_u03b1_3301_, lean_object* v_xss_3302_, lean_object* v_i_3303_, lean_object* v_acc_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3302_, v_i_3303_, v_acc_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(lean_object* v_00_u03b1_3306_, lean_object* v_xss_3307_, lean_object* v_i_3308_, lean_object* v_acc_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_3306_, v_xss_3307_, v_i_3308_, v_acc_3309_);
lean_dec(v_i_3308_);
lean_dec_ref(v_xss_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(lean_object* v_00_u03b1_3311_, lean_object* v_i_3312_, lean_object* v_acc_3313_, lean_object* v_xss_3314_, lean_object* v_as_3315_, size_t v_i_3316_, size_t v_stop_3317_, lean_object* v_b_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_3312_, v_acc_3313_, v_xss_3314_, v_as_3315_, v_i_3316_, v_stop_3317_, v_b_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(lean_object* v_00_u03b1_3320_, lean_object* v_i_3321_, lean_object* v_acc_3322_, lean_object* v_xss_3323_, lean_object* v_as_3324_, lean_object* v_i_3325_, lean_object* v_stop_3326_, lean_object* v_b_3327_){
_start:
{
size_t v_i_boxed_3328_; size_t v_stop_boxed_3329_; lean_object* v_res_3330_; 
v_i_boxed_3328_ = lean_unbox_usize(v_i_3325_);
lean_dec(v_i_3325_);
v_stop_boxed_3329_ = lean_unbox_usize(v_stop_3326_);
lean_dec(v_stop_3326_);
v_res_3330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_3320_, v_i_3321_, v_acc_3322_, v_xss_3323_, v_as_3324_, v_i_boxed_3328_, v_stop_boxed_3329_, v_b_3327_);
lean_dec_ref(v_as_3324_);
lean_dec_ref(v_xss_3323_);
lean_dec(v_i_3321_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(lean_object* v_as_3331_, size_t v_i_3332_, size_t v_stop_3333_, lean_object* v_b_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_eq(v_i_3332_, v_stop_3333_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; size_t v___x_3339_; size_t v___x_3340_; 
v___x_3336_ = lean_array_uget_borrowed(v_as_3331_, v_i_3332_);
v___x_3337_ = lean_array_get_size(v___x_3336_);
v___x_3338_ = lean_nat_mul(v_b_3334_, v___x_3337_);
lean_dec(v_b_3334_);
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_add(v_i_3332_, v___x_3339_);
v_i_3332_ = v___x_3340_;
v_b_3334_ = v___x_3338_;
goto _start;
}
else
{
return v_b_3334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(lean_object* v_as_3342_, lean_object* v_i_3343_, lean_object* v_stop_3344_, lean_object* v_b_3345_){
_start:
{
size_t v_i_boxed_3346_; size_t v_stop_boxed_3347_; lean_object* v_res_3348_; 
v_i_boxed_3346_ = lean_unbox_usize(v_i_3343_);
lean_dec(v_i_3343_);
v_stop_boxed_3347_ = lean_unbox_usize(v_stop_3344_);
lean_dec(v_stop_3344_);
v_res_3348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3342_, v_i_boxed_3346_, v_stop_boxed_3347_, v_b_3345_);
lean_dec_ref(v_as_3342_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg(lean_object* v_xss_3349_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3350_ = lean_unsigned_to_nat(10u);
v___x_3351_ = lean_unsigned_to_nat(1u);
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3360_ = lean_array_get_size(v_xss_3349_);
v___x_3361_ = lean_nat_dec_lt(v___x_3352_, v___x_3360_);
if (v___x_3361_ == 0)
{
v___y_3354_ = v___x_3351_;
goto v___jp_3353_;
}
else
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_nat_dec_le(v___x_3360_, v___x_3360_);
if (v___x_3362_ == 0)
{
if (v___x_3361_ == 0)
{
v___y_3354_ = v___x_3351_;
goto v___jp_3353_;
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3360_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3349_, v___x_3363_, v___x_3364_, v___x_3351_);
v___y_3354_ = v___x_3365_;
goto v___jp_3353_;
}
}
else
{
size_t v___x_3366_; size_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((size_t)0ULL);
v___x_3367_ = lean_usize_of_nat(v___x_3360_);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_3349_, v___x_3366_, v___x_3367_, v___x_3351_);
v___y_3354_ = v___x_3368_;
goto v___jp_3353_;
}
}
v___jp_3353_:
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_nat_dec_lt(v___x_3350_, v___y_3354_);
lean_dec(v___y_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0));
v___x_3357_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_3349_, v___x_3352_, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_box(0);
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___redArg___boxed(lean_object* v_xss_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3369_);
lean_dec_ref(v_xss_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations(lean_object* v_00_u03b1_3371_, lean_object* v_xss_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_allCombinations___boxed(lean_object* v_00_u03b1_3374_, lean_object* v_xss_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_3374_, v_xss_3375_);
lean_dec_ref(v_xss_3375_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(lean_object* v_00_u03b1_3377_, lean_object* v_as_3378_, size_t v_i_3379_, size_t v_stop_3380_, lean_object* v_b_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_3378_, v_i_3379_, v_stop_3380_, v_b_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(lean_object* v_00_u03b1_3383_, lean_object* v_as_3384_, lean_object* v_i_3385_, lean_object* v_stop_3386_, lean_object* v_b_3387_){
_start:
{
size_t v_i_boxed_3388_; size_t v_stop_boxed_3389_; lean_object* v_res_3390_; 
v_i_boxed_3388_ = lean_unbox_usize(v_i_3385_);
lean_dec(v_i_3385_);
v_stop_boxed_3389_ = lean_unbox_usize(v_stop_3386_);
lean_dec(v_stop_3386_);
v_res_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_3383_, v_as_3384_, v_i_boxed_3388_, v_stop_boxed_3389_, v_b_3387_);
lean_dec_ref(v_as_3384_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(lean_object* v_cls_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_options_3394_; uint8_t v_hasTrace_3395_; 
v_options_3394_ = lean_ctor_get(v___y_3392_, 2);
v_hasTrace_3395_ = lean_ctor_get_uint8(v_options_3394_, sizeof(void*)*1);
if (v_hasTrace_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v_cls_3391_);
v___x_3396_ = lean_box(v_hasTrace_3395_);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
else
{
lean_object* v_inheritedTraceOptions_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_inheritedTraceOptions_3398_ = lean_ctor_get(v___y_3392_, 13);
v___x_3399_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___redArg___closed__1));
v___x_3400_ = l_Lean_Name_append(v___x_3399_, v_cls_3391_);
v___x_3401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3394_, v___x_3400_);
lean_dec(v___x_3400_);
v___x_3402_ = lean_box(v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg___boxed(lean_object* v_cls_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v_cls_3404_, v___y_3405_);
lean_dec_ref(v___y_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1(lean_object* v_cls_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v_cls_3408_, v___y_3412_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___boxed(lean_object* v_cls_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1(v_cls_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg(lean_object* v_constName_3424_, uint8_t v_skipRealize_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; lean_object* v_env_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3428_ = lean_st_ref_get(v___y_3426_);
v_env_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc_ref(v_env_3429_);
lean_dec(v___x_3428_);
v___x_3430_ = l_Lean_Environment_contains(v_env_3429_, v_constName_3424_, v_skipRealize_3425_);
v___x_3431_ = lean_box(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg___boxed(lean_object* v_constName_3433_, lean_object* v_skipRealize_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v_skipRealize_boxed_3437_; lean_object* v_res_3438_; 
v_skipRealize_boxed_3437_ = lean_unbox(v_skipRealize_3434_);
v_res_3438_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg(v_constName_3433_, v_skipRealize_boxed_3437_, v___y_3435_);
lean_dec(v___y_3435_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4(lean_object* v_constName_3439_, uint8_t v_skipRealize_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg(v_constName_3439_, v_skipRealize_3440_, v___y_3445_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___boxed(lean_object* v_constName_3448_, lean_object* v_skipRealize_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v_skipRealize_boxed_3456_; lean_object* v_res_3457_; 
v_skipRealize_boxed_3456_ = lean_unbox(v_skipRealize_3449_);
v_res_3457_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4(v_constName_3448_, v_skipRealize_boxed_3456_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(lean_object* v_a_3458_, lean_object* v_xs_3459_, lean_object* v_as_3460_, size_t v_sz_3461_, size_t v_i_3462_, lean_object* v_b_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_usize_dec_lt(v_i_3462_, v_sz_3461_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec_ref(v_xs_3459_);
lean_dec_ref(v_a_3458_);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_b_3463_);
return v___x_3470_;
}
else
{
lean_object* v_snd_3471_; lean_object* v_fst_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3515_; 
v_snd_3471_ = lean_ctor_get(v_b_3463_, 1);
v_fst_3472_ = lean_ctor_get(v_b_3463_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_b_3463_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3474_ = v_b_3463_;
v_isShared_3475_ = v_isSharedCheck_3515_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_snd_3471_);
lean_inc(v_fst_3472_);
lean_dec(v_b_3463_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3515_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_array_3476_; lean_object* v_start_3477_; lean_object* v_stop_3478_; uint8_t v___x_3479_; 
v_array_3476_ = lean_ctor_get(v_snd_3471_, 0);
v_start_3477_ = lean_ctor_get(v_snd_3471_, 1);
v_stop_3478_ = lean_ctor_get(v_snd_3471_, 2);
v___x_3479_ = lean_nat_dec_lt(v_start_3477_, v_stop_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec_ref(v_xs_3459_);
lean_dec_ref(v_a_3458_);
if (v_isShared_3475_ == 0)
{
v___x_3481_ = v___x_3474_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_fst_3472_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_snd_3471_);
v___x_3481_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
}
else
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3511_; 
lean_inc(v_stop_3478_);
lean_inc(v_start_3477_);
lean_inc_ref(v_array_3476_);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_snd_3471_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; lean_object* v_unused_3513_; lean_object* v_unused_3514_; 
v_unused_3512_ = lean_ctor_get(v_snd_3471_, 2);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_snd_3471_, 1);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_snd_3471_, 0);
lean_dec(v_unused_3514_);
v___x_3485_ = v_snd_3471_;
v_isShared_3486_ = v_isSharedCheck_3511_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v_snd_3471_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3511_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v_a_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_a_3487_ = lean_array_uget_borrowed(v_as_3460_, v_i_3462_);
v___x_3488_ = lean_array_fget_borrowed(v_array_3476_, v_start_3477_);
lean_inc(v___y_3467_);
lean_inc_ref(v___y_3466_);
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v_a_3487_);
lean_inc_ref(v_xs_3459_);
lean_inc_ref(v_a_3458_);
v___x_3489_ = l_Lean_Elab_Structural_argsInGroup(v_a_3458_, v_xs_3459_, v_a_3487_, v___x_3488_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
v___x_3491_ = lean_unsigned_to_nat(1u);
v___x_3492_ = lean_nat_add(v_start_3477_, v___x_3491_);
lean_dec(v_start_3477_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___x_3492_);
v___x_3494_ = v___x_3485_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_array_3476_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_stop_3478_);
v___x_3494_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_array_push(v_fst_3472_, v_a_3490_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 1, v___x_3494_);
lean_ctor_set(v___x_3474_, 0, v___x_3495_);
v___x_3497_ = v___x_3474_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3494_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
size_t v___x_3498_; size_t v___x_3499_; 
v___x_3498_ = ((size_t)1ULL);
v___x_3499_ = lean_usize_add(v_i_3462_, v___x_3498_);
v_i_3462_ = v___x_3499_;
v_b_3463_ = v___x_3497_;
goto _start;
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_del_object(v___x_3485_);
lean_dec(v_stop_3478_);
lean_dec(v_start_3477_);
lean_dec_ref(v_array_3476_);
lean_del_object(v___x_3474_);
lean_dec(v_fst_3472_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec_ref(v_xs_3459_);
lean_dec_ref(v_a_3458_);
v_a_3503_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3489_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3489_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg___boxed(lean_object* v_a_3516_, lean_object* v_xs_3517_, lean_object* v_as_3518_, lean_object* v_sz_3519_, lean_object* v_i_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
size_t v_sz_boxed_3527_; size_t v_i_boxed_3528_; lean_object* v_res_3529_; 
v_sz_boxed_3527_ = lean_unbox_usize(v_sz_3519_);
lean_dec(v_sz_3519_);
v_i_boxed_3528_ = lean_unbox_usize(v_i_3520_);
lean_dec(v_i_3520_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(v_a_3516_, v_xs_3517_, v_as_3518_, v_sz_boxed_3527_, v_i_boxed_3528_, v_b_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec_ref(v_as_3518_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(lean_object* v_msg_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_ref_3536_; lean_object* v___x_3537_; lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3546_; 
v_ref_3536_ = lean_ctor_get(v___y_3533_, 5);
v___x_3537_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_inc(v_ref_3536_);
v___x_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3542_, 0, v_ref_3536_);
lean_ctor_set(v___x_3542_, 1, v_a_3538_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set_tag(v___x_3540_, 1);
lean_ctor_set(v___x_3540_, 0, v___x_3542_);
v___x_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg___boxed(lean_object* v_msg_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(v_msg_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(lean_object* v_cls_3554_, lean_object* v_msg_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_ref_3561_; lean_object* v___x_3562_; lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3607_; 
v_ref_3561_ = lean_ctor_get(v___y_3558_, 5);
v___x_3562_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v_msg_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3607_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3607_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v_traceState_3568_; lean_object* v_env_3569_; lean_object* v_nextMacroScope_3570_; lean_object* v_ngen_3571_; lean_object* v_auxDeclNGen_3572_; lean_object* v_cache_3573_; lean_object* v_messages_3574_; lean_object* v_infoState_3575_; lean_object* v_snapshotTasks_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3606_; 
v___x_3567_ = lean_st_ref_take(v___y_3559_);
v_traceState_3568_ = lean_ctor_get(v___x_3567_, 4);
v_env_3569_ = lean_ctor_get(v___x_3567_, 0);
v_nextMacroScope_3570_ = lean_ctor_get(v___x_3567_, 1);
v_ngen_3571_ = lean_ctor_get(v___x_3567_, 2);
v_auxDeclNGen_3572_ = lean_ctor_get(v___x_3567_, 3);
v_cache_3573_ = lean_ctor_get(v___x_3567_, 5);
v_messages_3574_ = lean_ctor_get(v___x_3567_, 6);
v_infoState_3575_ = lean_ctor_get(v___x_3567_, 7);
v_snapshotTasks_3576_ = lean_ctor_get(v___x_3567_, 8);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3578_ = v___x_3567_;
v_isShared_3579_ = v_isSharedCheck_3606_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_snapshotTasks_3576_);
lean_inc(v_infoState_3575_);
lean_inc(v_messages_3574_);
lean_inc(v_cache_3573_);
lean_inc(v_traceState_3568_);
lean_inc(v_auxDeclNGen_3572_);
lean_inc(v_ngen_3571_);
lean_inc(v_nextMacroScope_3570_);
lean_inc(v_env_3569_);
lean_dec(v___x_3567_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3606_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
uint64_t v_tid_3580_; lean_object* v_traces_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3605_; 
v_tid_3580_ = lean_ctor_get_uint64(v_traceState_3568_, sizeof(void*)*1);
v_traces_3581_ = lean_ctor_get(v_traceState_3568_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_traceState_3568_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3583_ = v_traceState_3568_;
v_isShared_3584_ = v_isSharedCheck_3605_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_traces_3581_);
lean_dec(v_traceState_3568_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3605_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; double v___x_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__0);
v___x_3587_ = 0;
v___x_3588_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___closed__1));
v___x_3589_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3589_, 0, v_cls_3554_);
lean_ctor_set(v___x_3589_, 1, v___x_3585_);
lean_ctor_set(v___x_3589_, 2, v___x_3588_);
lean_ctor_set_float(v___x_3589_, sizeof(void*)*3, v___x_3586_);
lean_ctor_set_float(v___x_3589_, sizeof(void*)*3 + 8, v___x_3586_);
lean_ctor_set_uint8(v___x_3589_, sizeof(void*)*3 + 16, v___x_3587_);
v___x_3590_ = ((lean_object*)(l_Lean_Elab_Structural_prettyParameterSet___closed__0));
v___x_3591_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v_a_3563_);
lean_ctor_set(v___x_3591_, 2, v___x_3590_);
lean_inc(v_ref_3561_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v_ref_3561_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = l_Lean_PersistentArray_push___redArg(v_traces_3581_, v___x_3592_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3593_);
v___x_3595_ = v___x_3583_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3593_);
lean_ctor_set_uint64(v_reuseFailAlloc_3604_, sizeof(void*)*1, v_tid_3580_);
v___x_3595_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 4, v___x_3595_);
v___x_3597_ = v___x_3578_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_env_3569_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_nextMacroScope_3570_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_ngen_3571_);
lean_ctor_set(v_reuseFailAlloc_3603_, 3, v_auxDeclNGen_3572_);
lean_ctor_set(v_reuseFailAlloc_3603_, 4, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3603_, 5, v_cache_3573_);
lean_ctor_set(v_reuseFailAlloc_3603_, 6, v_messages_3574_);
lean_ctor_set(v_reuseFailAlloc_3603_, 7, v_infoState_3575_);
lean_ctor_set(v_reuseFailAlloc_3603_, 8, v_snapshotTasks_3576_);
v___x_3597_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3598_ = lean_st_ref_set(v___y_3559_, v___x_3597_);
v___x_3599_ = lean_box(0);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3599_);
v___x_3601_ = v___x_3565_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg___boxed(lean_object* v_cls_3608_, lean_object* v_msg_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v_cls_3608_, v_msg_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
return v_res_3615_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__0));
v___x_3618_ = l_Lean_stringToMessageData(v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0(lean_object* v_k_3619_, lean_object* v_a_3620_, lean_object* v___x_3621_, lean_object* v_snd_3622_, lean_object* v_____r_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
lean_inc(v___y_3628_);
lean_inc_ref(v___y_3627_);
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
v___x_3630_ = lean_apply_7(v_k_3619_, v_a_3620_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, lean_box(0));
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3662_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3662_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3662_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3640_; 
lean_inc(v___x_3621_);
v___x_3640_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v___x_3621_, v___y_3627_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; uint8_t v___x_3642_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
v___x_3642_ = lean_unbox(v_a_3641_);
lean_dec(v_a_3641_);
if (v___x_3642_ == 0)
{
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_snd_3622_);
lean_dec(v___x_3621_);
goto v___jp_3635_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___closed__1);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v_snd_3622_);
v___x_3645_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v___x_3621_, v___x_3644_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_dec_ref(v___x_3645_);
goto v___jp_3635_;
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_del_object(v___x_3633_);
lean_dec(v_a_3631_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_snd_3622_);
lean_dec(v___x_3621_);
v_a_3654_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3640_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3640_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
v___jp_3635_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v_a_3631_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3636_);
v___x_3638_ = v___x_3633_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_snd_3622_);
lean_dec(v___x_3621_);
v_a_3663_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3630_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3630_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0___boxed(lean_object* v_k_3671_, lean_object* v_a_3672_, lean_object* v___x_3673_, lean_object* v_snd_3674_, lean_object* v_____r_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0(v_k_3671_, v_a_3672_, v___x_3673_, v_snd_3674_, v_____r_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v_res_3682_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__0));
v___x_3685_ = l_Lean_stringToMessageData(v___x_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__4));
v___x_3687_ = l_Lean_stringToMessageData(v___x_3686_);
return v___x_3687_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__3));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__5));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(lean_object* v_fnNames_3694_, lean_object* v_xs_3695_, lean_object* v_values_3696_, lean_object* v_k_3697_, lean_object* v_a_3698_, lean_object* v_as_3699_, size_t v_sz_3700_, size_t v_i_3701_, lean_object* v_b_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_usize_dec_lt(v_i_3701_, v_sz_3700_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v_a_3698_);
lean_dec_ref(v_k_3697_);
lean_dec_ref(v_values_3696_);
lean_dec_ref(v_xs_3695_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_b_3702_);
return v___x_3710_;
}
else
{
lean_object* v_snd_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3794_; 
v_snd_3711_ = lean_ctor_get(v_b_3702_, 1);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_b_3702_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v_b_3702_, 0);
lean_dec(v_unused_3795_);
v___x_3713_ = v_b_3702_;
v_isShared_3714_ = v_isSharedCheck_3794_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_snd_3711_);
lean_dec(v_b_3702_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3794_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_toIndGroupInfo_3715_; lean_object* v___x_3716_; lean_object* v_snd_3718_; lean_object* v_a_3725_; lean_object* v___y_3727_; uint8_t v___y_3728_; lean_object* v_a_3751_; lean_object* v___y_3755_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_toIndGroupInfo_3715_ = lean_ctor_get(v_a_3698_, 0);
v___x_3716_ = lean_box(0);
v_a_3725_ = lean_array_uget_borrowed(v_as_3699_, v_i_3701_);
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_3715_, v___x_3776_);
v___x_3778_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryAllArgs_spec__4___redArg(v___x_3777_, v___x_3709_, v___y_3707_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_3781_ = lean_unbox(v_a_3779_);
lean_dec(v_a_3779_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__4);
lean_inc_ref(v_a_3698_);
v___x_3783_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3698_);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__6);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(v___x_3786_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3706_);
lean_inc(v___y_3705_);
lean_inc_ref(v___y_3704_);
lean_inc(v___y_3703_);
lean_inc(v_snd_3711_);
lean_inc(v_a_3725_);
lean_inc_ref(v_k_3697_);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0(v_k_3697_, v_a_3725_, v___x_3780_, v_snd_3711_, v_a_3788_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
v___y_3755_ = v___x_3789_;
goto v___jp_3754_;
}
else
{
lean_object* v_a_3790_; 
v_a_3790_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3787_);
v_a_3751_ = v_a_3790_;
goto v___jp_3750_;
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_box(0);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3706_);
lean_inc(v___y_3705_);
lean_inc_ref(v___y_3704_);
lean_inc(v___y_3703_);
lean_inc(v_snd_3711_);
lean_inc(v_a_3725_);
lean_inc_ref(v_k_3697_);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___lam__0(v_k_3697_, v_a_3725_, v___x_3780_, v_snd_3711_, v___x_3791_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
v___y_3755_ = v___x_3792_;
goto v___jp_3754_;
}
}
else
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3778_);
v_a_3751_ = v_a_3793_;
goto v___jp_3750_;
}
v___jp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_snd_3718_);
lean_ctor_set(v___x_3713_, 0, v___x_3716_);
v___x_3720_ = v___x_3713_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_snd_3718_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
size_t v___x_3721_; size_t v___x_3722_; 
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3701_, v___x_3721_);
v_i_3701_ = v___x_3722_;
v_b_3702_ = v___x_3720_;
goto _start;
}
}
v___jp_3726_:
{
if (v___y_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3706_);
lean_inc(v___y_3705_);
lean_inc_ref(v___y_3704_);
lean_inc(v_a_3725_);
lean_inc_ref(v_values_3696_);
lean_inc_ref(v_xs_3695_);
v___x_3729_ = l_Lean_Elab_Structural_prettyParameterSet(v_fnNames_3694_, v_xs_3695_, v_values_3696_, v_a_3725_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref(v___x_3729_);
v___x_3731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__1);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v_a_3730_);
v___x_3733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__2___redArg___closed__3);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_Exception_toMessageData(v___y_3727_);
v___x_3736_ = l_Lean_indentD(v___x_3735_);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3734_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___closed__2);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_snd_3711_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v_snd_3718_ = v___x_3740_;
goto v___jp_3717_;
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v___y_3727_);
lean_del_object(v___x_3713_);
lean_dec(v_snd_3711_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v_a_3698_);
lean_dec_ref(v_k_3697_);
lean_dec_ref(v_values_3696_);
lean_dec_ref(v_xs_3695_);
v_a_3741_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3729_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3729_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v___x_3749_; 
lean_del_object(v___x_3713_);
lean_dec(v_snd_3711_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v_a_3698_);
lean_dec_ref(v_k_3697_);
lean_dec_ref(v_values_3696_);
lean_dec_ref(v_xs_3695_);
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___y_3727_);
return v___x_3749_;
}
}
v___jp_3750_:
{
uint8_t v___x_3752_; 
v___x_3752_ = l_Lean_Exception_isInterrupt(v_a_3751_);
if (v___x_3752_ == 0)
{
uint8_t v___x_3753_; 
lean_inc_ref(v_a_3751_);
v___x_3753_ = l_Lean_Exception_isRuntime(v_a_3751_);
v___y_3727_ = v_a_3751_;
v___y_3728_ = v___x_3753_;
goto v___jp_3726_;
}
else
{
v___y_3727_ = v_a_3751_;
v___y_3728_ = v___x_3752_;
goto v___jp_3726_;
}
}
v___jp_3754_:
{
if (lean_obj_tag(v___y_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3774_; 
v_a_3756_ = lean_ctor_get(v___y_3755_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___y_3755_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3758_ = v___y_3755_;
v_isShared_3759_ = v_isSharedCheck_3774_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___y_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3774_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
if (lean_obj_tag(v_a_3756_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3771_; 
lean_del_object(v___x_3713_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v_a_3698_);
lean_dec_ref(v_k_3697_);
lean_dec_ref(v_values_3696_);
lean_dec_ref(v_xs_3695_);
v_a_3760_ = lean_ctor_get(v_a_3756_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_a_3756_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3762_ = v_a_3756_;
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v_a_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 1);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_snd_3711_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3766_);
v___x_3768_ = v___x_3758_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v_snd_3773_; 
lean_del_object(v___x_3758_);
lean_dec(v_snd_3711_);
v_a_3772_ = lean_ctor_get(v_a_3756_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v_a_3756_);
v_snd_3773_ = lean_ctor_get(v_a_3772_, 1);
lean_inc(v_snd_3773_);
lean_dec(v_a_3772_);
v_snd_3718_ = v_snd_3773_;
goto v___jp_3717_;
}
}
}
else
{
lean_object* v_a_3775_; 
v_a_3775_ = lean_ctor_get(v___y_3755_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___y_3755_);
v_a_3751_ = v_a_3775_;
goto v___jp_3750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg___boxed(lean_object* v_fnNames_3796_, lean_object* v_xs_3797_, lean_object* v_values_3798_, lean_object* v_k_3799_, lean_object* v_a_3800_, lean_object* v_as_3801_, lean_object* v_sz_3802_, lean_object* v_i_3803_, lean_object* v_b_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
size_t v_sz_boxed_3811_; size_t v_i_boxed_3812_; lean_object* v_res_3813_; 
v_sz_boxed_3811_ = lean_unbox_usize(v_sz_3802_);
lean_dec(v_sz_3802_);
v_i_boxed_3812_ = lean_unbox_usize(v_i_3803_);
lean_dec(v_i_3803_);
v_res_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(v_fnNames_3796_, v_xs_3797_, v_values_3798_, v_k_3799_, v_a_3800_, v_as_3801_, v_sz_boxed_3811_, v_i_boxed_3812_, v_b_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec_ref(v_as_3801_);
lean_dec_ref(v_fnNames_3796_);
return v_res_3813_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0(lean_object* v___x_3814_, lean_object* v_x_3815_){
_start:
{
lean_object* v___x_3816_; uint8_t v___x_3817_; 
v___x_3816_ = lean_array_get_size(v_x_3815_);
v___x_3817_ = lean_nat_dec_eq(v___x_3816_, v___x_3814_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0___boxed(lean_object* v___x_3818_, lean_object* v_x_3819_){
_start:
{
uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_res_3820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___lam__0(v___x_3818_, v_x_3819_);
lean_dec_ref(v_x_3819_);
lean_dec(v___x_3818_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__2));
v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
return v___x_3828_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__4));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__6));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__8));
v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
return v___x_3837_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__10));
v___x_3840_ = l_Lean_stringToMessageData(v___x_3839_);
return v___x_3840_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__12));
v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg(lean_object* v___x_3844_, lean_object* v_values_3845_, lean_object* v_xs_3846_, lean_object* v_fnNames_3847_, lean_object* v_k_3848_, lean_object* v_as_3849_, size_t v_sz_3850_, size_t v_i_3851_, lean_object* v_b_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_a_3860_; uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3851_, v_sz_3850_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v_k_3848_);
lean_dec_ref(v_xs_3846_);
lean_dec_ref(v_values_3845_);
lean_dec_ref(v___x_3844_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_b_3852_);
return v___x_3865_;
}
else
{
lean_object* v___x_3866_; lean_object* v_recArgInfoss_3867_; lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0));
v_a_3868_ = lean_array_uget_borrowed(v_as_3849_, v_i_3851_);
v___x_3869_ = lean_array_get_size(v___x_3844_);
lean_inc_ref(v___x_3844_);
v___x_3870_ = l_Array_toSubarray___redArg(v___x_3844_, v___x_3866_, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v_recArgInfoss_3867_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v_sz_3872_ = lean_array_size(v_values_3845_);
v___x_3873_ = ((size_t)0ULL);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc_ref(v_xs_3846_);
lean_inc(v_a_3868_);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(v_a_3868_, v_xs_3846_, v_values_3845_, v_sz_3872_, v___x_3873_, v___x_3871_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v_snd_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3954_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v_snd_3876_ = lean_ctor_get(v_b_3852_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_b_3852_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; 
v_unused_3955_ = lean_ctor_get(v_b_3852_, 0);
lean_dec(v_unused_3955_);
v___x_3878_ = v_b_3852_;
v_isShared_3879_ = v_isSharedCheck_3954_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_snd_3876_);
lean_dec(v_b_3852_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3954_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v_fst_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3952_; 
v_fst_3880_ = lean_ctor_get(v_a_3875_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_a_3875_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; 
v_unused_3953_ = lean_ctor_get(v_a_3875_, 1);
lean_dec(v_unused_3953_);
v___x_3882_ = v_a_3875_;
v_isShared_3883_ = v_isSharedCheck_3952_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_fst_3880_);
lean_dec(v_a_3875_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3952_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___f_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___f_3884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__1));
v___x_3885_ = lean_box(0);
v___x_3886_ = l_Array_findIdx_x3f_loop___redArg(v___f_3884_, v_fst_3880_, v___x_3866_);
if (lean_obj_tag(v___x_3886_) == 1)
{
lean_object* v_val_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_dec(v_fst_3880_);
v_val_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_val_3887_);
lean_dec_ref(v___x_3886_);
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3);
lean_inc(v_a_3868_);
v___x_3890_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3868_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 7);
lean_ctor_set(v___x_3878_, 1, v___x_3890_);
lean_ctor_set(v___x_3878_, 0, v___x_3889_);
v___x_3892_ = v___x_3878_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_array_get_borrowed(v___x_3888_, v_fnNames_3847_, v_val_3887_);
lean_dec(v_val_3887_);
lean_inc(v___x_3895_);
v___x_3896_ = l_Lean_MessageData_ofName(v___x_3895_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3894_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v_snd_3876_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3900_);
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3902_ = v___x_3882_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
v_a_3860_ = v___x_3902_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v___x_3905_; 
lean_dec(v___x_3886_);
v___x_3905_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_3880_);
lean_dec(v_fst_3880_);
if (lean_obj_tag(v___x_3905_) == 1)
{
lean_object* v_val_3906_; lean_object* v___x_3908_; 
lean_del_object(v___x_3878_);
v_val_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_val_3906_);
lean_dec_ref(v___x_3905_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v_snd_3876_);
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3908_ = v___x_3882_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_snd_3876_);
v___x_3908_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
size_t v_sz_3909_; lean_object* v___x_3910_; 
v_sz_3909_ = lean_array_size(v_val_3906_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc(v___y_3853_);
lean_inc(v_a_3868_);
lean_inc_ref(v_k_3848_);
lean_inc_ref(v_values_3845_);
lean_inc_ref(v_xs_3846_);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(v_fnNames_3847_, v_xs_3846_, v_values_3845_, v_k_3848_, v_a_3868_, v_val_3906_, v_sz_3909_, v___x_3873_, v___x_3908_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v_val_3906_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3937_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3937_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3937_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_fst_3915_; 
v_fst_3915_ = lean_ctor_get(v_a_3911_, 0);
if (lean_obj_tag(v_fst_3915_) == 0)
{
lean_object* v_snd_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_del_object(v___x_3913_);
v_snd_3916_ = lean_ctor_get(v_a_3911_, 1);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; 
v_unused_3924_ = lean_ctor_get(v_a_3911_, 0);
lean_dec(v_unused_3924_);
v___x_3918_ = v_a_3911_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_snd_3916_);
lean_dec(v_a_3911_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3885_);
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_snd_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
v_a_3860_ = v___x_3921_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v_snd_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3935_; 
lean_inc_ref(v_fst_3915_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v_k_3848_);
lean_dec_ref(v_xs_3846_);
lean_dec_ref(v_values_3845_);
lean_dec_ref(v___x_3844_);
v_snd_3925_ = lean_ctor_get(v_a_3911_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v_a_3911_, 0);
lean_dec(v_unused_3936_);
v___x_3927_ = v_a_3911_;
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snd_3925_);
lean_dec(v_a_3911_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_fst_3915_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_snd_3925_);
v___x_3930_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3930_);
v___x_3932_ = v___x_3913_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
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
else
{
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v_k_3848_);
lean_dec_ref(v_xs_3846_);
lean_dec_ref(v_values_3845_);
lean_dec_ref(v___x_3844_);
return v___x_3910_;
}
}
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_dec(v___x_3905_);
v___x_3939_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9);
lean_inc(v_a_3868_);
v___x_3940_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_3868_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 7);
lean_ctor_set(v___x_3878_, 1, v___x_3940_);
lean_ctor_set(v___x_3878_, 0, v___x_3939_);
v___x_3942_ = v___x_3878_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_snd_3876_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3947_);
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3949_ = v___x_3882_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
v_a_3860_ = v___x_3949_;
goto v___jp_3859_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v_b_3852_);
lean_dec_ref(v_k_3848_);
lean_dec_ref(v_xs_3846_);
lean_dec_ref(v_values_3845_);
lean_dec_ref(v___x_3844_);
v_a_3956_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3874_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3874_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3851_, v___x_3861_);
v_i_3851_ = v___x_3862_;
v_b_3852_ = v_a_3860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___boxed(lean_object* v___x_3964_, lean_object* v_values_3965_, lean_object* v_xs_3966_, lean_object* v_fnNames_3967_, lean_object* v_k_3968_, lean_object* v_as_3969_, lean_object* v_sz_3970_, lean_object* v_i_3971_, lean_object* v_b_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
size_t v_sz_boxed_3979_; size_t v_i_boxed_3980_; lean_object* v_res_3981_; 
v_sz_boxed_3979_ = lean_unbox_usize(v_sz_3970_);
lean_dec(v_sz_3970_);
v_i_boxed_3980_ = lean_unbox_usize(v_i_3971_);
lean_dec(v_i_3971_);
v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg(v___x_3964_, v_values_3965_, v_xs_3966_, v_fnNames_3967_, v_k_3968_, v_as_3969_, v_sz_boxed_3979_, v_i_boxed_3980_, v_b_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec_ref(v_as_3969_);
lean_dec_ref(v_fnNames_3967_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg(lean_object* v_fnNames_3982_, lean_object* v_xs_3983_, lean_object* v_values_3984_, lean_object* v_k_3985_, lean_object* v___x_3986_, lean_object* v_as_3987_, size_t v_sz_3988_, size_t v_i_3989_, lean_object* v_b_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_a_3998_; uint8_t v___x_4002_; 
v___x_4002_ = lean_usize_dec_lt(v_i_3989_, v_sz_3988_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_k_3985_);
lean_dec_ref(v_values_3984_);
lean_dec_ref(v_xs_3983_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v_b_3990_);
return v___x_4003_;
}
else
{
lean_object* v___x_4004_; lean_object* v_recArgInfoss_4005_; lean_object* v_a_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; size_t v_sz_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v___x_4004_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_4005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0));
v_a_4006_ = lean_array_uget_borrowed(v_as_3987_, v_i_3989_);
v___x_4007_ = lean_array_get_size(v___x_3986_);
lean_inc_ref(v___x_3986_);
v___x_4008_ = l_Array_toSubarray___redArg(v___x_3986_, v___x_4004_, v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v_recArgInfoss_4005_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v_sz_4010_ = lean_array_size(v_values_3984_);
v___x_4011_ = ((size_t)0ULL);
lean_inc(v___y_3995_);
lean_inc_ref(v___y_3994_);
lean_inc(v___y_3993_);
lean_inc_ref(v___y_3992_);
lean_inc_ref(v_xs_3983_);
lean_inc(v_a_4006_);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(v_a_4006_, v_xs_3983_, v_values_3984_, v_sz_4010_, v___x_4011_, v___x_4009_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_snd_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4092_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_4012_);
v_snd_4014_ = lean_ctor_get(v_b_3990_, 1);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_b_3990_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v_b_3990_, 0);
lean_dec(v_unused_4093_);
v___x_4016_ = v_b_3990_;
v_isShared_4017_ = v_isSharedCheck_4092_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_snd_4014_);
lean_dec(v_b_3990_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4092_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_fst_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4090_; 
v_fst_4018_ = lean_ctor_get(v_a_4013_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_a_4013_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_a_4013_, 1);
lean_dec(v_unused_4091_);
v___x_4020_ = v_a_4013_;
v_isShared_4021_ = v_isSharedCheck_4090_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_fst_4018_);
lean_dec(v_a_4013_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4090_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___f_4023_; lean_object* v___x_4024_; 
v___x_4022_ = lean_box(0);
v___f_4023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__1));
v___x_4024_ = l_Array_findIdx_x3f_loop___redArg(v___f_4023_, v_fst_4018_, v___x_4004_);
if (lean_obj_tag(v___x_4024_) == 1)
{
lean_object* v_val_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
lean_dec(v_fst_4018_);
v_val_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_val_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = lean_box(0);
v___x_4027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__3);
lean_inc(v_a_4006_);
v___x_4028_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_4006_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set_tag(v___x_4016_, 7);
lean_ctor_set(v___x_4016_, 1, v___x_4028_);
lean_ctor_set(v___x_4016_, 0, v___x_4027_);
v___x_4030_ = v___x_4016_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__5);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_array_get_borrowed(v___x_4026_, v_fnNames_3982_, v_val_4025_);
lean_dec(v_val_4025_);
lean_inc(v___x_4033_);
v___x_4034_ = l_Lean_MessageData_ofName(v___x_4033_);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4032_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__7);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v_snd_4014_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v___x_4038_);
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4040_ = v___x_4020_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
v_a_3998_ = v___x_4040_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v___x_4043_; 
lean_dec(v___x_4024_);
v___x_4043_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_4018_);
lean_dec(v_fst_4018_);
if (lean_obj_tag(v___x_4043_) == 1)
{
lean_object* v_val_4044_; lean_object* v___x_4046_; 
lean_del_object(v___x_4016_);
v_val_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_val_4044_);
lean_dec_ref(v___x_4043_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v_snd_4014_);
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4046_ = v___x_4020_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_snd_4014_);
v___x_4046_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
size_t v_sz_4047_; lean_object* v___x_4048_; 
v_sz_4047_ = lean_array_size(v_val_4044_);
lean_inc(v___y_3995_);
lean_inc_ref(v___y_3994_);
lean_inc(v___y_3993_);
lean_inc_ref(v___y_3992_);
lean_inc(v___y_3991_);
lean_inc(v_a_4006_);
lean_inc_ref(v_k_3985_);
lean_inc_ref(v_values_3984_);
lean_inc_ref(v_xs_3983_);
v___x_4048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(v_fnNames_3982_, v_xs_3983_, v_values_3984_, v_k_3985_, v_a_4006_, v_val_4044_, v_sz_4047_, v___x_4011_, v___x_4046_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v_val_4044_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4075_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4075_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4075_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_fst_4053_; 
v_fst_4053_ = lean_ctor_get(v_a_4049_, 0);
if (lean_obj_tag(v_fst_4053_) == 0)
{
lean_object* v_snd_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_del_object(v___x_4051_);
v_snd_4054_ = lean_ctor_get(v_a_4049_, 1);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_a_4049_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; 
v_unused_4062_ = lean_ctor_get(v_a_4049_, 0);
lean_dec(v_unused_4062_);
v___x_4056_ = v_a_4049_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_snd_4054_);
lean_dec(v_a_4049_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v___x_4022_);
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_snd_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
v_a_3998_ = v___x_4059_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_snd_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4073_; 
lean_inc_ref(v_fst_4053_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_k_3985_);
lean_dec_ref(v_values_3984_);
lean_dec_ref(v_xs_3983_);
v_snd_4063_ = lean_ctor_get(v_a_4049_, 1);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_a_4049_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; 
v_unused_4074_ = lean_ctor_get(v_a_4049_, 0);
lean_dec(v_unused_4074_);
v___x_4065_ = v_a_4049_;
v_isShared_4066_ = v_isSharedCheck_4073_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_snd_4063_);
lean_dec(v_a_4049_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4073_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_fst_4053_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_snd_4063_);
v___x_4068_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4070_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4068_);
v___x_4070_ = v___x_4051_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
else
{
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_k_3985_);
lean_dec_ref(v_values_3984_);
lean_dec_ref(v_xs_3983_);
return v___x_4048_;
}
}
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
lean_dec(v___x_4043_);
v___x_4077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__9);
lean_inc(v_a_4006_);
v___x_4078_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_4006_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set_tag(v___x_4016_, 7);
lean_ctor_set(v___x_4016_, 1, v___x_4078_);
lean_ctor_set(v___x_4016_, 0, v___x_4077_);
v___x_4080_ = v___x_4016_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4081_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__11);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v_snd_4014_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__13);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 1, v___x_4085_);
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4087_ = v___x_4020_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
v_a_3998_ = v___x_4087_;
goto v___jp_3997_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v_b_3990_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_k_3985_);
lean_dec_ref(v_values_3984_);
lean_dec_ref(v_xs_3983_);
v_a_4094_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4012_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4012_);
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
v___jp_3997_:
{
size_t v___x_3999_; size_t v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = lean_usize_add(v_i_3989_, v___x_3999_);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg(v___x_3986_, v_values_3984_, v_xs_3983_, v_fnNames_3982_, v_k_3985_, v_as_3987_, v_sz_3988_, v___x_4000_, v_a_3998_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg___boxed(lean_object* v_fnNames_4102_, lean_object* v_xs_4103_, lean_object* v_values_4104_, lean_object* v_k_4105_, lean_object* v___x_4106_, lean_object* v_as_4107_, lean_object* v_sz_4108_, lean_object* v_i_4109_, lean_object* v_b_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
size_t v_sz_boxed_4117_; size_t v_i_boxed_4118_; lean_object* v_res_4119_; 
v_sz_boxed_4117_ = lean_unbox_usize(v_sz_4108_);
lean_dec(v_sz_4108_);
v_i_boxed_4118_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_res_4119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg(v_fnNames_4102_, v_xs_4103_, v_values_4104_, v_k_4105_, v___x_4106_, v_as_4107_, v_sz_boxed_4117_, v_i_boxed_4118_, v_b_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec_ref(v_as_4107_);
lean_dec_ref(v_fnNames_4102_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__11(lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
if (lean_obj_tag(v_a_4120_) == 0)
{
lean_object* v___x_4122_; 
v___x_4122_ = l_List_reverse___redArg(v_a_4121_);
return v___x_4122_;
}
else
{
lean_object* v_head_4123_; lean_object* v_tail_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4134_; 
v_head_4123_ = lean_ctor_get(v_a_4120_, 0);
v_tail_4124_ = lean_ctor_get(v_a_4120_, 1);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_a_4120_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4126_ = v_a_4120_;
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_tail_4124_);
lean_inc(v_head_4123_);
lean_dec(v_a_4120_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4128_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_4123_);
v___x_4129_ = l_Lean_MessageData_ofFormat(v___x_4128_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 1, v_a_4121_);
lean_ctor_set(v___x_4126_, 0, v___x_4129_);
v___x_4131_ = v___x_4126_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_a_4121_);
v___x_4131_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
v_a_4120_ = v_tail_4124_;
v_a_4121_ = v___x_4131_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg(lean_object* v_xs_4135_, lean_object* v_as_4136_, size_t v_sz_4137_, size_t v_i_4138_, lean_object* v_b_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
uint8_t v___x_4145_; 
v___x_4145_ = lean_usize_dec_lt(v_i_4138_, v_sz_4137_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; 
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_xs_4135_);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_b_4139_);
return v___x_4146_;
}
else
{
lean_object* v_snd_4147_; lean_object* v_snd_4148_; lean_object* v_snd_4149_; lean_object* v_snd_4150_; lean_object* v_fst_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4295_; 
v_snd_4147_ = lean_ctor_get(v_b_4139_, 1);
lean_inc(v_snd_4147_);
v_snd_4148_ = lean_ctor_get(v_snd_4147_, 1);
lean_inc(v_snd_4148_);
v_snd_4149_ = lean_ctor_get(v_snd_4148_, 1);
lean_inc(v_snd_4149_);
v_snd_4150_ = lean_ctor_get(v_snd_4149_, 1);
lean_inc(v_snd_4150_);
v_fst_4151_ = lean_ctor_get(v_b_4139_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_b_4139_);
if (v_isSharedCheck_4295_ == 0)
{
lean_object* v_unused_4296_; 
v_unused_4296_ = lean_ctor_get(v_b_4139_, 1);
lean_dec(v_unused_4296_);
v___x_4153_ = v_b_4139_;
v_isShared_4154_ = v_isSharedCheck_4295_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_fst_4151_);
lean_dec(v_b_4139_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4295_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v_fst_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4293_; 
v_fst_4155_ = lean_ctor_get(v_snd_4147_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_snd_4147_);
if (v_isSharedCheck_4293_ == 0)
{
lean_object* v_unused_4294_; 
v_unused_4294_ = lean_ctor_get(v_snd_4147_, 1);
lean_dec(v_unused_4294_);
v___x_4157_ = v_snd_4147_;
v_isShared_4158_ = v_isSharedCheck_4293_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_fst_4155_);
lean_dec(v_snd_4147_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4293_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v_fst_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4291_; 
v_fst_4159_ = lean_ctor_get(v_snd_4148_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_snd_4148_);
if (v_isSharedCheck_4291_ == 0)
{
lean_object* v_unused_4292_; 
v_unused_4292_ = lean_ctor_get(v_snd_4148_, 1);
lean_dec(v_unused_4292_);
v___x_4161_ = v_snd_4148_;
v_isShared_4162_ = v_isSharedCheck_4291_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_fst_4159_);
lean_dec(v_snd_4148_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4291_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4289_; 
v_fst_4163_ = lean_ctor_get(v_snd_4149_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v_snd_4149_);
if (v_isSharedCheck_4289_ == 0)
{
lean_object* v_unused_4290_; 
v_unused_4290_ = lean_ctor_get(v_snd_4149_, 1);
lean_dec(v_unused_4290_);
v___x_4165_ = v_snd_4149_;
v_isShared_4166_ = v_isSharedCheck_4289_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_fst_4163_);
lean_dec(v_snd_4149_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4289_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v_array_4167_; lean_object* v_start_4168_; lean_object* v_stop_4169_; uint8_t v___x_4170_; 
v_array_4167_ = lean_ctor_get(v_snd_4150_, 0);
v_start_4168_ = lean_ctor_get(v_snd_4150_, 1);
v_stop_4169_ = lean_ctor_get(v_snd_4150_, 2);
v___x_4170_ = lean_nat_dec_lt(v_start_4168_, v_stop_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4172_; 
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_xs_4135_);
if (v_isShared_4166_ == 0)
{
v___x_4172_ = v___x_4165_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_fst_4163_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_snd_4150_);
v___x_4172_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4174_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v___x_4172_);
v___x_4174_ = v___x_4161_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_fst_4159_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4176_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4174_);
v___x_4176_ = v___x_4157_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_fst_4155_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_object* v___x_4178_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 1, v___x_4176_);
v___x_4178_ = v___x_4153_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_fst_4151_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
}
}
}
}
else
{
lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4285_; 
lean_inc(v_stop_4169_);
lean_inc(v_start_4168_);
lean_inc_ref(v_array_4167_);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_snd_4150_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; lean_object* v_unused_4287_; lean_object* v_unused_4288_; 
v_unused_4286_ = lean_ctor_get(v_snd_4150_, 2);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v_snd_4150_, 1);
lean_dec(v_unused_4287_);
v_unused_4288_ = lean_ctor_get(v_snd_4150_, 0);
lean_dec(v_unused_4288_);
v___x_4185_ = v_snd_4150_;
v_isShared_4186_ = v_isSharedCheck_4285_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v_snd_4150_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4285_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_array_4187_; lean_object* v_start_4188_; lean_object* v_stop_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4194_; 
v_array_4187_ = lean_ctor_get(v_fst_4163_, 0);
v_start_4188_ = lean_ctor_get(v_fst_4163_, 1);
v_stop_4189_ = lean_ctor_get(v_fst_4163_, 2);
v___x_4190_ = lean_array_fget(v_array_4167_, v_start_4168_);
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_add(v_start_4168_, v___x_4191_);
lean_dec(v_start_4168_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v___x_4192_);
v___x_4194_ = v___x_4185_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_array_4167_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v___x_4192_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_stop_4169_);
v___x_4194_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
uint8_t v___x_4195_; 
v___x_4195_ = lean_nat_dec_lt(v_start_4188_, v_stop_4189_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4197_; 
lean_dec(v___x_4190_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_xs_4135_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___x_4194_);
v___x_4197_ = v___x_4165_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_fst_4163_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4194_);
v___x_4197_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4199_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v___x_4197_);
v___x_4199_ = v___x_4161_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_fst_4159_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4201_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4199_);
v___x_4201_ = v___x_4157_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_fst_4155_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4203_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 1, v___x_4201_);
v___x_4203_ = v___x_4153_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_fst_4151_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
}
}
else
{
lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4280_; 
lean_inc(v_stop_4189_);
lean_inc(v_start_4188_);
lean_inc_ref(v_array_4187_);
v_isSharedCheck_4280_ = !lean_is_exclusive(v_fst_4163_);
if (v_isSharedCheck_4280_ == 0)
{
lean_object* v_unused_4281_; lean_object* v_unused_4282_; lean_object* v_unused_4283_; 
v_unused_4281_ = lean_ctor_get(v_fst_4163_, 2);
lean_dec(v_unused_4281_);
v_unused_4282_ = lean_ctor_get(v_fst_4163_, 1);
lean_dec(v_unused_4282_);
v_unused_4283_ = lean_ctor_get(v_fst_4163_, 0);
lean_dec(v_unused_4283_);
v___x_4210_ = v_fst_4163_;
v_isShared_4211_ = v_isSharedCheck_4280_;
goto v_resetjp_4209_;
}
else
{
lean_dec(v_fst_4163_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4280_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v_array_4212_; lean_object* v_start_4213_; lean_object* v_stop_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4218_; 
v_array_4212_ = lean_ctor_get(v_fst_4159_, 0);
v_start_4213_ = lean_ctor_get(v_fst_4159_, 1);
v_stop_4214_ = lean_ctor_get(v_fst_4159_, 2);
v___x_4215_ = lean_array_fget(v_array_4187_, v_start_4188_);
v___x_4216_ = lean_nat_add(v_start_4188_, v___x_4191_);
lean_dec(v_start_4188_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 1, v___x_4216_);
v___x_4218_ = v___x_4210_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_array_4187_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4279_, 2, v_stop_4189_);
v___x_4218_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
uint8_t v___x_4219_; 
v___x_4219_ = lean_nat_dec_lt(v_start_4213_, v_stop_4214_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4221_; 
lean_dec(v___x_4215_);
lean_dec(v___x_4190_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_xs_4135_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___x_4194_);
lean_ctor_set(v___x_4165_, 0, v___x_4218_);
v___x_4221_ = v___x_4165_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v___x_4194_);
v___x_4221_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4223_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v___x_4221_);
v___x_4223_ = v___x_4161_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_fst_4159_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4223_);
v___x_4225_ = v___x_4157_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_fst_4155_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4227_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 1, v___x_4225_);
v___x_4227_ = v___x_4153_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_fst_4151_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
}
}
}
else
{
lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4275_; 
lean_inc(v_stop_4214_);
lean_inc(v_start_4213_);
lean_inc_ref(v_array_4212_);
lean_del_object(v___x_4153_);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_fst_4159_);
if (v_isSharedCheck_4275_ == 0)
{
lean_object* v_unused_4276_; lean_object* v_unused_4277_; lean_object* v_unused_4278_; 
v_unused_4276_ = lean_ctor_get(v_fst_4159_, 2);
lean_dec(v_unused_4276_);
v_unused_4277_ = lean_ctor_get(v_fst_4159_, 1);
lean_dec(v_unused_4277_);
v_unused_4278_ = lean_ctor_get(v_fst_4159_, 0);
lean_dec(v_unused_4278_);
v___x_4234_ = v_fst_4159_;
v_isShared_4235_ = v_isSharedCheck_4275_;
goto v_resetjp_4233_;
}
else
{
lean_dec(v_fst_4159_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4275_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v_a_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_a_4236_ = lean_array_uget_borrowed(v_as_4136_, v_i_4138_);
v___x_4237_ = lean_array_fget_borrowed(v_array_4212_, v_start_4213_);
lean_inc(v___y_4143_);
lean_inc_ref(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
lean_inc(v___x_4237_);
lean_inc_ref(v_xs_4135_);
lean_inc(v_a_4236_);
v___x_4238_ = l_Lean_Elab_Structural_getRecArgInfos(v_a_4236_, v___x_4190_, v_xs_4135_, v___x_4237_, v___x_4215_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v_fst_4240_; lean_object* v_snd_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4266_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref(v___x_4238_);
v_fst_4240_ = lean_ctor_get(v_a_4239_, 0);
v_snd_4241_ = lean_ctor_get(v_a_4239_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_a_4239_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4243_ = v_a_4239_;
v_isShared_4244_ = v_isSharedCheck_4266_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_snd_4241_);
lean_inc(v_fst_4240_);
lean_dec(v_a_4239_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4266_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4245_ = lean_nat_add(v_start_4213_, v___x_4191_);
lean_dec(v_start_4213_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___x_4245_);
v___x_4247_ = v___x_4234_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_array_4212_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4265_, 2, v_stop_4214_);
v___x_4247_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v_fst_4151_);
lean_ctor_set(v___x_4248_, 1, v_snd_4241_);
v___x_4249_ = lean_array_push(v_fst_4155_, v_fst_4240_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 1, v___x_4194_);
lean_ctor_set(v___x_4243_, 0, v___x_4218_);
v___x_4251_ = v___x_4243_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4218_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4194_);
v___x_4251_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4253_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___x_4251_);
lean_ctor_set(v___x_4165_, 0, v___x_4247_);
v___x_4253_ = v___x_4165_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4255_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v___x_4253_);
lean_ctor_set(v___x_4161_, 0, v___x_4249_);
v___x_4255_ = v___x_4161_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4249_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v___x_4253_);
v___x_4255_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4257_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4255_);
lean_ctor_set(v___x_4157_, 0, v___x_4248_);
v___x_4257_ = v___x_4157_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
size_t v___x_4258_; size_t v___x_4259_; 
v___x_4258_ = ((size_t)1ULL);
v___x_4259_ = lean_usize_add(v_i_4138_, v___x_4258_);
v_i_4138_ = v___x_4259_;
v_b_4139_ = v___x_4257_;
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
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_del_object(v___x_4234_);
lean_dec_ref(v___x_4218_);
lean_dec(v_stop_4214_);
lean_dec(v_start_4213_);
lean_dec_ref(v_array_4212_);
lean_dec_ref(v___x_4194_);
lean_del_object(v___x_4165_);
lean_del_object(v___x_4161_);
lean_del_object(v___x_4157_);
lean_dec(v_fst_4155_);
lean_dec(v_fst_4151_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_xs_4135_);
v_a_4267_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4238_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4238_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg___boxed(lean_object* v_xs_4297_, lean_object* v_as_4298_, lean_object* v_sz_4299_, lean_object* v_i_4300_, lean_object* v_b_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
size_t v_sz_boxed_4307_; size_t v_i_boxed_4308_; lean_object* v_res_4309_; 
v_sz_boxed_4307_ = lean_unbox_usize(v_sz_4299_);
lean_dec(v_sz_4299_);
v_i_boxed_4308_ = lean_unbox_usize(v_i_4300_);
lean_dec(v_i_4300_);
v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg(v_xs_4297_, v_as_4298_, v_sz_boxed_4307_, v_i_boxed_4308_, v_b_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec_ref(v_as_4298_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(lean_object* v_as_4310_, size_t v_i_4311_, size_t v_stop_4312_, lean_object* v_b_4313_){
_start:
{
uint8_t v___x_4314_; 
v___x_4314_ = lean_usize_dec_eq(v_i_4311_, v_stop_4312_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; lean_object* v___x_4316_; size_t v___x_4317_; size_t v___x_4318_; 
v___x_4315_ = lean_array_uget_borrowed(v_as_4310_, v_i_4311_);
v___x_4316_ = l_Array_append___redArg(v_b_4313_, v___x_4315_);
v___x_4317_ = ((size_t)1ULL);
v___x_4318_ = lean_usize_add(v_i_4311_, v___x_4317_);
v_i_4311_ = v___x_4318_;
v_b_4313_ = v___x_4316_;
goto _start;
}
else
{
return v_b_4313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10___boxed(lean_object* v_as_4320_, lean_object* v_i_4321_, lean_object* v_stop_4322_, lean_object* v_b_4323_){
_start:
{
size_t v_i_boxed_4324_; size_t v_stop_boxed_4325_; lean_object* v_res_4326_; 
v_i_boxed_4324_ = lean_unbox_usize(v_i_4321_);
lean_dec(v_i_4321_);
v_stop_boxed_4325_ = lean_unbox_usize(v_stop_4322_);
lean_dec(v_stop_4322_);
v_res_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(v_as_4320_, v_i_boxed_4324_, v_stop_boxed_4325_, v_b_4323_);
lean_dec_ref(v_as_4320_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__9(lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
if (lean_obj_tag(v_a_4327_) == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = l_List_reverse___redArg(v_a_4328_);
return v___x_4329_;
}
else
{
lean_object* v_head_4330_; lean_object* v_tail_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4340_; 
v_head_4330_ = lean_ctor_get(v_a_4327_, 0);
v_tail_4331_ = lean_ctor_get(v_a_4327_, 1);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_a_4327_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4333_ = v_a_4327_;
v_isShared_4334_ = v_isSharedCheck_4340_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_tail_4331_);
lean_inc(v_head_4330_);
lean_dec(v_a_4327_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4340_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; lean_object* v___x_4337_; 
v___x_4335_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_4330_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 1, v_a_4328_);
lean_ctor_set(v___x_4333_, 0, v___x_4335_);
v___x_4337_ = v___x_4333_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_a_4328_);
v___x_4337_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
v_a_4327_ = v_tail_4331_;
v_a_4328_ = v___x_4337_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2(size_t v_sz_4341_, size_t v_i_4342_, lean_object* v_bs_4343_){
_start:
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
if (v___x_4344_ == 0)
{
return v_bs_4343_;
}
else
{
lean_object* v_v_4345_; lean_object* v___x_4346_; lean_object* v_bs_x27_4347_; lean_object* v___x_4348_; size_t v___x_4349_; size_t v___x_4350_; lean_object* v___x_4351_; 
v_v_4345_ = lean_array_uget(v_bs_4343_, v_i_4342_);
v___x_4346_ = lean_unsigned_to_nat(0u);
v_bs_x27_4347_ = lean_array_uset(v_bs_4343_, v_i_4342_, v___x_4346_);
v___x_4348_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_4345_);
lean_dec(v_v_4345_);
v___x_4349_ = ((size_t)1ULL);
v___x_4350_ = lean_usize_add(v_i_4342_, v___x_4349_);
v___x_4351_ = lean_array_uset(v_bs_x27_4347_, v_i_4342_, v___x_4348_);
v_i_4342_ = v___x_4350_;
v_bs_4343_ = v___x_4351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2___boxed(lean_object* v_sz_4353_, lean_object* v_i_4354_, lean_object* v_bs_4355_){
_start:
{
size_t v_sz_boxed_4356_; size_t v_i_boxed_4357_; lean_object* v_res_4358_; 
v_sz_boxed_4356_ = lean_unbox_usize(v_sz_4353_);
lean_dec(v_sz_4353_);
v_i_boxed_4357_ = lean_unbox_usize(v_i_4354_);
lean_dec(v_i_4354_);
v_res_4358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2(v_sz_boxed_4356_, v_i_boxed_4357_, v_bs_4355_);
return v_res_4358_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1(void){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__0));
v___x_4361_ = l_Lean_stringToMessageData(v___x_4360_);
return v___x_4361_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3(void){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__2));
v___x_4364_ = l_Lean_stringToMessageData(v___x_4363_);
return v___x_4364_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__5));
v___x_4369_ = l_Lean_MessageData_ofFormat(v___x_4368_);
return v___x_4369_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__7));
v___x_4372_ = l_Lean_stringToMessageData(v___x_4371_);
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__10));
v___x_4377_ = l_Lean_stringToMessageData(v___x_4376_);
return v___x_4377_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_box(1);
v___x_4379_ = l_Lean_MessageData_ofFormat(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg(lean_object* v_fnNames_4380_, lean_object* v_fixedParamPerms_4381_, lean_object* v_xs_4382_, lean_object* v_values_4383_, lean_object* v_termMeasure_x3fs_4384_, lean_object* v_k_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4392_; lean_object* v_recArgInfoss_4393_; lean_object* v___x_4394_; lean_object* v_perms_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v_report_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; size_t v_sz_4406_; size_t v___x_4407_; lean_object* v___x_4408_; 
v___x_4392_ = lean_unsigned_to_nat(0u);
v_recArgInfoss_4393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg___closed__0));
v___x_4394_ = lean_array_get_size(v_values_4383_);
v_perms_4395_ = lean_ctor_get(v_fixedParamPerms_4381_, 1);
lean_inc_ref(v_perms_4395_);
lean_dec_ref(v_fixedParamPerms_4381_);
lean_inc_ref(v_values_4383_);
v___x_4396_ = l_Array_toSubarray___redArg(v_values_4383_, v___x_4392_, v___x_4394_);
v___x_4397_ = lean_array_get_size(v_termMeasure_x3fs_4384_);
v_report_4398_ = lean_obj_once(&l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3, &l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once, _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3);
v___x_4399_ = l_Array_toSubarray___redArg(v_termMeasure_x3fs_4384_, v___x_4392_, v___x_4397_);
v___x_4400_ = lean_array_get_size(v_perms_4395_);
v___x_4401_ = l_Array_toSubarray___redArg(v_perms_4395_, v___x_4392_, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4399_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4396_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v_recArgInfoss_4393_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v_report_4398_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v_sz_4406_ = lean_array_size(v_fnNames_4380_);
v___x_4407_ = ((size_t)0ULL);
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
lean_inc_ref(v_xs_4382_);
v___x_4408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg(v_xs_4382_, v_fnNames_4380_, v_sz_4406_, v___x_4407_, v___x_4405_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_snd_4410_; lean_object* v_fst_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4574_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_snd_4410_ = lean_ctor_get(v_a_4409_, 1);
v_fst_4411_ = lean_ctor_get(v_a_4409_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4413_ = v_a_4409_;
v_isShared_4414_ = v_isSharedCheck_4574_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_snd_4410_);
lean_inc(v_fst_4411_);
lean_dec(v_a_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4574_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v_fst_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4572_; 
v_fst_4415_ = lean_ctor_get(v_snd_4410_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_snd_4410_);
if (v_isSharedCheck_4572_ == 0)
{
lean_object* v_unused_4573_; 
v_unused_4573_ = lean_ctor_get(v_snd_4410_, 1);
lean_dec(v_unused_4573_);
v___x_4417_ = v_snd_4410_;
v_isShared_4418_ = v_isSharedCheck_4572_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_fst_4415_);
lean_dec(v_snd_4410_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4572_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_a_4421_; size_t v_sz_4422_; lean_object* v___x_4423_; lean_object* v___y_4425_; lean_object* v_report_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; uint8_t v___x_4544_; 
v___x_4419_ = ((lean_object*)(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9));
v___x_4420_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v___x_4419_, v_a_4389_);
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref(v___x_4420_);
v_sz_4422_ = lean_array_size(v_fst_4415_);
v___x_4423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_tryAllArgs_spec__2(v_sz_4422_, v___x_4407_, v_fst_4415_);
v___x_4544_ = lean_unbox(v_a_4421_);
lean_dec(v_a_4421_);
if (v___x_4544_ == 0)
{
v___y_4531_ = v_a_4386_;
v___y_4532_ = v_a_4387_;
v___y_4533_ = v_a_4388_;
v___y_4534_ = v_a_4389_;
v___y_4535_ = v_a_4390_;
goto v___jp_4530_;
}
else
{
lean_object* v___x_4545_; lean_object* v___y_4547_; lean_object* v___x_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4545_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__11);
v___x_4564_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__9));
v___x_4565_ = lean_array_get_size(v___x_4423_);
v___x_4566_ = lean_nat_dec_lt(v___x_4392_, v___x_4565_);
if (v___x_4566_ == 0)
{
v___y_4547_ = v___x_4564_;
goto v___jp_4546_;
}
else
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_nat_dec_le(v___x_4565_, v___x_4565_);
if (v___x_4567_ == 0)
{
if (v___x_4566_ == 0)
{
v___y_4547_ = v___x_4564_;
goto v___jp_4546_;
}
else
{
size_t v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_usize_of_nat(v___x_4565_);
v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(v___x_4423_, v___x_4407_, v___x_4568_, v___x_4564_);
v___y_4547_ = v___x_4569_;
goto v___jp_4546_;
}
}
else
{
size_t v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = lean_usize_of_nat(v___x_4565_);
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(v___x_4423_, v___x_4407_, v___x_4570_, v___x_4564_);
v___y_4547_ = v___x_4571_;
goto v___jp_4546_;
}
}
v___jp_4546_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4548_ = lean_array_to_list(v___y_4547_);
v___x_4549_ = lean_box(0);
v___x_4550_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__11(v___x_4548_, v___x_4549_);
v___x_4551_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__12);
v___x_4552_ = l_Lean_MessageData_joinSep(v___x_4550_, v___x_4551_);
v___x_4553_ = l_Lean_indentD(v___x_4552_);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4545_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v___x_4419_, v___x_4554_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_dec_ref(v___x_4555_);
v___y_4531_ = v_a_4386_;
v___y_4532_ = v_a_4387_;
v___y_4533_ = v_a_4388_;
v___y_4534_ = v_a_4389_;
v___y_4535_ = v_a_4390_;
goto v___jp_4530_;
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec_ref(v___x_4423_);
lean_del_object(v___x_4417_);
lean_del_object(v___x_4413_);
lean_dec(v_fst_4411_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_k_4385_);
lean_dec_ref(v_values_4383_);
lean_dec_ref(v_xs_4382_);
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4555_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
}
v___jp_4424_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = lean_box(0);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 1, v_report_4426_);
lean_ctor_set(v___x_4417_, 0, v___x_4432_);
v___x_4434_ = v___x_4417_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_report_4426_);
v___x_4434_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
size_t v_sz_4435_; lean_object* v___x_4436_; 
v_sz_4435_ = lean_array_size(v___y_4425_);
lean_inc(v___y_4431_);
lean_inc_ref(v___y_4430_);
lean_inc(v___y_4429_);
lean_inc_ref(v___y_4428_);
v___x_4436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg(v_fnNames_4380_, v_xs_4382_, v_values_4383_, v_k_4385_, v___x_4423_, v___y_4425_, v_sz_4435_, v___x_4407_, v___x_4434_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec_ref(v___y_4425_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4474_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4474_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4474_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v_fst_4441_; 
v_fst_4441_ = lean_ctor_get(v_a_4437_, 0);
if (lean_obj_tag(v_fst_4441_) == 0)
{
lean_object* v_snd_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4439_);
v_snd_4442_ = lean_ctor_get(v_a_4437_, 1);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_a_4437_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v_a_4437_, 0);
lean_dec(v_unused_4469_);
v___x_4444_ = v_a_4437_;
v_isShared_4445_ = v_isSharedCheck_4468_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_snd_4442_);
lean_dec(v_a_4437_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4468_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v_a_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
v___x_4446_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v___x_4419_, v___y_4430_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref(v___x_4446_);
v___x_4448_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__1);
if (v_isShared_4445_ == 0)
{
lean_ctor_set_tag(v___x_4444_, 7);
lean_ctor_set(v___x_4444_, 0, v___x_4448_);
v___x_4450_ = v___x_4444_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_snd_4442_);
v___x_4450_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
uint8_t v___x_4451_; 
v___x_4451_ = lean_unbox(v_a_4447_);
lean_dec(v_a_4447_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; 
lean_del_object(v___x_4413_);
v___x_4452_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(v___x_4450_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v___x_4452_;
}
else
{
lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4453_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__3);
lean_inc_ref(v___x_4450_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 7);
lean_ctor_set(v___x_4413_, 1, v___x_4450_);
lean_ctor_set(v___x_4413_, 0, v___x_4453_);
v___x_4455_ = v___x_4413_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___x_4450_);
v___x_4455_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v___x_4419_, v___x_4455_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4457_; 
lean_dec_ref(v___x_4456_);
v___x_4457_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(v___x_4450_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v___x_4457_;
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref(v___x_4450_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
v_a_4458_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4456_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4456_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
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
lean_object* v_val_4470_; lean_object* v___x_4472_; 
lean_inc_ref(v_fst_4441_);
lean_dec(v_a_4437_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_del_object(v___x_4413_);
v_val_4470_ = lean_ctor_get(v_fst_4441_, 0);
lean_inc(v_val_4470_);
lean_dec_ref(v_fst_4441_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v_val_4470_);
v___x_4472_ = v___x_4439_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_val_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_del_object(v___x_4413_);
v_a_4475_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4436_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4436_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
v___jp_4484_:
{
lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4491_ = lean_array_get_size(v___y_4485_);
v___x_4492_ = lean_nat_dec_eq(v___x_4491_, v___x_4392_);
if (v___x_4492_ == 0)
{
v___y_4425_ = v___y_4485_;
v_report_4426_ = v_fst_4411_;
v___y_4427_ = v___y_4486_;
v___y_4428_ = v___y_4487_;
v___y_4429_ = v___y_4488_;
v___y_4430_ = v___y_4489_;
v___y_4431_ = v___y_4490_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__6);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v_fst_4411_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___y_4425_ = v___y_4485_;
v_report_4426_ = v___x_4494_;
v___y_4427_ = v___y_4486_;
v___y_4428_ = v___y_4487_;
v___y_4429_ = v___y_4488_;
v___y_4430_ = v___y_4489_;
v___y_4431_ = v___y_4490_;
goto v___jp_4424_;
}
}
v___jp_4495_:
{
lean_object* v___x_4502_; 
lean_inc(v___y_4497_);
lean_inc_ref(v___y_4500_);
lean_inc(v___y_4498_);
lean_inc_ref(v___y_4496_);
v___x_4502_ = l_Lean_Elab_Structural_inductiveGroups(v___y_4501_, v___y_4496_, v___y_4498_, v___y_4500_, v___y_4497_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___x_4504_; lean_object* v_a_4505_; uint8_t v___x_4506_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref(v___x_4502_);
v___x_4504_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Structural_tryAllArgs_spec__1___redArg(v___x_4419_, v___y_4500_);
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
v___x_4506_ = lean_unbox(v_a_4505_);
lean_dec(v_a_4505_);
if (v___x_4506_ == 0)
{
v___y_4485_ = v_a_4503_;
v___y_4486_ = v___y_4499_;
v___y_4487_ = v___y_4496_;
v___y_4488_ = v___y_4498_;
v___y_4489_ = v___y_4500_;
v___y_4490_ = v___y_4497_;
goto v___jp_4484_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4507_ = lean_obj_once(&l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8, &l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8_once, _init_l_Lean_Elab_Structural_tryAllArgs___redArg___closed__8);
lean_inc(v_a_4503_);
v___x_4508_ = lean_array_to_list(v_a_4503_);
v___x_4509_ = lean_box(0);
v___x_4510_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__9(v___x_4508_, v___x_4509_);
v___x_4511_ = l_Lean_MessageData_ofList(v___x_4510_);
v___x_4512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4507_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
v___x_4513_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v___x_4419_, v___x_4512_, v___y_4496_, v___y_4498_, v___y_4500_, v___y_4497_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_dec_ref(v___x_4513_);
v___y_4485_ = v_a_4503_;
v___y_4486_ = v___y_4499_;
v___y_4487_ = v___y_4496_;
v___y_4488_ = v___y_4498_;
v___y_4489_ = v___y_4500_;
v___y_4490_ = v___y_4497_;
goto v___jp_4484_;
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v_a_4503_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec_ref(v___x_4423_);
lean_del_object(v___x_4417_);
lean_del_object(v___x_4413_);
lean_dec(v_fst_4411_);
lean_dec_ref(v_k_4385_);
lean_dec_ref(v_values_4383_);
lean_dec_ref(v_xs_4382_);
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4513_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4513_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
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
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec_ref(v___x_4423_);
lean_del_object(v___x_4417_);
lean_del_object(v___x_4413_);
lean_dec(v_fst_4411_);
lean_dec_ref(v_k_4385_);
lean_dec_ref(v_values_4383_);
lean_dec_ref(v_xs_4382_);
v_a_4522_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4502_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4502_);
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
v___jp_4530_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4536_ = ((lean_object*)(l_Lean_Elab_Structural_tryAllArgs___redArg___closed__9));
v___x_4537_ = lean_array_get_size(v___x_4423_);
v___x_4538_ = lean_nat_dec_lt(v___x_4392_, v___x_4537_);
if (v___x_4538_ == 0)
{
v___y_4496_ = v___y_4532_;
v___y_4497_ = v___y_4535_;
v___y_4498_ = v___y_4533_;
v___y_4499_ = v___y_4531_;
v___y_4500_ = v___y_4534_;
v___y_4501_ = v___x_4536_;
goto v___jp_4495_;
}
else
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_nat_dec_le(v___x_4537_, v___x_4537_);
if (v___x_4539_ == 0)
{
if (v___x_4538_ == 0)
{
v___y_4496_ = v___y_4532_;
v___y_4497_ = v___y_4535_;
v___y_4498_ = v___y_4533_;
v___y_4499_ = v___y_4531_;
v___y_4500_ = v___y_4534_;
v___y_4501_ = v___x_4536_;
goto v___jp_4495_;
}
else
{
size_t v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = lean_usize_of_nat(v___x_4537_);
v___x_4541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(v___x_4423_, v___x_4407_, v___x_4540_, v___x_4536_);
v___y_4496_ = v___y_4532_;
v___y_4497_ = v___y_4535_;
v___y_4498_ = v___y_4533_;
v___y_4499_ = v___y_4531_;
v___y_4500_ = v___y_4534_;
v___y_4501_ = v___x_4541_;
goto v___jp_4495_;
}
}
else
{
size_t v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = lean_usize_of_nat(v___x_4537_);
v___x_4543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_tryAllArgs_spec__10(v___x_4423_, v___x_4407_, v___x_4542_, v___x_4536_);
v___y_4496_ = v___y_4532_;
v___y_4497_ = v___y_4535_;
v___y_4498_ = v___y_4533_;
v___y_4499_ = v___y_4531_;
v___y_4500_ = v___y_4534_;
v___y_4501_ = v___x_4543_;
goto v___jp_4495_;
}
}
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_k_4385_);
lean_dec_ref(v_values_4383_);
lean_dec_ref(v_xs_4382_);
v_a_4575_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4408_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4408_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___redArg___boxed(lean_object* v_fnNames_4583_, lean_object* v_fixedParamPerms_4584_, lean_object* v_xs_4585_, lean_object* v_values_4586_, lean_object* v_termMeasure_x3fs_4587_, lean_object* v_k_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_Elab_Structural_tryAllArgs___redArg(v_fnNames_4583_, v_fixedParamPerms_4584_, v_xs_4585_, v_values_4586_, v_termMeasure_x3fs_4587_, v_k_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec_ref(v_fnNames_4583_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs(lean_object* v_00_u03b1_4596_, lean_object* v_fnNames_4597_, lean_object* v_fixedParamPerms_4598_, lean_object* v_xs_4599_, lean_object* v_values_4600_, lean_object* v_termMeasure_x3fs_4601_, lean_object* v_k_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_Elab_Structural_tryAllArgs___redArg(v_fnNames_4597_, v_fixedParamPerms_4598_, v_xs_4599_, v_values_4600_, v_termMeasure_x3fs_4601_, v_k_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_tryAllArgs___boxed(lean_object* v_00_u03b1_4610_, lean_object* v_fnNames_4611_, lean_object* v_fixedParamPerms_4612_, lean_object* v_xs_4613_, lean_object* v_values_4614_, lean_object* v_termMeasure_x3fs_4615_, lean_object* v_k_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lean_Elab_Structural_tryAllArgs(v_00_u03b1_4610_, v_fnNames_4611_, v_fixedParamPerms_4612_, v_xs_4613_, v_values_4614_, v_termMeasure_x3fs_4615_, v_k_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec_ref(v_fnNames_4611_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0(lean_object* v_xs_4624_, lean_object* v_as_4625_, size_t v_sz_4626_, size_t v_i_4627_, lean_object* v_b_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___redArg(v_xs_4624_, v_as_4625_, v_sz_4626_, v_i_4627_, v_b_4628_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0___boxed(lean_object* v_xs_4636_, lean_object* v_as_4637_, lean_object* v_sz_4638_, lean_object* v_i_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
size_t v_sz_boxed_4647_; size_t v_i_boxed_4648_; lean_object* v_res_4649_; 
v_sz_boxed_4647_ = lean_unbox_usize(v_sz_4638_);
lean_dec(v_sz_4638_);
v_i_boxed_4648_ = lean_unbox_usize(v_i_4639_);
lean_dec(v_i_4639_);
v_res_4649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__0(v_xs_4636_, v_as_4637_, v_sz_boxed_4647_, v_i_boxed_4648_, v_b_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4641_);
lean_dec_ref(v_as_4637_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3(lean_object* v_cls_4650_, lean_object* v_msg_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___redArg(v_cls_4650_, v_msg_4651_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3___boxed(lean_object* v_cls_4659_, lean_object* v_msg_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_addTrace___at___00Lean_Elab_Structural_tryAllArgs_spec__3(v_cls_4659_, v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5(lean_object* v_00_u03b1_4668_, lean_object* v_msg_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___redArg(v_msg_4669_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5___boxed(lean_object* v_00_u03b1_4677_, lean_object* v_msg_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_throwError___at___00Lean_Elab_Structural_tryAllArgs_spec__5(v_00_u03b1_4677_, v_msg_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6(lean_object* v_a_4686_, lean_object* v_xs_4687_, lean_object* v_as_4688_, size_t v_sz_4689_, size_t v_i_4690_, lean_object* v_b_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___redArg(v_a_4686_, v_xs_4687_, v_as_4688_, v_sz_4689_, v_i_4690_, v_b_4691_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6___boxed(lean_object* v_a_4699_, lean_object* v_xs_4700_, lean_object* v_as_4701_, lean_object* v_sz_4702_, lean_object* v_i_4703_, lean_object* v_b_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
size_t v_sz_boxed_4711_; size_t v_i_boxed_4712_; lean_object* v_res_4713_; 
v_sz_boxed_4711_ = lean_unbox_usize(v_sz_4702_);
lean_dec(v_sz_4702_);
v_i_boxed_4712_ = lean_unbox_usize(v_i_4703_);
lean_dec(v_i_4703_);
v_res_4713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__6(v_a_4699_, v_xs_4700_, v_as_4701_, v_sz_boxed_4711_, v_i_boxed_4712_, v_b_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4705_);
lean_dec_ref(v_as_4701_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7(lean_object* v_00_u03b1_4714_, lean_object* v_fnNames_4715_, lean_object* v_xs_4716_, lean_object* v_values_4717_, lean_object* v_k_4718_, lean_object* v_a_4719_, lean_object* v_as_4720_, size_t v_sz_4721_, size_t v_i_4722_, lean_object* v_b_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___redArg(v_fnNames_4715_, v_xs_4716_, v_values_4717_, v_k_4718_, v_a_4719_, v_as_4720_, v_sz_4721_, v_i_4722_, v_b_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7___boxed(lean_object* v_00_u03b1_4731_, lean_object* v_fnNames_4732_, lean_object* v_xs_4733_, lean_object* v_values_4734_, lean_object* v_k_4735_, lean_object* v_a_4736_, lean_object* v_as_4737_, lean_object* v_sz_4738_, lean_object* v_i_4739_, lean_object* v_b_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
size_t v_sz_boxed_4747_; size_t v_i_boxed_4748_; lean_object* v_res_4749_; 
v_sz_boxed_4747_ = lean_unbox_usize(v_sz_4738_);
lean_dec(v_sz_4738_);
v_i_boxed_4748_ = lean_unbox_usize(v_i_4739_);
lean_dec(v_i_4739_);
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__7(v_00_u03b1_4731_, v_fnNames_4732_, v_xs_4733_, v_values_4734_, v_k_4735_, v_a_4736_, v_as_4737_, v_sz_boxed_4747_, v_i_boxed_4748_, v_b_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec_ref(v_as_4737_);
lean_dec_ref(v_fnNames_4732_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8(lean_object* v_00_u03b1_4750_, lean_object* v_fnNames_4751_, lean_object* v_xs_4752_, lean_object* v_values_4753_, lean_object* v_k_4754_, lean_object* v___x_4755_, lean_object* v_as_4756_, size_t v_sz_4757_, size_t v_i_4758_, lean_object* v_b_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___redArg(v_fnNames_4751_, v_xs_4752_, v_values_4753_, v_k_4754_, v___x_4755_, v_as_4756_, v_sz_4757_, v_i_4758_, v_b_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8___boxed(lean_object* v_00_u03b1_4767_, lean_object* v_fnNames_4768_, lean_object* v_xs_4769_, lean_object* v_values_4770_, lean_object* v_k_4771_, lean_object* v___x_4772_, lean_object* v_as_4773_, lean_object* v_sz_4774_, lean_object* v_i_4775_, lean_object* v_b_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
size_t v_sz_boxed_4783_; size_t v_i_boxed_4784_; lean_object* v_res_4785_; 
v_sz_boxed_4783_ = lean_unbox_usize(v_sz_4774_);
lean_dec(v_sz_4774_);
v_i_boxed_4784_ = lean_unbox_usize(v_i_4775_);
lean_dec(v_i_4775_);
v_res_4785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8(v_00_u03b1_4767_, v_fnNames_4768_, v_xs_4769_, v_values_4770_, v_k_4771_, v___x_4772_, v_as_4773_, v_sz_boxed_4783_, v_i_boxed_4784_, v_b_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec_ref(v_as_4773_);
lean_dec_ref(v_fnNames_4768_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8(lean_object* v_00_u03b1_4786_, lean_object* v___x_4787_, lean_object* v_values_4788_, lean_object* v_xs_4789_, lean_object* v_fnNames_4790_, lean_object* v_k_4791_, lean_object* v_as_4792_, size_t v_sz_4793_, size_t v_i_4794_, lean_object* v_b_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___redArg(v___x_4787_, v_values_4788_, v_xs_4789_, v_fnNames_4790_, v_k_4791_, v_as_4792_, v_sz_4793_, v_i_4794_, v_b_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8___boxed(lean_object* v_00_u03b1_4803_, lean_object* v___x_4804_, lean_object* v_values_4805_, lean_object* v_xs_4806_, lean_object* v_fnNames_4807_, lean_object* v_k_4808_, lean_object* v_as_4809_, lean_object* v_sz_4810_, lean_object* v_i_4811_, lean_object* v_b_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
size_t v_sz_boxed_4819_; size_t v_i_boxed_4820_; lean_object* v_res_4821_; 
v_sz_boxed_4819_ = lean_unbox_usize(v_sz_4810_);
lean_dec(v_sz_4810_);
v_i_boxed_4820_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_res_4821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryAllArgs_spec__8_spec__8(v_00_u03b1_4803_, v___x_4804_, v_values_4805_, v_xs_4806_, v_fnNames_4807_, v_k_4808_, v_as_4809_, v_sz_boxed_4819_, v_i_boxed_4820_, v_b_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
lean_dec_ref(v_as_4809_);
lean_dec_ref(v_fnNames_4807_);
return v_res_4821_;
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
