// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqnsUtils
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Split import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.SplitIf import Lean.Meta.Tactic.Contradiction
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_tryURefl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Eqns_tryURefl___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "not definitionally equal"};
static const lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__0;
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__1;
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deltaLHS"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 64, 102, 150, 180, 16, 252, 96)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to delta reduce lhs"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Eqns_tryContradiction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Eqns_tryContradiction___closed__0 = (const lean_object*)&l_Lean_Elab_Eqns_tryContradiction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
lean_inc(v_mvarId_1_);
v___x_7_ = l_Lean_Meta_Split_simpMatchTarget(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; 
v___x_12_ = l_Lean_instBEqMVarId_beq(v_mvarId_1_, v_a_8_);
lean_dec(v_mvarId_1_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v_a_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v___x_17_; lean_object* v___x_19_; 
lean_dec(v_a_8_);
v___x_17_ = lean_box(0);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_17_);
v___x_19_ = v___x_10_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_mvarId_1_);
v_a_22_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_7_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_7_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object* v_mvarId_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object* v_mvarId_37_, uint8_t v_useNewSemantics_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
uint8_t v___x_44_; lean_object* v___x_45_; 
v___x_44_ = 1;
lean_inc(v_mvarId_37_);
v___x_45_ = l_Lean_Meta_simpIfTarget(v_mvarId_37_, v___x_44_, v_useNewSemantics_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_59_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_59_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_59_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_59_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_instBEqMVarId_beq(v_mvarId_37_, v_a_46_);
lean_dec(v_mvarId_37_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_51_);
v___x_53_ = v___x_48_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_57_; 
lean_dec(v_a_46_);
v___x_55_ = lean_box(0);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_55_);
v___x_57_ = v___x_48_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec(v_mvarId_37_);
v_a_60_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_45_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_45_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object* v_mvarId_68_, lean_object* v_useNewSemantics_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_useNewSemantics_boxed_75_; lean_object* v_res_76_; 
v_useNewSemantics_boxed_75_ = lean_unbox(v_useNewSemantics_69_);
v_res_76_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_68_, v_useNewSemantics_boxed_75_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(lean_object* v_e_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Lean_Expr_hasMVar(v_e_77_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_e_77_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v_mctx_83_; lean_object* v___x_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v___x_87_; lean_object* v_cache_88_; lean_object* v_zetaDeltaFVarIds_89_; lean_object* v_postponed_90_; lean_object* v_diag_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v___x_82_ = lean_st_ref_get(v___y_78_);
v_mctx_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_mctx_83_);
lean_dec(v___x_82_);
v___x_84_ = l_Lean_instantiateMVarsCore(v_mctx_83_, v_e_77_);
v_fst_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_fst_85_);
v_snd_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_snd_86_);
lean_dec_ref(v___x_84_);
v___x_87_ = lean_st_ref_take(v___y_78_);
v_cache_88_ = lean_ctor_get(v___x_87_, 1);
v_zetaDeltaFVarIds_89_ = lean_ctor_get(v___x_87_, 2);
v_postponed_90_ = lean_ctor_get(v___x_87_, 3);
v_diag_91_ = lean_ctor_get(v___x_87_, 4);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_87_, 0);
lean_dec(v_unused_101_);
v___x_93_ = v___x_87_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_diag_91_);
lean_inc(v_postponed_90_);
lean_inc(v_zetaDeltaFVarIds_89_);
lean_inc(v_cache_88_);
lean_dec(v___x_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v_snd_86_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_snd_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_cache_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_zetaDeltaFVarIds_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_postponed_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_diag_91_);
v___x_96_ = v_reuseFailAlloc_99_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_st_ref_put(v___y_78_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_fst_85_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg___boxed(lean_object* v_e_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_e_102_, v___y_103_);
lean_dec(v___y_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object* v_e_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_e_106_, v___y_108_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object* v_e_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_e_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4(lean_object* v_opts_120_, lean_object* v_opt_121_){
_start:
{
lean_object* v_name_122_; lean_object* v_defValue_123_; lean_object* v_map_124_; lean_object* v___x_125_; 
v_name_122_ = lean_ctor_get(v_opt_121_, 0);
v_defValue_123_ = lean_ctor_get(v_opt_121_, 1);
v_map_124_ = lean_ctor_get(v_opts_120_, 0);
v___x_125_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_124_, v_name_122_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_inc(v_defValue_123_);
return v_defValue_123_;
}
else
{
lean_object* v_val_126_; 
v_val_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v___x_125_, 1);
if (lean_obj_tag(v_val_126_) == 3)
{
lean_object* v_v_127_; 
v_v_127_ = lean_ctor_get(v_val_126_, 0);
lean_inc(v_v_127_);
lean_dec_ref_known(v_val_126_, 1);
return v_v_127_;
}
else
{
lean_dec(v_val_126_);
lean_inc(v_defValue_123_);
return v_defValue_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(lean_object* v_mvarId_131_, lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_131_, v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg___boxed(lean_object* v_mvarId_155_, lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_155_, v_x_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5(lean_object* v_00_u03b1_163_, lean_object* v_mvarId_164_, lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_164_, v_x_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___boxed(lean_object* v_00_u03b1_172_, lean_object* v_mvarId_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5(v_00_u03b1_172_, v_mvarId_173_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_tryURefl___lam__0(lean_object* v_declName_181_, lean_object* v_x_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_name_eq(v_x_182_, v_declName_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__0___boxed(lean_object* v_declName_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_Elab_Eqns_tryURefl___lam__0(v_declName_184_, v_x_185_);
lean_dec(v_x_185_);
lean_dec(v_declName_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(lean_object* v_a_188_, lean_object* v_as_189_, size_t v_i_190_, size_t v_stop_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_usize_dec_eq(v_i_190_, v_stop_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_array_uget_borrowed(v_as_189_, v_i_190_);
v___x_194_ = lean_name_eq(v_a_188_, v___x_193_);
if (v___x_194_ == 0)
{
size_t v___x_195_; size_t v___x_196_; 
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_add(v_i_190_, v___x_195_);
v_i_190_ = v___x_196_;
goto _start;
}
else
{
return v___x_194_;
}
}
else
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___boxed(lean_object* v_a_199_, lean_object* v_as_200_, lean_object* v_i_201_, lean_object* v_stop_202_){
_start:
{
size_t v_i_boxed_203_; size_t v_stop_boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_i_boxed_203_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_stop_boxed_204_ = lean_unbox_usize(v_stop_202_);
lean_dec(v_stop_202_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_a_199_, v_as_200_, v_i_boxed_203_, v_stop_boxed_204_);
lean_dec_ref(v_as_200_);
lean_dec(v_a_199_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object* v_as_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_array_get_size(v_as_207_);
v___x_211_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
return v___x_211_;
}
else
{
size_t v___x_212_; size_t v___x_213_; uint8_t v___x_214_; 
v___x_212_ = ((size_t)0ULL);
v___x_213_ = lean_usize_of_nat(v___x_210_);
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_a_208_, v_as_207_, v___x_212_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object* v_as_215_, lean_object* v_a_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_as_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_as_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12___redArg(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_ks_223_; lean_object* v_vs_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_248_; 
v_ks_223_ = lean_ctor_get(v_x_219_, 0);
v_vs_224_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_248_ == 0)
{
v___x_226_ = v_x_219_;
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_vs_224_);
lean_inc(v_ks_223_);
lean_dec(v_x_219_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_ks_223_);
v___x_229_ = lean_nat_dec_lt(v_x_220_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_x_220_);
v___x_230_ = lean_array_push(v_ks_223_, v_x_221_);
v___x_231_ = lean_array_push(v_vs_224_, v_x_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_231_);
lean_ctor_set(v___x_226_, 0, v___x_230_);
v___x_233_ = v___x_226_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v_k_x27_235_; uint8_t v___x_236_; 
v_k_x27_235_ = lean_array_fget_borrowed(v_ks_223_, v_x_220_);
v___x_236_ = l_Lean_instBEqMVarId_beq(v_x_221_, v_k_x27_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_227_ == 0)
{
v___x_238_ = v___x_226_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_ks_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_vs_224_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_x_220_, v___x_239_);
lean_dec(v_x_220_);
v_x_219_ = v___x_238_;
v_x_220_ = v___x_240_;
goto _start;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_array_fset(v_ks_223_, v_x_220_, v_x_221_);
v___x_244_ = lean_array_fset(v_vs_224_, v_x_220_, v_x_222_);
lean_dec(v_x_220_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_244_);
lean_ctor_set(v___x_226_, 0, v___x_243_);
v___x_246_ = v___x_226_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11___redArg(lean_object* v_n_249_, lean_object* v_k_250_, lean_object* v_v_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12___redArg(v_n_249_, v___x_252_, v_k_250_, v_v_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(lean_object* v_x_255_, size_t v_x_256_, size_t v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v_es_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v_j_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_es_260_ = lean_ctor_get(v_x_255_, 0);
v___x_261_ = ((size_t)31ULL);
v___x_262_ = lean_usize_land(v_x_256_, v___x_261_);
v_j_263_ = lean_usize_to_nat(v___x_262_);
v___x_264_ = lean_array_get_size(v_es_260_);
v___x_265_ = lean_nat_dec_lt(v_j_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_j_263_);
lean_dec(v_x_259_);
lean_dec(v_x_258_);
return v_x_255_;
}
else
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_304_; 
lean_inc_ref(v_es_260_);
v_isSharedCheck_304_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_x_255_, 0);
lean_dec(v_unused_305_);
v___x_267_ = v_x_255_;
v_isShared_268_ = v_isSharedCheck_304_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_x_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_304_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_xs_x27_271_; lean_object* v___y_273_; 
v_v_269_ = lean_array_fget(v_es_260_, v_j_263_);
v___x_270_ = lean_box(0);
v_xs_x27_271_ = lean_array_fset(v_es_260_, v_j_263_, v___x_270_);
switch(lean_obj_tag(v_v_269_))
{
case 0:
{
lean_object* v_key_278_; lean_object* v_val_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_key_278_ = lean_ctor_get(v_v_269_, 0);
v_val_279_ = lean_ctor_get(v_v_269_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_v_269_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v_v_269_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_val_279_);
lean_inc(v_key_278_);
lean_dec(v_v_269_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_instBEqMVarId_beq(v_x_258_, v_key_278_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_281_);
v___x_284_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_278_, v_val_279_, v_x_258_, v_x_259_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___y_273_ = v___x_285_;
goto v___jp_272_;
}
else
{
lean_object* v___x_287_; 
lean_dec(v_val_279_);
lean_dec(v_key_278_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_x_259_);
lean_ctor_set(v___x_281_, 0, v_x_258_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_x_258_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_x_259_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v___y_273_ = v___x_287_;
goto v___jp_272_;
}
}
}
}
case 1:
{
lean_object* v_node_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_302_; 
v_node_290_ = lean_ctor_get(v_v_269_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_v_269_);
if (v_isSharedCheck_302_ == 0)
{
v___x_292_ = v_v_269_;
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_node_290_);
lean_dec(v_v_269_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_294_ = ((size_t)5ULL);
v___x_295_ = lean_usize_shift_right(v_x_256_, v___x_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_x_257_, v___x_296_);
v___x_298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_node_290_, v___x_295_, v___x_297_, v_x_258_, v_x_259_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_298_);
v___x_300_ = v___x_292_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
v___y_273_ = v___x_300_;
goto v___jp_272_;
}
}
}
default: 
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_x_258_);
lean_ctor_set(v___x_303_, 1, v_x_259_);
v___y_273_ = v___x_303_;
goto v___jp_272_;
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_array_fset(v_xs_x27_271_, v_j_263_, v___y_273_);
lean_dec(v_j_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_274_);
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_ks_306_; lean_object* v_vs_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_325_; 
v_ks_306_ = lean_ctor_get(v_x_255_, 0);
v_vs_307_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_325_ == 0)
{
v___x_309_ = v_x_255_;
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_vs_307_);
lean_inc(v_ks_306_);
lean_dec(v_x_255_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_ks_306_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_vs_307_);
v___x_312_ = v_reuseFailAlloc_324_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v_newNode_313_; size_t v___x_314_; uint8_t v___x_315_; 
v_newNode_313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11___redArg(v___x_312_, v_x_258_, v_x_259_);
v___x_314_ = ((size_t)7ULL);
v___x_315_ = lean_usize_dec_le(v___x_314_, v_x_257_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_313_);
v___x_317_ = lean_unsigned_to_nat(4u);
v___x_318_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_ks_319_ = lean_ctor_get(v_newNode_313_, 0);
lean_inc_ref(v_ks_319_);
v_vs_320_ = lean_ctor_get(v_newNode_313_, 1);
lean_inc_ref(v_vs_320_);
lean_dec_ref(v_newNode_313_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(v_x_257_, v_ks_319_, v_vs_320_, v___x_321_, v___x_322_);
lean_dec_ref(v_vs_320_);
lean_dec_ref(v_ks_319_);
return v___x_323_;
}
else
{
return v_newNode_313_;
}
}
else
{
return v_newNode_313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(size_t v_depth_326_, lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_i_329_, lean_object* v_entries_330_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_array_get_size(v_keys_327_);
v___x_332_ = lean_nat_dec_lt(v_i_329_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec(v_i_329_);
return v_entries_330_;
}
else
{
lean_object* v_k_333_; lean_object* v_v_334_; uint64_t v___x_335_; size_t v_h_336_; size_t v___x_337_; lean_object* v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v_h_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_k_333_ = lean_array_fget_borrowed(v_keys_327_, v_i_329_);
v_v_334_ = lean_array_fget_borrowed(v_vals_328_, v_i_329_);
v___x_335_ = l_Lean_instHashableMVarId_hash(v_k_333_);
v_h_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = ((size_t)5ULL);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v_depth_326_, v___x_339_);
v___x_341_ = lean_usize_mul(v___x_337_, v___x_340_);
v_h_342_ = lean_usize_shift_right(v_h_336_, v___x_341_);
v___x_343_ = lean_nat_add(v_i_329_, v___x_338_);
lean_dec(v_i_329_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
v___x_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_entries_330_, v_h_342_, v_depth_326_, v_k_333_, v_v_334_);
v_i_329_ = v___x_343_;
v_entries_330_ = v___x_344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_i_349_, lean_object* v_entries_350_){
_start:
{
size_t v_depth_boxed_351_; lean_object* v_res_352_; 
v_depth_boxed_351_ = lean_unbox_usize(v_depth_346_);
lean_dec(v_depth_346_);
v_res_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(v_depth_boxed_351_, v_keys_347_, v_vals_348_, v_i_349_, v_entries_350_);
lean_dec_ref(v_vals_348_);
lean_dec_ref(v_keys_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
size_t v_x_6309__boxed_358_; size_t v_x_6310__boxed_359_; lean_object* v_res_360_; 
v_x_6309__boxed_358_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_x_6310__boxed_359_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_x_353_, v_x_6309__boxed_358_, v_x_6310__boxed_359_, v_x_356_, v_x_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint64_t v___x_364_; size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; 
v___x_364_ = l_Lean_instHashableMVarId_hash(v_x_362_);
v___x_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_x_361_, v___x_365_, v___x_366_, v_x_362_, v_x_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(lean_object* v_mvarId_368_, lean_object* v_val_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_mctx_373_; lean_object* v_cache_374_; lean_object* v_zetaDeltaFVarIds_375_; lean_object* v_postponed_376_; lean_object* v_diag_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_406_; 
v___x_372_ = lean_st_ref_take(v___y_370_);
v_mctx_373_ = lean_ctor_get(v___x_372_, 0);
v_cache_374_ = lean_ctor_get(v___x_372_, 1);
v_zetaDeltaFVarIds_375_ = lean_ctor_get(v___x_372_, 2);
v_postponed_376_ = lean_ctor_get(v___x_372_, 3);
v_diag_377_ = lean_ctor_get(v___x_372_, 4);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_406_ == 0)
{
v___x_379_ = v___x_372_;
v_isShared_380_ = v_isSharedCheck_406_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_diag_377_);
lean_inc(v_postponed_376_);
lean_inc(v_zetaDeltaFVarIds_375_);
lean_inc(v_cache_374_);
lean_inc(v_mctx_373_);
lean_dec(v___x_372_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_406_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_depth_381_; lean_object* v_levelAssignDepth_382_; lean_object* v_lmvarCounter_383_; lean_object* v_mvarCounter_384_; lean_object* v_lDecls_385_; lean_object* v_decls_386_; lean_object* v_userNames_387_; lean_object* v_lAssignment_388_; lean_object* v_eAssignment_389_; lean_object* v_dAssignment_390_; lean_object* v_instanceTypedMVars_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_405_; 
v_depth_381_ = lean_ctor_get(v_mctx_373_, 0);
v_levelAssignDepth_382_ = lean_ctor_get(v_mctx_373_, 1);
v_lmvarCounter_383_ = lean_ctor_get(v_mctx_373_, 2);
v_mvarCounter_384_ = lean_ctor_get(v_mctx_373_, 3);
v_lDecls_385_ = lean_ctor_get(v_mctx_373_, 4);
v_decls_386_ = lean_ctor_get(v_mctx_373_, 5);
v_userNames_387_ = lean_ctor_get(v_mctx_373_, 6);
v_lAssignment_388_ = lean_ctor_get(v_mctx_373_, 7);
v_eAssignment_389_ = lean_ctor_get(v_mctx_373_, 8);
v_dAssignment_390_ = lean_ctor_get(v_mctx_373_, 9);
v_instanceTypedMVars_391_ = lean_ctor_get(v_mctx_373_, 10);
v_isSharedCheck_405_ = !lean_is_exclusive(v_mctx_373_);
if (v_isSharedCheck_405_ == 0)
{
v___x_393_ = v_mctx_373_;
v_isShared_394_ = v_isSharedCheck_405_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_instanceTypedMVars_391_);
lean_inc(v_dAssignment_390_);
lean_inc(v_eAssignment_389_);
lean_inc(v_lAssignment_388_);
lean_inc(v_userNames_387_);
lean_inc(v_decls_386_);
lean_inc(v_lDecls_385_);
lean_inc(v_mvarCounter_384_);
lean_inc(v_lmvarCounter_383_);
lean_inc(v_levelAssignDepth_382_);
lean_inc(v_depth_381_);
lean_dec(v_mctx_373_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_405_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_box(0);
v___x_396_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(v_eAssignment_389_, v_mvarId_368_, v_val_369_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 8, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_depth_381_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_levelAssignDepth_382_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_lmvarCounter_383_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_mvarCounter_384_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_lDecls_385_);
lean_ctor_set(v_reuseFailAlloc_404_, 5, v_decls_386_);
lean_ctor_set(v_reuseFailAlloc_404_, 6, v_userNames_387_);
lean_ctor_set(v_reuseFailAlloc_404_, 7, v_lAssignment_388_);
lean_ctor_set(v_reuseFailAlloc_404_, 8, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 9, v_dAssignment_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 10, v_instanceTypedMVars_391_);
v___x_398_ = v_reuseFailAlloc_404_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_398_);
v___x_400_ = v___x_379_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_cache_374_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_zetaDeltaFVarIds_375_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_postponed_376_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_diag_377_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_st_ref_put(v___y_370_, v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_395_);
return v___x_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg___boxed(lean_object* v_mvarId_407_, lean_object* v_val_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_407_, v_val_408_, v___y_409_);
lean_dec(v___y_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(lean_object* v_msgData_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; lean_object* v_env_419_; uint8_t v___x_420_; lean_object* v_env_421_; lean_object* v___x_422_; lean_object* v_toCold_423_; lean_object* v_mctx_424_; lean_object* v_lctx_425_; lean_object* v_options_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_418_ = lean_st_ref_get(v___y_416_);
v_env_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_env_419_);
lean_dec(v___x_418_);
v___x_420_ = 0;
v_env_421_ = l_Lean_Environment_setRecordingDeps(v_env_419_, v___x_420_);
v___x_422_ = lean_st_ref_get(v___y_414_);
v_toCold_423_ = lean_ctor_get(v___y_415_, 0);
v_mctx_424_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_mctx_424_);
lean_dec(v___x_422_);
v_lctx_425_ = lean_ctor_get(v___y_413_, 2);
v_options_426_ = lean_ctor_get(v_toCold_423_, 2);
lean_inc_ref(v_options_426_);
lean_inc_ref(v_lctx_425_);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v_env_421_);
lean_ctor_set(v___x_427_, 1, v_mctx_424_);
lean_ctor_set(v___x_427_, 2, v_lctx_425_);
lean_ctor_set(v___x_427_, 3, v_options_426_);
v___x_428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_msgData_412_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5___boxed(lean_object* v_msgData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(v_msgData_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_ref_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_ref_443_ = lean_ctor_get(v___y_440_, 2);
v___x_444_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(v_msg_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_ref_443_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_ref_443_);
lean_ctor_set(v___x_449_, 1, v_a_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg___boxed(lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v_msg_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__4));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1(lean_object* v_mvarId_471_, lean_object* v_declNames_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_481_; 
lean_inc(v_mvarId_471_);
v___x_481_ = l_Lean_MVarId_getType_x27(v_mvarId_471_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = l_Lean_Expr_cleanupAnnotations(v_a_482_);
lean_dec(v_a_482_);
v___x_484_ = l_Lean_Expr_isApp(v___x_483_);
if (v___x_484_ == 0)
{
lean_dec_ref(v___x_483_);
goto v___jp_478_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = l_Lean_Expr_appFnCleanup___redArg(v___x_483_);
v___x_486_ = l_Lean_Expr_isApp(v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref(v___x_485_);
lean_dec_ref(v___x_483_);
goto v___jp_478_;
}
else
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = l_Lean_Expr_appFnCleanup___redArg(v___x_485_);
v___x_488_ = l_Lean_Expr_isApp(v___x_487_);
if (v___x_488_ == 0)
{
lean_dec_ref(v___x_487_);
lean_dec_ref(v___x_485_);
lean_dec_ref(v___x_483_);
goto v___jp_478_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_487_);
v___x_490_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_491_ = l_Lean_Expr_isConstOf(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec_ref(v___x_489_);
lean_dec_ref(v___x_487_);
lean_dec_ref(v___x_485_);
lean_dec_ref(v___x_483_);
goto v___jp_478_;
}
else
{
lean_object* v_arg_492_; lean_object* v_arg_493_; lean_object* v_arg_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v_a_498_; lean_object* v___x_510_; 
v_arg_492_ = lean_ctor_get(v___x_483_, 1);
lean_inc_ref(v_arg_492_);
lean_dec_ref(v___x_483_);
v_arg_493_ = lean_ctor_get(v___x_485_, 1);
lean_inc_ref(v_arg_493_);
lean_dec_ref(v___x_485_);
v_arg_494_ = lean_ctor_get(v___x_487_, 1);
lean_inc_ref(v_arg_494_);
lean_dec_ref(v___x_487_);
v___x_495_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_arg_493_, v___y_474_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_arg_492_, v___y_474_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
v___x_510_ = l_Lean_Expr_getAppFn(v_a_496_);
if (lean_obj_tag(v___x_510_) == 4)
{
lean_object* v_declName_511_; uint8_t v___x_512_; 
v_declName_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_declName_511_);
lean_dec_ref_known(v___x_510_, 2);
v___x_512_ = l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_declNames_472_, v_declName_511_);
if (v___x_512_ == 0)
{
lean_dec(v_declName_511_);
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
goto v___jp_499_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Expr_isAppOf(v_a_498_, v_declName_511_);
if (v___x_513_ == 0)
{
lean_dec(v_declName_511_);
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
goto v___jp_499_;
}
else
{
lean_object* v___f_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_tryURefl___lam__0___boxed), 2, 1);
lean_closure_set(v___f_514_, 0, v_declName_511_);
v___x_515_ = 0;
lean_inc(v_a_496_);
v___x_516_ = l_Lean_Meta_delta_x3f(v_a_496_, v___f_514_, v___x_515_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
if (lean_obj_tag(v_a_517_) == 1)
{
lean_object* v_val_518_; lean_object* v___y_520_; lean_object* v___x_526_; 
v_val_518_ = lean_ctor_get(v_a_517_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_a_517_, 1);
v___x_526_ = l_Lean_Meta_isExprDefEq(v_a_496_, v_a_498_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; uint8_t v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_unbox(v_a_527_);
lean_dec(v_a_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_val_518_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
lean_dec(v_mvarId_471_);
v___x_529_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5, &l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5_once, _init_l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5);
v___x_530_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v___x_529_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_530_;
}
else
{
v___y_520_ = v___y_474_;
goto v___jp_519_;
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_val_518_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
lean_dec(v_mvarId_471_);
v_a_531_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_526_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3));
v___x_522_ = l_Lean_Expr_constLevels_x21(v___x_489_);
lean_dec_ref(v___x_489_);
v___x_523_ = l_Lean_mkConst(v___x_521_, v___x_522_);
v___x_524_ = l_Lean_mkAppB(v___x_523_, v_arg_494_, v_val_518_);
v___x_525_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_471_, v___x_524_, v___y_520_);
return v___x_525_;
}
}
else
{
lean_object* v___x_539_; 
lean_dec(v_a_517_);
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
v___x_539_ = l_Lean_MVarId_refl(v_mvarId_471_, v___x_491_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_539_;
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
lean_dec(v_mvarId_471_);
v_a_540_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_516_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_516_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
else
{
lean_object* v___x_548_; 
lean_dec_ref(v___x_510_);
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref(v_arg_494_);
lean_dec_ref(v___x_489_);
v___x_548_ = l_Lean_MVarId_refl(v_mvarId_471_, v___x_491_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_548_;
}
v___jp_499_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_MVarId_refl(v_mvarId_471_, v___x_491_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_500_, 0);
lean_dec(v_unused_509_);
v___x_502_ = v___x_500_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_dec(v___x_500_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_box(0);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
return v___x_500_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_mvarId_471_);
v_a_549_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_481_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_481_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
v___jp_478_:
{
uint8_t v___x_479_; lean_object* v___x_480_; 
v___x_479_ = 1;
v___x_480_ = l_Lean_MVarId_refl(v_mvarId_471_, v___x_479_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___boxed(lean_object* v_mvarId_557_, lean_object* v_declNames_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Elab_Eqns_tryURefl___lam__1(v_mvarId_557_, v_declNames_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_declNames_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(lean_object* v_o_568_, lean_object* v_k_569_, uint8_t v_v_570_){
_start:
{
lean_object* v_map_571_; uint8_t v_hasTrace_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_586_; 
v_map_571_ = lean_ctor_get(v_o_568_, 0);
v_hasTrace_572_ = lean_ctor_get_uint8(v_o_568_, sizeof(void*)*1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_o_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_574_ = v_o_568_;
v_isShared_575_ = v_isSharedCheck_586_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_map_571_);
lean_dec(v_o_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_586_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_576_, 0, v_v_570_);
lean_inc(v_k_569_);
v___x_577_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_569_, v___x_576_, v_map_571_);
if (v_hasTrace_572_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_581_; 
v___x_578_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__1));
v___x_579_ = l_Lean_Name_isPrefixOf(v___x_578_, v_k_569_);
lean_dec(v_k_569_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_577_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*1, v___x_579_);
return v___x_581_;
}
}
else
{
lean_object* v___x_584_; 
lean_dec(v_k_569_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_584_ = v___x_574_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*1, v_hasTrace_572_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___boxed(lean_object* v_o_587_, lean_object* v_k_588_, lean_object* v_v_589_){
_start:
{
uint8_t v_v_boxed_590_; lean_object* v_res_591_; 
v_v_boxed_590_ = lean_unbox(v_v_589_);
v_res_591_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(v_o_587_, v_k_588_, v_v_boxed_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(lean_object* v_opts_592_, lean_object* v_opt_593_, uint8_t v_val_594_){
_start:
{
lean_object* v_name_595_; lean_object* v___x_596_; 
v_name_595_ = lean_ctor_get(v_opt_593_, 0);
lean_inc(v_name_595_);
lean_dec_ref(v_opt_593_);
v___x_596_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(v_opts_592_, v_name_595_, v_val_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6___boxed(lean_object* v_opts_597_, lean_object* v_opt_598_, lean_object* v_val_599_){
_start:
{
uint8_t v_val_boxed_600_; lean_object* v_res_601_; 
v_val_boxed_600_ = lean_unbox(v_val_599_);
v_res_601_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(v_opts_597_, v_opt_598_, v_val_boxed_600_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_607_, lean_object* v_declNames_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_toCold_614_; lean_object* v_currRecDepth_615_; lean_object* v_ref_616_; uint8_t v_suppressElabErrors_617_; uint8_t v_checkDeprecated_618_; uint8_t v_isRecordingDeps_619_; lean_object* v_fileName_620_; lean_object* v_fileMap_621_; lean_object* v_options_622_; lean_object* v_currNamespace_623_; lean_object* v_openDecls_624_; lean_object* v_initHeartbeats_625_; lean_object* v_maxHeartbeats_626_; lean_object* v_quotContext_627_; lean_object* v_currMacroScope_628_; lean_object* v_cancelTk_x3f_629_; lean_object* v_inheritedTraceOptions_630_; lean_object* v___f_631_; uint16_t v___y_633_; lean_object* v___y_634_; lean_object* v_fileName_635_; lean_object* v_fileMap_636_; lean_object* v_currNamespace_637_; lean_object* v_openDecls_638_; lean_object* v_initHeartbeats_639_; lean_object* v_maxHeartbeats_640_; lean_object* v_quotContext_641_; lean_object* v_currMacroScope_642_; lean_object* v_cancelTk_x3f_643_; lean_object* v_inheritedTraceOptions_644_; lean_object* v_currRecDepth_645_; lean_object* v_ref_646_; uint8_t v_suppressElabErrors_647_; uint8_t v_checkDeprecated_648_; uint8_t v_isRecordingDeps_649_; lean_object* v___y_650_; uint8_t v___y_684_; uint16_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_709_; 
v_toCold_614_ = lean_ctor_get(v_a_611_, 0);
v_currRecDepth_615_ = lean_ctor_get(v_a_611_, 1);
v_ref_616_ = lean_ctor_get(v_a_611_, 2);
v_suppressElabErrors_617_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*3 + 2);
v_checkDeprecated_618_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*3 + 3);
v_isRecordingDeps_619_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*3 + 4);
v_fileName_620_ = lean_ctor_get(v_toCold_614_, 0);
v_fileMap_621_ = lean_ctor_get(v_toCold_614_, 1);
v_options_622_ = lean_ctor_get(v_toCold_614_, 2);
v_currNamespace_623_ = lean_ctor_get(v_toCold_614_, 4);
v_openDecls_624_ = lean_ctor_get(v_toCold_614_, 5);
v_initHeartbeats_625_ = lean_ctor_get(v_toCold_614_, 6);
v_maxHeartbeats_626_ = lean_ctor_get(v_toCold_614_, 7);
v_quotContext_627_ = lean_ctor_get(v_toCold_614_, 8);
v_currMacroScope_628_ = lean_ctor_get(v_toCold_614_, 9);
v_cancelTk_x3f_629_ = lean_ctor_get(v_toCold_614_, 10);
v_inheritedTraceOptions_630_ = lean_ctor_get(v_toCold_614_, 11);
lean_inc(v_mvarId_607_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_tryURefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_631_, 0, v_mvarId_607_);
lean_closure_set(v___f_631_, 1, v_declNames_608_);
if (v_isRecordingDeps_619_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_622_);
v___x_721_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(v_options_622_, v___x_720_, v_isRecordingDeps_619_);
v___y_709_ = v___x_721_;
goto v___jp_708_;
}
else
{
lean_object* v___x_722_; 
lean_inc_ref(v_options_622_);
v___x_722_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_622_);
v___y_709_ = v___x_722_;
goto v___jp_708_;
}
v___jp_632_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = l_Lean_maxRecDepth;
v___x_652_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4(v___y_634_, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_653_, 0, v_fileName_635_);
lean_ctor_set(v___x_653_, 1, v_fileMap_636_);
lean_ctor_set(v___x_653_, 2, v___y_634_);
lean_ctor_set(v___x_653_, 3, v___x_652_);
lean_ctor_set(v___x_653_, 4, v_currNamespace_637_);
lean_ctor_set(v___x_653_, 5, v_openDecls_638_);
lean_ctor_set(v___x_653_, 6, v_initHeartbeats_639_);
lean_ctor_set(v___x_653_, 7, v_maxHeartbeats_640_);
lean_ctor_set(v___x_653_, 8, v_quotContext_641_);
lean_ctor_set(v___x_653_, 9, v_currMacroScope_642_);
lean_ctor_set(v___x_653_, 10, v_cancelTk_x3f_643_);
lean_ctor_set(v___x_653_, 11, v_inheritedTraceOptions_644_);
lean_inc(v_ref_646_);
lean_inc(v_currRecDepth_645_);
v___x_654_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_currRecDepth_645_);
lean_ctor_set(v___x_654_, 2, v_ref_646_);
lean_ctor_set_uint16(v___x_654_, sizeof(void*)*3, v___y_633_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3 + 2, v_suppressElabErrors_647_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3 + 3, v_checkDeprecated_648_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3 + 4, v_isRecordingDeps_649_);
v___x_655_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_607_, v___f_631_, v_a_609_, v_a_610_, v___x_654_, v___y_650_);
lean_dec_ref_known(v___x_654_, 3);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_665_);
v___x_657_ = v___x_655_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_659_ = 1;
v___x_660_ = lean_box(v___x_659_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_682_; 
v_a_666_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_682_ == 0)
{
v___x_668_ = v___x_655_;
v_isShared_669_ = v_isSharedCheck_682_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_655_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_682_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_Exception_isInterrupt(v_a_666_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
lean_inc(v_a_666_);
v___x_671_ = l_Lean_Exception_isRuntime(v_a_666_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_674_; 
lean_dec(v_a_666_);
v___x_672_ = lean_box(v___x_671_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
lean_ctor_set(v___x_668_, 0, v___x_672_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
lean_object* v___x_677_; 
if (v_isShared_669_ == 0)
{
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_666_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v___x_680_; 
if (v_isShared_669_ == 0)
{
v___x_680_ = v___x_668_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_666_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
v___jp_683_:
{
lean_object* v___x_687_; lean_object* v_env_688_; lean_object* v_nextMacroScope_689_; lean_object* v_ngen_690_; lean_object* v_auxDeclNGen_691_; lean_object* v_traceState_692_; lean_object* v_recordedDeps_693_; lean_object* v_messages_694_; lean_object* v_infoState_695_; lean_object* v_snapshotTasks_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v___x_687_ = lean_st_ref_take(v_a_612_);
v_env_688_ = lean_ctor_get(v___x_687_, 0);
v_nextMacroScope_689_ = lean_ctor_get(v___x_687_, 1);
v_ngen_690_ = lean_ctor_get(v___x_687_, 2);
v_auxDeclNGen_691_ = lean_ctor_get(v___x_687_, 3);
v_traceState_692_ = lean_ctor_get(v___x_687_, 4);
v_recordedDeps_693_ = lean_ctor_get(v___x_687_, 6);
v_messages_694_ = lean_ctor_get(v___x_687_, 7);
v_infoState_695_ = lean_ctor_get(v___x_687_, 8);
v_snapshotTasks_696_ = lean_ctor_get(v___x_687_, 9);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_687_, 5);
lean_dec(v_unused_707_);
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snapshotTasks_696_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_694_);
lean_inc(v_recordedDeps_693_);
lean_inc(v_traceState_692_);
lean_inc(v_auxDeclNGen_691_);
lean_inc(v_ngen_690_);
lean_inc(v_nextMacroScope_689_);
lean_inc(v_env_688_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = l_Lean_Kernel_enableDiag(v_env_688_, v___y_684_);
v___x_701_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 5, v___x_701_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_nextMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_ngen_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_auxDeclNGen_691_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_traceState_692_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_705_, 6, v_recordedDeps_693_);
lean_ctor_set(v_reuseFailAlloc_705_, 7, v_messages_694_);
lean_ctor_set(v_reuseFailAlloc_705_, 8, v_infoState_695_);
lean_ctor_set(v_reuseFailAlloc_705_, 9, v_snapshotTasks_696_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_st_ref_put(v_a_612_, v___x_703_);
lean_inc_ref(v_inheritedTraceOptions_630_);
lean_inc(v_cancelTk_x3f_629_);
lean_inc(v_currMacroScope_628_);
lean_inc(v_quotContext_627_);
lean_inc(v_maxHeartbeats_626_);
lean_inc(v_initHeartbeats_625_);
lean_inc(v_openDecls_624_);
lean_inc(v_currNamespace_623_);
lean_inc_ref(v_fileMap_621_);
lean_inc_ref(v_fileName_620_);
v___y_633_ = v___y_685_;
v___y_634_ = v___y_686_;
v_fileName_635_ = v_fileName_620_;
v_fileMap_636_ = v_fileMap_621_;
v_currNamespace_637_ = v_currNamespace_623_;
v_openDecls_638_ = v_openDecls_624_;
v_initHeartbeats_639_ = v_initHeartbeats_625_;
v_maxHeartbeats_640_ = v_maxHeartbeats_626_;
v_quotContext_641_ = v_quotContext_627_;
v_currMacroScope_642_ = v_currMacroScope_628_;
v_cancelTk_x3f_643_ = v_cancelTk_x3f_629_;
v_inheritedTraceOptions_644_ = v_inheritedTraceOptions_630_;
v_currRecDepth_645_ = v_currRecDepth_615_;
v_ref_646_ = v_ref_616_;
v_suppressElabErrors_647_ = v_suppressElabErrors_617_;
v_checkDeprecated_648_ = v_checkDeprecated_618_;
v_isRecordingDeps_649_ = v_isRecordingDeps_619_;
v___y_650_ = v_a_612_;
goto v___jp_632_;
}
}
}
v___jp_708_:
{
uint16_t v___x_710_; lean_object* v___x_711_; lean_object* v_env_712_; uint8_t v___x_713_; uint16_t v___x_714_; uint16_t v___x_715_; uint16_t v___x_716_; uint8_t v___x_717_; 
v___x_710_ = l_Lean_OptionFlags_ofOptions(v___y_709_);
v___x_711_ = lean_st_ref_get(v_a_612_);
v_env_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_711_);
v___x_713_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_712_);
lean_dec_ref(v_env_712_);
v___x_714_ = 512;
v___x_715_ = lean_uint16_land(v___x_710_, v___x_714_);
v___x_716_ = 0;
v___x_717_ = lean_uint16_dec_eq(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
if (v___x_713_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = 1;
v___y_684_ = v___x_718_;
v___y_685_ = v___x_710_;
v___y_686_ = v___y_709_;
goto v___jp_683_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_630_);
lean_inc(v_cancelTk_x3f_629_);
lean_inc(v_currMacroScope_628_);
lean_inc(v_quotContext_627_);
lean_inc(v_maxHeartbeats_626_);
lean_inc(v_initHeartbeats_625_);
lean_inc(v_openDecls_624_);
lean_inc(v_currNamespace_623_);
lean_inc_ref(v_fileMap_621_);
lean_inc_ref(v_fileName_620_);
v___y_633_ = v___x_710_;
v___y_634_ = v___y_709_;
v_fileName_635_ = v_fileName_620_;
v_fileMap_636_ = v_fileMap_621_;
v_currNamespace_637_ = v_currNamespace_623_;
v_openDecls_638_ = v_openDecls_624_;
v_initHeartbeats_639_ = v_initHeartbeats_625_;
v_maxHeartbeats_640_ = v_maxHeartbeats_626_;
v_quotContext_641_ = v_quotContext_627_;
v_currMacroScope_642_ = v_currMacroScope_628_;
v_cancelTk_x3f_643_ = v_cancelTk_x3f_629_;
v_inheritedTraceOptions_644_ = v_inheritedTraceOptions_630_;
v_currRecDepth_645_ = v_currRecDepth_615_;
v_ref_646_ = v_ref_616_;
v_suppressElabErrors_647_ = v_suppressElabErrors_617_;
v_checkDeprecated_648_ = v_checkDeprecated_618_;
v_isRecordingDeps_649_ = v_isRecordingDeps_619_;
v___y_650_ = v_a_612_;
goto v___jp_632_;
}
}
else
{
if (v___x_713_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_630_);
lean_inc(v_cancelTk_x3f_629_);
lean_inc(v_currMacroScope_628_);
lean_inc(v_quotContext_627_);
lean_inc(v_maxHeartbeats_626_);
lean_inc(v_initHeartbeats_625_);
lean_inc(v_openDecls_624_);
lean_inc(v_currNamespace_623_);
lean_inc_ref(v_fileMap_621_);
lean_inc_ref(v_fileName_620_);
v___y_633_ = v___x_710_;
v___y_634_ = v___y_709_;
v_fileName_635_ = v_fileName_620_;
v_fileMap_636_ = v_fileMap_621_;
v_currNamespace_637_ = v_currNamespace_623_;
v_openDecls_638_ = v_openDecls_624_;
v_initHeartbeats_639_ = v_initHeartbeats_625_;
v_maxHeartbeats_640_ = v_maxHeartbeats_626_;
v_quotContext_641_ = v_quotContext_627_;
v_currMacroScope_642_ = v_currMacroScope_628_;
v_cancelTk_x3f_643_ = v_cancelTk_x3f_629_;
v_inheritedTraceOptions_644_ = v_inheritedTraceOptions_630_;
v_currRecDepth_645_ = v_currRecDepth_615_;
v_ref_646_ = v_ref_616_;
v_suppressElabErrors_647_ = v_suppressElabErrors_617_;
v_checkDeprecated_648_ = v_checkDeprecated_618_;
v_isRecordingDeps_649_ = v_isRecordingDeps_619_;
v___y_650_ = v_a_612_;
goto v___jp_632_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = 0;
v___y_684_ = v___x_719_;
v___y_685_ = v___x_710_;
v___y_686_ = v___y_709_;
goto v___jp_683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_723_, lean_object* v_declNames_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_723_, v_declNames_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object* v_mvarId_731_, lean_object* v_val_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_731_, v_val_732_, v___y_734_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object* v_mvarId_739_, lean_object* v_val_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2(v_mvarId_739_, v_val_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3(lean_object* v_00_u03b1_747_, lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v_msg_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___boxed(lean_object* v_00_u03b1_755_, lean_object* v_msg_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3(v_00_u03b1_755_, v_msg_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3(lean_object* v_00_u03b2_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(v_x_764_, v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, size_t v_x_770_, size_t v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_x_769_, v_x_770_, v_x_771_, v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_7029__boxed_781_; size_t v_x_7030__boxed_782_; lean_object* v_res_783_; 
v_x_7029__boxed_781_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_x_7030__boxed_782_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_res_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6(v_00_u03b2_775_, v_x_776_, v_x_7029__boxed_781_, v_x_7030__boxed_782_, v_x_779_, v_x_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_784_, lean_object* v_n_785_, lean_object* v_k_786_, lean_object* v_v_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11___redArg(v_n_785_, v_k_786_, v_v_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_789_, size_t v_depth_790_, lean_object* v_keys_791_, lean_object* v_vals_792_, lean_object* v_heq_793_, lean_object* v_i_794_, lean_object* v_entries_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(v_depth_790_, v_keys_791_, v_vals_792_, v_i_794_, v_entries_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_797_, lean_object* v_depth_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_heq_801_, lean_object* v_i_802_, lean_object* v_entries_803_){
_start:
{
size_t v_depth_boxed_804_; lean_object* v_res_805_; 
v_depth_boxed_804_ = lean_unbox_usize(v_depth_798_);
lean_dec(v_depth_798_);
v_res_805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12(v_00_u03b2_797_, v_depth_boxed_804_, v_keys_799_, v_vals_800_, v_heq_801_, v_i_802_, v_entries_803_);
lean_dec_ref(v_vals_800_);
lean_dec_ref(v_keys_799_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12___redArg(v_x_807_, v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_812_, lean_object* v_x_813_){
_start:
{
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_814_, lean_object* v_x_815_){
_start:
{
uint8_t v___x_668__boxed_816_; uint8_t v_res_817_; lean_object* v_r_818_; 
v___x_668__boxed_816_ = lean_unbox(v___x_814_);
v_res_817_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_668__boxed_816_, v_x_815_);
lean_dec(v_x_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_826_ = l_Lean_MessageData_ofFormat(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7));
v___x_833_ = l_Lean_MessageData_ofFormat(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
lean_inc(v_mvarId_836_);
v___x_842_ = l_Lean_MVarId_getType_x27(v_mvarId_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_845_ = lean_unsigned_to_nat(3u);
v___x_846_ = l_Lean_Expr_isAppOfArity(v_a_843_, v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v_a_843_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_848_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5);
v___x_849_ = l_Lean_Meta_throwTacticEx___redArg(v___x_847_, v_mvarId_836_, v___x_848_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_850_ = lean_box(v___x_846_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_851_, 0, v___x_850_);
v___x_852_ = l_Lean_Expr_appFn_x21(v_a_843_);
v___x_853_ = l_Lean_Expr_appArg_x21(v___x_852_);
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_Expr_appArg_x21(v_a_843_);
lean_dec(v_a_843_);
v___x_855_ = 0;
v___x_856_ = l_Lean_Meta_delta_x3f(v___x_853_, v___f_851_, v___x_855_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
if (lean_obj_tag(v_a_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; 
v_val_858_ = lean_ctor_get(v_a_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_a_857_, 1);
v___x_859_ = l_Lean_Meta_mkEq(v_val_858_, v___x_854_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_836_, v_a_860_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_861_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_mvarId_836_);
v_a_862_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_859_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_a_857_);
lean_dec_ref(v___x_854_);
v___x_870_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_871_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9);
v___x_872_ = l_Lean_Meta_throwTacticEx___redArg(v___x_870_, v_mvarId_836_, v___x_871_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_872_;
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___x_854_);
lean_dec(v_mvarId_836_);
v_a_873_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_856_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_856_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_mvarId_836_);
v_a_881_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_842_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_842_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___f_902_; lean_object* v___x_903_; 
lean_inc(v_mvarId_896_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_902_, 0, v_mvarId_896_);
v___x_903_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_896_, v___f_902_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_921_ = l_Lean_MVarId_contradictionCore(v_mvarId_914_, v___x_920_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_928_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_929_; lean_object* v_dummy_930_; 
v___x_929_ = lean_box(0);
v_dummy_930_ = l_Lean_Expr_sort___override(v___x_929_);
return v_dummy_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_whnfR(v_e_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v___x_939_ = l_Lean_Expr_getAppFn(v_a_938_);
if (lean_obj_tag(v___x_939_) == 11)
{
lean_object* v_typeName_940_; lean_object* v_idx_941_; lean_object* v_struct_942_; lean_object* v___x_943_; 
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v_typeName_940_ = lean_ctor_get(v___x_939_, 0);
v_idx_941_ = lean_ctor_get(v___x_939_, 1);
v_struct_942_ = lean_ctor_get(v___x_939_, 2);
lean_inc_ref(v_struct_942_);
v___x_943_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_942_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_964_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_964_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___y_949_; size_t v___x_960_; size_t v___x_961_; uint8_t v___x_962_; 
v___x_960_ = lean_ptr_addr(v_struct_942_);
v___x_961_ = lean_ptr_addr(v_a_944_);
v___x_962_ = lean_usize_dec_eq(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_inc(v_idx_941_);
lean_inc(v_typeName_940_);
lean_dec_ref_known(v___x_939_, 3);
v___x_963_ = l_Lean_Expr_proj___override(v_typeName_940_, v_idx_941_, v_a_944_);
v___y_949_ = v___x_963_;
goto v___jp_948_;
}
else
{
lean_dec(v_a_944_);
v___y_949_ = v___x_939_;
goto v___jp_948_;
}
v___jp_948_:
{
lean_object* v_dummy_950_; lean_object* v_nargs_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v_dummy_950_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_951_ = l_Lean_Expr_getAppNumArgs(v_a_938_);
lean_inc(v_nargs_951_);
v___x_952_ = lean_mk_array(v_nargs_951_, v_dummy_950_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_sub(v_nargs_951_, v___x_953_);
lean_dec(v_nargs_951_);
v___x_955_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_938_, v___x_952_, v___x_954_);
v___x_956_ = l_Lean_mkAppN(v___y_949_, v___x_955_);
lean_dec_ref(v___x_955_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_956_);
v___x_958_ = v___x_946_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_939_, 3);
lean_dec(v_a_938_);
return v___x_943_;
}
}
else
{
lean_dec_ref(v___x_939_);
return v___x_937_;
}
}
else
{
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
lean_inc(v_mvarId_972_);
v___x_978_ = l_Lean_MVarId_getType_x27(v_mvarId_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1040_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_1040_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1040_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_984_ = lean_unsigned_to_nat(3u);
v___x_985_ = l_Lean_Expr_isAppOfArity(v_a_979_, v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
lean_dec(v_a_979_);
lean_dec(v_mvarId_972_);
v___x_986_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_986_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_981_);
v___x_990_ = l_Lean_Expr_appFn_x21(v_a_979_);
v___x_991_ = l_Lean_Expr_appArg_x21(v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = l_Lean_Expr_appArg_x21(v_a_979_);
lean_dec(v_a_979_);
lean_inc_ref(v___x_991_);
v___x_993_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_991_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1031_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1031_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1031_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_expr_eqv(v_a_994_, v___x_991_);
lean_dec_ref(v___x_991_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_del_object(v___x_996_);
v___x_999_ = l_Lean_Meta_mkEq(v_a_994_, v___x_992_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_972_, v_a_1000_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_a_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1001_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1001_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_mvarId_972_);
v_a_1019_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_999_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_999_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_dec(v_a_994_);
lean_dec_ref(v___x_992_);
lean_dec(v_mvarId_972_);
v___x_1027_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1027_);
v___x_1029_ = v___x_996_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_991_);
lean_dec(v_mvarId_972_);
v_a_1032_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_993_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_993_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_mvarId_972_);
v_a_1041_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_978_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_978_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
lean_inc(v_mvarId_1056_);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1062_, 0, v_mvarId_1056_);
v___x_1063_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_1056_, v___f_1062_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
return v_res_1070_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
}
#ifdef __cplusplus
}
#endif
