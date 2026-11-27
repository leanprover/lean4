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
size_t v_x_6302__boxed_358_; size_t v_x_6303__boxed_359_; lean_object* v_res_360_; 
v_x_6302__boxed_358_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_x_6303__boxed_359_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_x_353_, v_x_6302__boxed_358_, v_x_6303__boxed_359_, v_x_356_, v_x_357_);
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
lean_object* v___x_372_; lean_object* v_mctx_373_; lean_object* v_cache_374_; lean_object* v_zetaDeltaFVarIds_375_; lean_object* v_postponed_376_; lean_object* v_diag_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_405_; 
v___x_372_ = lean_st_ref_take(v___y_370_);
v_mctx_373_ = lean_ctor_get(v___x_372_, 0);
v_cache_374_ = lean_ctor_get(v___x_372_, 1);
v_zetaDeltaFVarIds_375_ = lean_ctor_get(v___x_372_, 2);
v_postponed_376_ = lean_ctor_get(v___x_372_, 3);
v_diag_377_ = lean_ctor_get(v___x_372_, 4);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_405_ == 0)
{
v___x_379_ = v___x_372_;
v_isShared_380_ = v_isSharedCheck_405_;
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
v_isShared_380_ = v_isSharedCheck_405_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_depth_381_; lean_object* v_levelAssignDepth_382_; lean_object* v_lmvarCounter_383_; lean_object* v_mvarCounter_384_; lean_object* v_lDecls_385_; lean_object* v_decls_386_; lean_object* v_userNames_387_; lean_object* v_lAssignment_388_; lean_object* v_eAssignment_389_; lean_object* v_dAssignment_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_404_; 
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
v_isSharedCheck_404_ = !lean_is_exclusive(v_mctx_373_);
if (v_isSharedCheck_404_ == 0)
{
v___x_392_ = v_mctx_373_;
v_isShared_393_ = v_isSharedCheck_404_;
goto v_resetjp_391_;
}
else
{
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
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_404_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_box(0);
v___x_395_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(v_eAssignment_389_, v_mvarId_368_, v_val_369_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 8, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_depth_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_levelAssignDepth_382_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_lmvarCounter_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_mvarCounter_384_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_lDecls_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_decls_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_userNames_387_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_lAssignment_388_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_403_, 9, v_dAssignment_390_);
v___x_397_ = v_reuseFailAlloc_403_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_397_);
v___x_399_ = v___x_379_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_cache_374_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_zetaDeltaFVarIds_375_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_postponed_376_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_diag_377_);
v___x_399_ = v_reuseFailAlloc_402_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_st_ref_put(v___y_370_, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_394_);
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg___boxed(lean_object* v_mvarId_406_, lean_object* v_val_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_406_, v_val_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(lean_object* v_msgData_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_env_418_; uint8_t v___x_419_; lean_object* v_env_420_; lean_object* v___x_421_; lean_object* v_toCold_422_; lean_object* v_mctx_423_; lean_object* v_lctx_424_; lean_object* v_options_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_env_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_env_418_);
lean_dec(v___x_417_);
v___x_419_ = 0;
v_env_420_ = l_Lean_Environment_setRecordingDeps(v_env_418_, v___x_419_);
v___x_421_ = lean_st_ref_get(v___y_413_);
v_toCold_422_ = lean_ctor_get(v___y_414_, 0);
v_mctx_423_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_mctx_423_);
lean_dec(v___x_421_);
v_lctx_424_ = lean_ctor_get(v___y_412_, 2);
v_options_425_ = lean_ctor_get(v_toCold_422_, 2);
lean_inc_ref(v_options_425_);
lean_inc_ref(v_lctx_424_);
v___x_426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_426_, 0, v_env_420_);
lean_ctor_set(v___x_426_, 1, v_mctx_423_);
lean_ctor_set(v___x_426_, 2, v_lctx_424_);
lean_ctor_set(v___x_426_, 3, v_options_425_);
v___x_427_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_msgData_411_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5___boxed(lean_object* v_msgData_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(v_msgData_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_ref_442_; lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_ref_442_ = lean_ctor_get(v___y_439_, 2);
v___x_443_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3_spec__5(v_msg_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
lean_inc(v_ref_442_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_ref_442_);
lean_ctor_set(v___x_448_, 1, v_a_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg___boxed(lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__4));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1(lean_object* v_mvarId_470_, lean_object* v_declNames_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_480_; 
lean_inc(v_mvarId_470_);
v___x_480_ = l_Lean_MVarId_getType_x27(v_mvarId_470_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = l_Lean_Expr_cleanupAnnotations(v_a_481_);
lean_dec(v_a_481_);
v___x_483_ = l_Lean_Expr_isApp(v___x_482_);
if (v___x_483_ == 0)
{
lean_dec_ref(v___x_482_);
goto v___jp_477_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_482_);
v___x_485_ = l_Lean_Expr_isApp(v___x_484_);
if (v___x_485_ == 0)
{
lean_dec_ref(v___x_484_);
lean_dec_ref(v___x_482_);
goto v___jp_477_;
}
else
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_484_);
v___x_487_ = l_Lean_Expr_isApp(v___x_486_);
if (v___x_487_ == 0)
{
lean_dec_ref(v___x_486_);
lean_dec_ref(v___x_484_);
lean_dec_ref(v___x_482_);
goto v___jp_477_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_486_);
v___x_489_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_490_ = l_Lean_Expr_isConstOf(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec_ref(v___x_488_);
lean_dec_ref(v___x_486_);
lean_dec_ref(v___x_484_);
lean_dec_ref(v___x_482_);
goto v___jp_477_;
}
else
{
lean_object* v_arg_491_; lean_object* v_arg_492_; lean_object* v_arg_493_; lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_509_; 
v_arg_491_ = lean_ctor_get(v___x_482_, 1);
lean_inc_ref(v_arg_491_);
lean_dec_ref(v___x_482_);
v_arg_492_ = lean_ctor_get(v___x_484_, 1);
lean_inc_ref(v_arg_492_);
lean_dec_ref(v___x_484_);
v_arg_493_ = lean_ctor_get(v___x_486_, 1);
lean_inc_ref(v_arg_493_);
lean_dec_ref(v___x_486_);
v___x_494_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_arg_492_, v___y_473_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_instantiateMVars___at___00Lean_Elab_Eqns_tryURefl_spec__0___redArg(v_arg_491_, v___y_473_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v___x_509_ = l_Lean_Expr_getAppFn(v_a_495_);
if (lean_obj_tag(v___x_509_) == 4)
{
lean_object* v_declName_510_; uint8_t v___x_511_; 
v_declName_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_declName_510_);
lean_dec_ref_known(v___x_509_, 2);
v___x_511_ = l_Array_contains___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_declNames_471_, v_declName_510_);
if (v___x_511_ == 0)
{
lean_dec(v_declName_510_);
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
goto v___jp_498_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_Expr_isAppOf(v_a_497_, v_declName_510_);
if (v___x_512_ == 0)
{
lean_dec(v_declName_510_);
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
goto v___jp_498_;
}
else
{
lean_object* v___f_513_; uint8_t v___x_514_; lean_object* v___x_515_; 
v___f_513_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_tryURefl___lam__0___boxed), 2, 1);
lean_closure_set(v___f_513_, 0, v_declName_510_);
v___x_514_ = 0;
lean_inc(v_a_495_);
v___x_515_ = l_Lean_Meta_delta_x3f(v_a_495_, v___f_513_, v___x_514_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
if (lean_obj_tag(v_a_516_) == 1)
{
lean_object* v_val_517_; lean_object* v___y_519_; lean_object* v___x_525_; 
v_val_517_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_a_516_, 1);
v___x_525_ = l_Lean_Meta_isExprDefEq(v_a_495_, v_a_497_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_unbox(v_a_526_);
lean_dec(v_a_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_val_517_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
lean_dec(v_mvarId_470_);
v___x_528_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5, &l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5_once, _init_l_Lean_Elab_Eqns_tryURefl___lam__1___closed__5);
v___x_529_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v___x_528_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_529_;
}
else
{
v___y_519_ = v___y_473_;
goto v___jp_518_;
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_val_517_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
lean_dec(v_mvarId_470_);
v_a_530_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_525_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__3));
v___x_521_ = l_Lean_Expr_constLevels_x21(v___x_488_);
lean_dec_ref(v___x_488_);
v___x_522_ = l_Lean_mkConst(v___x_520_, v___x_521_);
v___x_523_ = l_Lean_mkAppB(v___x_522_, v_arg_493_, v_val_517_);
v___x_524_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_470_, v___x_523_, v___y_519_);
return v___x_524_;
}
}
else
{
lean_object* v___x_538_; 
lean_dec(v_a_516_);
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
v___x_538_ = l_Lean_MVarId_refl(v_mvarId_470_, v___x_490_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_538_;
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
lean_dec(v_mvarId_470_);
v_a_539_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_515_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_515_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v___x_509_);
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec_ref(v_arg_493_);
lean_dec_ref(v___x_488_);
v___x_547_ = l_Lean_MVarId_refl(v_mvarId_470_, v___x_490_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_547_;
}
v___jp_498_:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_MVarId_refl(v_mvarId_470_, v___x_490_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_499_, 0);
lean_dec(v_unused_508_);
v___x_501_ = v___x_499_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_dec(v___x_499_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
return v___x_499_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_mvarId_470_);
v_a_548_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_480_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_480_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
v___jp_477_:
{
uint8_t v___x_478_; lean_object* v___x_479_; 
v___x_478_ = 1;
v___x_479_ = l_Lean_MVarId_refl(v_mvarId_470_, v___x_478_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___lam__1___boxed(lean_object* v_mvarId_556_, lean_object* v_declNames_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Elab_Eqns_tryURefl___lam__1(v_mvarId_556_, v_declNames_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec_ref(v_declNames_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(lean_object* v_o_567_, lean_object* v_k_568_, uint8_t v_v_569_){
_start:
{
lean_object* v_map_570_; uint8_t v_hasTrace_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_585_; 
v_map_570_ = lean_ctor_get(v_o_567_, 0);
v_hasTrace_571_ = lean_ctor_get_uint8(v_o_567_, sizeof(void*)*1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_o_567_);
if (v_isSharedCheck_585_ == 0)
{
v___x_573_ = v_o_567_;
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_map_570_);
lean_dec(v_o_567_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_575_, 0, v_v_569_);
lean_inc(v_k_568_);
v___x_576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_568_, v___x_575_, v_map_570_);
if (v_hasTrace_571_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_580_; 
v___x_577_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___closed__1));
v___x_578_ = l_Lean_Name_isPrefixOf(v___x_577_, v_k_568_);
lean_dec(v_k_568_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_576_);
v___x_580_ = v___x_573_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_576_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_578_);
return v___x_580_;
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v_k_568_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_576_);
v___x_583_ = v___x_573_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*1, v_hasTrace_571_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9___boxed(lean_object* v_o_586_, lean_object* v_k_587_, lean_object* v_v_588_){
_start:
{
uint8_t v_v_boxed_589_; lean_object* v_res_590_; 
v_v_boxed_589_ = lean_unbox(v_v_588_);
v_res_590_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(v_o_586_, v_k_587_, v_v_boxed_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(lean_object* v_opts_591_, lean_object* v_opt_592_, uint8_t v_val_593_){
_start:
{
lean_object* v_name_594_; lean_object* v___x_595_; 
v_name_594_ = lean_ctor_get(v_opt_592_, 0);
lean_inc(v_name_594_);
lean_dec_ref(v_opt_592_);
v___x_595_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6_spec__9(v_opts_591_, v_name_594_, v_val_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6___boxed(lean_object* v_opts_596_, lean_object* v_opt_597_, lean_object* v_val_598_){
_start:
{
uint8_t v_val_boxed_599_; lean_object* v_res_600_; 
v_val_boxed_599_ = lean_unbox(v_val_598_);
v_res_600_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(v_opts_596_, v_opt_597_, v_val_boxed_599_);
return v_res_600_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_606_, lean_object* v_declNames_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_toCold_613_; lean_object* v_currRecDepth_614_; lean_object* v_ref_615_; uint8_t v_suppressElabErrors_616_; uint8_t v_checkDeprecated_617_; uint8_t v_isRecordingDeps_618_; lean_object* v_fileName_619_; lean_object* v_fileMap_620_; lean_object* v_options_621_; lean_object* v_currNamespace_622_; lean_object* v_openDecls_623_; lean_object* v_initHeartbeats_624_; lean_object* v_maxHeartbeats_625_; lean_object* v_quotContext_626_; lean_object* v_currMacroScope_627_; lean_object* v_cancelTk_x3f_628_; lean_object* v_inheritedTraceOptions_629_; lean_object* v___f_630_; lean_object* v___y_632_; uint16_t v___y_633_; lean_object* v_fileName_634_; lean_object* v_fileMap_635_; lean_object* v_currNamespace_636_; lean_object* v_openDecls_637_; lean_object* v_initHeartbeats_638_; lean_object* v_maxHeartbeats_639_; lean_object* v_quotContext_640_; lean_object* v_currMacroScope_641_; lean_object* v_cancelTk_x3f_642_; lean_object* v_inheritedTraceOptions_643_; lean_object* v_currRecDepth_644_; lean_object* v_ref_645_; uint8_t v_suppressElabErrors_646_; uint8_t v_checkDeprecated_647_; uint8_t v_isRecordingDeps_648_; lean_object* v___y_649_; lean_object* v___y_683_; uint16_t v___y_684_; uint8_t v___y_685_; lean_object* v___y_708_; 
v_toCold_613_ = lean_ctor_get(v_a_610_, 0);
v_currRecDepth_614_ = lean_ctor_get(v_a_610_, 1);
v_ref_615_ = lean_ctor_get(v_a_610_, 2);
v_suppressElabErrors_616_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*3 + 2);
v_checkDeprecated_617_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*3 + 3);
v_isRecordingDeps_618_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*3 + 4);
v_fileName_619_ = lean_ctor_get(v_toCold_613_, 0);
v_fileMap_620_ = lean_ctor_get(v_toCold_613_, 1);
v_options_621_ = lean_ctor_get(v_toCold_613_, 2);
v_currNamespace_622_ = lean_ctor_get(v_toCold_613_, 4);
v_openDecls_623_ = lean_ctor_get(v_toCold_613_, 5);
v_initHeartbeats_624_ = lean_ctor_get(v_toCold_613_, 6);
v_maxHeartbeats_625_ = lean_ctor_get(v_toCold_613_, 7);
v_quotContext_626_ = lean_ctor_get(v_toCold_613_, 8);
v_currMacroScope_627_ = lean_ctor_get(v_toCold_613_, 9);
v_cancelTk_x3f_628_ = lean_ctor_get(v_toCold_613_, 10);
v_inheritedTraceOptions_629_ = lean_ctor_get(v_toCold_613_, 11);
lean_inc(v_mvarId_606_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_tryURefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_630_, 0, v_mvarId_606_);
lean_closure_set(v___f_630_, 1, v_declNames_607_);
if (v_isRecordingDeps_618_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_621_);
v___x_720_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__6(v_options_621_, v___x_719_, v_isRecordingDeps_618_);
v___y_708_ = v___x_720_;
goto v___jp_707_;
}
else
{
lean_object* v___x_721_; 
lean_inc_ref(v_options_621_);
v___x_721_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_621_);
v___y_708_ = v___x_721_;
goto v___jp_707_;
}
v___jp_631_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_650_ = l_Lean_maxRecDepth;
v___x_651_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__4(v___y_632_, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_652_, 0, v_fileName_634_);
lean_ctor_set(v___x_652_, 1, v_fileMap_635_);
lean_ctor_set(v___x_652_, 2, v___y_632_);
lean_ctor_set(v___x_652_, 3, v___x_651_);
lean_ctor_set(v___x_652_, 4, v_currNamespace_636_);
lean_ctor_set(v___x_652_, 5, v_openDecls_637_);
lean_ctor_set(v___x_652_, 6, v_initHeartbeats_638_);
lean_ctor_set(v___x_652_, 7, v_maxHeartbeats_639_);
lean_ctor_set(v___x_652_, 8, v_quotContext_640_);
lean_ctor_set(v___x_652_, 9, v_currMacroScope_641_);
lean_ctor_set(v___x_652_, 10, v_cancelTk_x3f_642_);
lean_ctor_set(v___x_652_, 11, v_inheritedTraceOptions_643_);
lean_inc(v_ref_645_);
lean_inc(v_currRecDepth_644_);
v___x_653_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_currRecDepth_644_);
lean_ctor_set(v___x_653_, 2, v_ref_645_);
lean_ctor_set_uint16(v___x_653_, sizeof(void*)*3, v___y_633_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 2, v_suppressElabErrors_646_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 3, v_checkDeprecated_647_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 4, v_isRecordingDeps_648_);
v___x_654_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_606_, v___f_630_, v_a_608_, v_a_609_, v___x_653_, v___y_649_);
lean_dec_ref_known(v___x_653_, 3);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_654_, 0);
lean_dec(v_unused_664_);
v___x_656_ = v___x_654_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_dec(v___x_654_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = 1;
v___x_659_ = lean_box(v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_681_; 
v_a_665_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_681_ == 0)
{
v___x_667_ = v___x_654_;
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_654_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; 
v___x_669_ = l_Lean_Exception_isInterrupt(v_a_665_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
lean_inc(v_a_665_);
v___x_670_ = l_Lean_Exception_isRuntime(v_a_665_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v_a_665_);
v___x_671_ = lean_box(v___x_670_);
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 0);
lean_ctor_set(v___x_667_, 0, v___x_671_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
lean_object* v___x_676_; 
if (v_isShared_668_ == 0)
{
v___x_676_ = v___x_667_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_665_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v___x_679_; 
if (v_isShared_668_ == 0)
{
v___x_679_ = v___x_667_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_665_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_recordedDeps_692_; lean_object* v_messages_693_; lean_object* v_infoState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v___x_686_ = lean_st_ref_take(v_a_611_);
v_env_687_ = lean_ctor_get(v___x_686_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_686_, 1);
v_ngen_689_ = lean_ctor_get(v___x_686_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_686_, 3);
v_traceState_691_ = lean_ctor_get(v___x_686_, 4);
v_recordedDeps_692_ = lean_ctor_get(v___x_686_, 6);
v_messages_693_ = lean_ctor_get(v___x_686_, 7);
v_infoState_694_ = lean_ctor_get(v___x_686_, 8);
v_snapshotTasks_695_ = lean_ctor_get(v___x_686_, 9);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_686_, 5);
lean_dec(v_unused_706_);
v___x_697_ = v___x_686_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snapshotTasks_695_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_693_);
lean_inc(v_recordedDeps_692_);
lean_inc(v_traceState_691_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_686_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = l_Lean_Kernel_enableDiag(v_env_687_, v___y_685_);
v___x_700_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 5, v___x_700_);
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_traceState_691_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_recordedDeps_692_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_messages_693_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_infoState_694_);
lean_ctor_set(v_reuseFailAlloc_704_, 9, v_snapshotTasks_695_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; 
v___x_703_ = lean_st_ref_put(v_a_611_, v___x_702_);
lean_inc_ref(v_inheritedTraceOptions_629_);
lean_inc(v_cancelTk_x3f_628_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc_ref(v_fileMap_620_);
lean_inc_ref(v_fileName_619_);
v___y_632_ = v___y_683_;
v___y_633_ = v___y_684_;
v_fileName_634_ = v_fileName_619_;
v_fileMap_635_ = v_fileMap_620_;
v_currNamespace_636_ = v_currNamespace_622_;
v_openDecls_637_ = v_openDecls_623_;
v_initHeartbeats_638_ = v_initHeartbeats_624_;
v_maxHeartbeats_639_ = v_maxHeartbeats_625_;
v_quotContext_640_ = v_quotContext_626_;
v_currMacroScope_641_ = v_currMacroScope_627_;
v_cancelTk_x3f_642_ = v_cancelTk_x3f_628_;
v_inheritedTraceOptions_643_ = v_inheritedTraceOptions_629_;
v_currRecDepth_644_ = v_currRecDepth_614_;
v_ref_645_ = v_ref_615_;
v_suppressElabErrors_646_ = v_suppressElabErrors_616_;
v_checkDeprecated_647_ = v_checkDeprecated_617_;
v_isRecordingDeps_648_ = v_isRecordingDeps_618_;
v___y_649_ = v_a_611_;
goto v___jp_631_;
}
}
}
v___jp_707_:
{
uint16_t v___x_709_; lean_object* v___x_710_; lean_object* v_env_711_; uint8_t v___x_712_; uint16_t v___x_713_; uint16_t v___x_714_; uint16_t v___x_715_; uint8_t v___x_716_; 
v___x_709_ = l_Lean_OptionFlags_ofOptions(v___y_708_);
v___x_710_ = lean_st_ref_get(v_a_611_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_710_);
v___x_712_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_711_);
lean_dec_ref(v_env_711_);
v___x_713_ = 512;
v___x_714_ = lean_uint16_land(v___x_709_, v___x_713_);
v___x_715_ = 0;
v___x_716_ = lean_uint16_dec_eq(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
if (v___x_712_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = 1;
v___y_683_ = v___y_708_;
v___y_684_ = v___x_709_;
v___y_685_ = v___x_717_;
goto v___jp_682_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_629_);
lean_inc(v_cancelTk_x3f_628_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc_ref(v_fileMap_620_);
lean_inc_ref(v_fileName_619_);
v___y_632_ = v___y_708_;
v___y_633_ = v___x_709_;
v_fileName_634_ = v_fileName_619_;
v_fileMap_635_ = v_fileMap_620_;
v_currNamespace_636_ = v_currNamespace_622_;
v_openDecls_637_ = v_openDecls_623_;
v_initHeartbeats_638_ = v_initHeartbeats_624_;
v_maxHeartbeats_639_ = v_maxHeartbeats_625_;
v_quotContext_640_ = v_quotContext_626_;
v_currMacroScope_641_ = v_currMacroScope_627_;
v_cancelTk_x3f_642_ = v_cancelTk_x3f_628_;
v_inheritedTraceOptions_643_ = v_inheritedTraceOptions_629_;
v_currRecDepth_644_ = v_currRecDepth_614_;
v_ref_645_ = v_ref_615_;
v_suppressElabErrors_646_ = v_suppressElabErrors_616_;
v_checkDeprecated_647_ = v_checkDeprecated_617_;
v_isRecordingDeps_648_ = v_isRecordingDeps_618_;
v___y_649_ = v_a_611_;
goto v___jp_631_;
}
}
else
{
if (v___x_712_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_629_);
lean_inc(v_cancelTk_x3f_628_);
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
lean_inc(v_maxHeartbeats_625_);
lean_inc(v_initHeartbeats_624_);
lean_inc(v_openDecls_623_);
lean_inc(v_currNamespace_622_);
lean_inc_ref(v_fileMap_620_);
lean_inc_ref(v_fileName_619_);
v___y_632_ = v___y_708_;
v___y_633_ = v___x_709_;
v_fileName_634_ = v_fileName_619_;
v_fileMap_635_ = v_fileMap_620_;
v_currNamespace_636_ = v_currNamespace_622_;
v_openDecls_637_ = v_openDecls_623_;
v_initHeartbeats_638_ = v_initHeartbeats_624_;
v_maxHeartbeats_639_ = v_maxHeartbeats_625_;
v_quotContext_640_ = v_quotContext_626_;
v_currMacroScope_641_ = v_currMacroScope_627_;
v_cancelTk_x3f_642_ = v_cancelTk_x3f_628_;
v_inheritedTraceOptions_643_ = v_inheritedTraceOptions_629_;
v_currRecDepth_644_ = v_currRecDepth_614_;
v_ref_645_ = v_ref_615_;
v_suppressElabErrors_646_ = v_suppressElabErrors_616_;
v_checkDeprecated_647_ = v_checkDeprecated_617_;
v_isRecordingDeps_648_ = v_isRecordingDeps_618_;
v___y_649_ = v_a_611_;
goto v___jp_631_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
v___y_683_ = v___y_708_;
v___y_684_ = v___x_709_;
v___y_685_ = v___x_718_;
goto v___jp_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_722_, lean_object* v_declNames_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_722_, v_declNames_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object* v_mvarId_730_, lean_object* v_val_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___redArg(v_mvarId_730_, v_val_731_, v___y_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object* v_mvarId_738_, lean_object* v_val_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2(v_mvarId_738_, v_val_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3(lean_object* v_00_u03b1_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___redArg(v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3___boxed(lean_object* v_00_u03b1_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_throwError___at___00Lean_Elab_Eqns_tryURefl_spec__3(v_00_u03b1_754_, v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3___redArg(v_x_763_, v_x_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, size_t v_x_769_, size_t v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___redArg(v_x_768_, v_x_769_, v_x_770_, v_x_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
size_t v_x_7022__boxed_780_; size_t v_x_7023__boxed_781_; lean_object* v_res_782_; 
v_x_7022__boxed_780_ = lean_unbox_usize(v_x_776_);
lean_dec(v_x_776_);
v_x_7023__boxed_781_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_res_782_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6(v_00_u03b2_774_, v_x_775_, v_x_7022__boxed_780_, v_x_7023__boxed_781_, v_x_778_, v_x_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_783_, lean_object* v_n_784_, lean_object* v_k_785_, lean_object* v_v_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11___redArg(v_n_784_, v_k_785_, v_v_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_788_, size_t v_depth_789_, lean_object* v_keys_790_, lean_object* v_vals_791_, lean_object* v_heq_792_, lean_object* v_i_793_, lean_object* v_entries_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___redArg(v_depth_789_, v_keys_790_, v_vals_791_, v_i_793_, v_entries_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_796_, lean_object* v_depth_797_, lean_object* v_keys_798_, lean_object* v_vals_799_, lean_object* v_heq_800_, lean_object* v_i_801_, lean_object* v_entries_802_){
_start:
{
size_t v_depth_boxed_803_; lean_object* v_res_804_; 
v_depth_boxed_803_ = lean_unbox_usize(v_depth_797_);
lean_dec(v_depth_797_);
v_res_804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__12(v_00_u03b2_796_, v_depth_boxed_803_, v_keys_798_, v_vals_799_, v_heq_800_, v_i_801_, v_entries_802_);
lean_dec_ref(v_vals_799_);
lean_dec_ref(v_keys_798_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Eqns_tryURefl_spec__2_spec__3_spec__6_spec__11_spec__12___redArg(v_x_806_, v_x_807_, v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_811_, lean_object* v_x_812_){
_start:
{
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_813_, lean_object* v_x_814_){
_start:
{
uint8_t v___x_668__boxed_815_; uint8_t v_res_816_; lean_object* v_r_817_; 
v___x_668__boxed_815_ = lean_unbox(v___x_813_);
v_res_816_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_668__boxed_815_, v_x_814_);
lean_dec(v_x_814_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_825_ = l_Lean_MessageData_ofFormat(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7));
v___x_832_ = l_Lean_MessageData_ofFormat(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
lean_inc(v_mvarId_835_);
v___x_841_ = l_Lean_MVarId_getType_x27(v_mvarId_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_844_ = lean_unsigned_to_nat(3u);
v___x_845_ = l_Lean_Expr_isAppOfArity(v_a_842_, v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v_a_842_);
v___x_846_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_847_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5);
v___x_848_ = l_Lean_Meta_throwTacticEx___redArg(v___x_846_, v_mvarId_835_, v___x_847_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; 
v___x_849_ = lean_box(v___x_845_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_850_, 0, v___x_849_);
v___x_851_ = l_Lean_Expr_appFn_x21(v_a_842_);
v___x_852_ = l_Lean_Expr_appArg_x21(v___x_851_);
lean_dec_ref(v___x_851_);
v___x_853_ = l_Lean_Expr_appArg_x21(v_a_842_);
lean_dec(v_a_842_);
v___x_854_ = 0;
v___x_855_ = l_Lean_Meta_delta_x3f(v___x_852_, v___f_850_, v___x_854_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
if (lean_obj_tag(v_a_856_) == 1)
{
lean_object* v_val_857_; lean_object* v___x_858_; 
v_val_857_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v_a_856_, 1);
v___x_858_ = l_Lean_Meta_mkEq(v_val_857_, v___x_853_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_835_, v_a_859_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_mvarId_835_);
v_a_861_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_858_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_a_856_);
lean_dec_ref(v___x_853_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_870_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9);
v___x_871_ = l_Lean_Meta_throwTacticEx___redArg(v___x_869_, v_mvarId_835_, v___x_870_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_871_;
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___x_853_);
lean_dec(v_mvarId_835_);
v_a_872_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_855_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_855_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
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
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_mvarId_835_);
v_a_880_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_841_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_841_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___f_901_; lean_object* v___x_902_; 
lean_inc(v_mvarId_895_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_901_, 0, v_mvarId_895_);
v___x_902_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_895_, v___f_901_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_920_ = l_Lean_MVarId_contradictionCore(v_mvarId_913_, v___x_919_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_927_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_928_; lean_object* v_dummy_929_; 
v___x_928_ = lean_box(0);
v_dummy_929_ = l_Lean_Expr_sort___override(v___x_928_);
return v_dummy_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_whnfR(v_e_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v___x_938_ = l_Lean_Expr_getAppFn(v_a_937_);
if (lean_obj_tag(v___x_938_) == 11)
{
lean_object* v_typeName_939_; lean_object* v_idx_940_; lean_object* v_struct_941_; lean_object* v___x_942_; 
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v_typeName_939_ = lean_ctor_get(v___x_938_, 0);
v_idx_940_ = lean_ctor_get(v___x_938_, 1);
v_struct_941_ = lean_ctor_get(v___x_938_, 2);
lean_inc_ref(v_struct_941_);
v___x_942_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_941_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_963_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_963_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_963_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_963_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___y_948_; size_t v___x_959_; size_t v___x_960_; uint8_t v___x_961_; 
v___x_959_ = lean_ptr_addr(v_struct_941_);
v___x_960_ = lean_ptr_addr(v_a_943_);
v___x_961_ = lean_usize_dec_eq(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_inc(v_idx_940_);
lean_inc(v_typeName_939_);
lean_dec_ref_known(v___x_938_, 3);
v___x_962_ = l_Lean_Expr_proj___override(v_typeName_939_, v_idx_940_, v_a_943_);
v___y_948_ = v___x_962_;
goto v___jp_947_;
}
else
{
lean_dec(v_a_943_);
v___y_948_ = v___x_938_;
goto v___jp_947_;
}
v___jp_947_:
{
lean_object* v_dummy_949_; lean_object* v_nargs_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v_dummy_949_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_950_ = l_Lean_Expr_getAppNumArgs(v_a_937_);
lean_inc(v_nargs_950_);
v___x_951_ = lean_mk_array(v_nargs_950_, v_dummy_949_);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_sub(v_nargs_950_, v___x_952_);
lean_dec(v_nargs_950_);
v___x_954_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_937_, v___x_951_, v___x_953_);
v___x_955_ = l_Lean_mkAppN(v___y_948_, v___x_954_);
lean_dec_ref(v___x_954_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_955_);
v___x_957_ = v___x_945_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_938_, 3);
lean_dec(v_a_937_);
return v___x_942_;
}
}
else
{
lean_dec_ref(v___x_938_);
return v___x_936_;
}
}
else
{
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
lean_inc(v_mvarId_971_);
v___x_977_ = l_Lean_MVarId_getType_x27(v_mvarId_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1039_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1039_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1039_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_Eqns_tryURefl___lam__1___closed__1));
v___x_983_ = lean_unsigned_to_nat(3u);
v___x_984_ = l_Lean_Expr_isAppOfArity(v_a_978_, v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v_a_978_);
lean_dec(v_mvarId_971_);
v___x_985_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_985_);
v___x_987_ = v___x_980_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_del_object(v___x_980_);
v___x_989_ = l_Lean_Expr_appFn_x21(v_a_978_);
v___x_990_ = l_Lean_Expr_appArg_x21(v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = l_Lean_Expr_appArg_x21(v_a_978_);
lean_dec(v_a_978_);
lean_inc_ref(v___x_990_);
v___x_992_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_990_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1030_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = lean_expr_eqv(v_a_993_, v___x_990_);
lean_dec_ref(v___x_990_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
lean_del_object(v___x_995_);
v___x_998_ = l_Lean_Meta_mkEq(v_a_993_, v___x_991_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_971_, v_a_999_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_a_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1000_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1000_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_mvarId_971_);
v_a_1018_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_998_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_998_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec(v_a_993_);
lean_dec_ref(v___x_991_);
lean_dec(v_mvarId_971_);
v___x_1026_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1026_);
v___x_1028_ = v___x_995_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_990_);
lean_dec(v_mvarId_971_);
v_a_1031_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_992_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_992_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_mvarId_971_);
v_a_1040_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_977_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_977_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; 
lean_inc(v_mvarId_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1061_, 0, v_mvarId_1055_);
v___x_1062_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_tryURefl_spec__5___redArg(v_mvarId_1055_, v___f_1061_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1069_;
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
