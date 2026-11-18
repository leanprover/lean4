// Lean compiler output
// Module: Lean.Meta.Tactic.Refl
// Imports: public import Lean.Meta.Reduce public import Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_refl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__0_value;
static const lean_string_object l_Lean_MVarId_refl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_refl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_refl___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__2_value;
static const lean_string_object l_Lean_MVarId_refl___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "equality lhs"};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_refl___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_refl___lam__0___closed__4;
static const lean_string_object l_Lean_MVarId_refl___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "\nis not definitionally equal to rhs"};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__5 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_MVarId_refl___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_refl___lam__0___closed__6;
static const lean_ctor_object l_Lean_MVarId_refl___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_refl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__7 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__7_value;
static const lean_string_object l_Lean_MVarId_refl___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_MVarId_refl___lam__0___closed__8 = (const lean_object*)&l_Lean_MVarId_refl___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_MVarId_refl___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_refl___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_refl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_MVarId_refl___closed__0 = (const lean_object*)&l_Lean_MVarId_refl___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_refl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_refl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 180, 45, 223, 5, 219, 138, 223)}};
static const lean_object* l_Lean_MVarId_refl___closed__1 = (const lean_object*)&l_Lean_MVarId_refl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_heqOfEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "heq_of_eq"};
static const lean_object* l_Lean_MVarId_heqOfEq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_heqOfEq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_heqOfEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_heqOfEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 243, 206, 193, 60, 85, 181, 135)}};
static const lean_object* l_Lean_MVarId_heqOfEq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_heqOfEq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_heqOfEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_heqOfEq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_heqOfEq___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_of_heq"};
static const lean_object* l_Lean_MVarId_eqOfHEq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_eqOfHEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_eqOfHEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 61, 104, 192, 47, 1, 246, 178)}};
static const lean_object* l_Lean_MVarId_eqOfHEq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_eqOfHEq___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_hrefl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_hrefl___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_hrefl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_hrefl___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_hrefl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_MVarId_hrefl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_hrefl___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_MVarId_refl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 202, 227, 45, 204, 223, 127, 41)}};
static const lean_object* l_Lean_MVarId_hrefl___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_hrefl___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_hrefl___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hrefl"};
static const lean_object* l_Lean_MVarId_hrefl___lam__1___closed__0 = (const lean_object*)&l_Lean_MVarId_hrefl___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_hrefl___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_hrefl___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 0, 103, 192, 146, 115, 118, 96)}};
static const lean_object* l_Lean_MVarId_hrefl___lam__1___closed__1 = (const lean_object*)&l_Lean_MVarId_hrefl___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_51_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_51_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg___boxed(lean_object* v_mvarId_68_, lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_68_, v_x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(lean_object* v_00_u03b1_76_, lean_object* v_mvarId_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___boxed(lean_object* v_00_u03b1_85_, lean_object* v_mvarId_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(v_00_u03b1_85_, v_mvarId_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_ks_98_; lean_object* v_vs_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_123_; 
v_ks_98_ = lean_ctor_get(v_x_94_, 0);
v_vs_99_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_123_ == 0)
{
v___x_101_ = v_x_94_;
v_isShared_102_ = v_isSharedCheck_123_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_vs_99_);
lean_inc(v_ks_98_);
lean_dec(v_x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_123_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_array_get_size(v_ks_98_);
v___x_104_ = lean_nat_dec_lt(v_x_95_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
lean_dec(v_x_95_);
v___x_105_ = lean_array_push(v_ks_98_, v_x_96_);
v___x_106_ = lean_array_push(v_vs_99_, v_x_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_106_);
lean_ctor_set(v___x_101_, 0, v___x_105_);
v___x_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v_k_x27_110_; uint8_t v___x_111_; 
v_k_x27_110_ = lean_array_fget_borrowed(v_ks_98_, v_x_95_);
v___x_111_ = l_Lean_instBEqMVarId_beq(v_x_96_, v_k_x27_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_113_; 
if (v_isShared_102_ == 0)
{
v___x_113_ = v___x_101_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_ks_98_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_vs_99_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_x_95_, v___x_114_);
lean_dec(v_x_95_);
v_x_94_ = v___x_113_;
v_x_95_ = v___x_115_;
goto _start;
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_118_ = lean_array_fset(v_ks_98_, v_x_95_, v_x_96_);
v___x_119_ = lean_array_fset(v_vs_99_, v_x_95_, v_x_97_);
lean_dec(v_x_95_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_119_);
lean_ctor_set(v___x_101_, 0, v___x_118_);
v___x_121_ = v___x_101_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_124_, lean_object* v_k_125_, lean_object* v_v_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_124_, v___x_127_, v_k_125_, v_v_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(lean_object* v_x_130_, size_t v_x_131_, size_t v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v_es_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_j_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_es_135_ = lean_ctor_get(v_x_130_, 0);
v___x_136_ = ((size_t)31ULL);
v___x_137_ = lean_usize_land(v_x_131_, v___x_136_);
v_j_138_ = lean_usize_to_nat(v___x_137_);
v___x_139_ = lean_array_get_size(v_es_135_);
v___x_140_ = lean_nat_dec_lt(v_j_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v_j_138_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
return v_x_130_;
}
else
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_179_; 
lean_inc_ref(v_es_135_);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_x_130_, 0);
lean_dec(v_unused_180_);
v___x_142_ = v_x_130_;
v_isShared_143_ = v_isSharedCheck_179_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_x_130_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_179_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_v_144_; lean_object* v___x_145_; lean_object* v_xs_x27_146_; lean_object* v___y_148_; 
v_v_144_ = lean_array_fget(v_es_135_, v_j_138_);
v___x_145_ = lean_box(0);
v_xs_x27_146_ = lean_array_fset(v_es_135_, v_j_138_, v___x_145_);
switch(lean_obj_tag(v_v_144_))
{
case 0:
{
lean_object* v_key_153_; lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
v_key_153_ = lean_ctor_get(v_v_144_, 0);
v_val_154_ = lean_ctor_get(v_v_144_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_v_144_);
if (v_isSharedCheck_164_ == 0)
{
v___x_156_ = v_v_144_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_inc(v_key_153_);
lean_dec(v_v_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_instBEqMVarId_beq(v_x_133_, v_key_153_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_del_object(v___x_156_);
v___x_159_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_153_, v_val_154_, v_x_133_, v_x_134_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___y_148_ = v___x_160_;
goto v___jp_147_;
}
else
{
lean_object* v___x_162_; 
lean_dec(v_val_154_);
lean_dec(v_key_153_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_x_134_);
lean_ctor_set(v___x_156_, 0, v_x_133_);
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_x_133_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_x_134_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
v___y_148_ = v___x_162_;
goto v___jp_147_;
}
}
}
}
case 1:
{
lean_object* v_node_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_177_; 
v_node_165_ = lean_ctor_get(v_v_144_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v_v_144_);
if (v_isSharedCheck_177_ == 0)
{
v___x_167_ = v_v_144_;
v_isShared_168_ = v_isSharedCheck_177_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_node_165_);
lean_dec(v_v_144_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_177_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_169_ = ((size_t)5ULL);
v___x_170_ = lean_usize_shift_right(v_x_131_, v___x_169_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_x_132_, v___x_171_);
v___x_173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_node_165_, v___x_170_, v___x_172_, v_x_133_, v_x_134_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_173_);
v___x_175_ = v___x_167_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
v___y_148_ = v___x_175_;
goto v___jp_147_;
}
}
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_x_133_);
lean_ctor_set(v___x_178_, 1, v_x_134_);
v___y_148_ = v___x_178_;
goto v___jp_147_;
}
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_array_fset(v_xs_x27_146_, v_j_138_, v___y_148_);
lean_dec(v_j_138_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_149_);
v___x_151_ = v___x_142_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v_ks_181_; lean_object* v_vs_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_200_; 
v_ks_181_ = lean_ctor_get(v_x_130_, 0);
v_vs_182_ = lean_ctor_get(v_x_130_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_200_ == 0)
{
v___x_184_ = v_x_130_;
v_isShared_185_ = v_isSharedCheck_200_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_vs_182_);
lean_inc(v_ks_181_);
lean_dec(v_x_130_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_200_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_ks_181_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_vs_182_);
v___x_187_ = v_reuseFailAlloc_199_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v_newNode_188_; size_t v___x_189_; uint8_t v___x_190_; 
v_newNode_188_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_187_, v_x_133_, v_x_134_);
v___x_189_ = ((size_t)7ULL);
v___x_190_ = lean_usize_dec_le(v___x_189_, v_x_132_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_188_);
v___x_192_ = lean_unsigned_to_nat(4u);
v___x_193_ = lean_nat_dec_lt(v___x_191_, v___x_192_);
lean_dec(v___x_191_);
if (v___x_193_ == 0)
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_ks_194_ = lean_ctor_get(v_newNode_188_, 0);
lean_inc_ref(v_ks_194_);
v_vs_195_ = lean_ctor_get(v_newNode_188_, 1);
lean_inc_ref(v_vs_195_);
lean_dec_ref(v_newNode_188_);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_132_, v_ks_194_, v_vs_195_, v___x_196_, v___x_197_);
lean_dec_ref(v_vs_195_);
lean_dec_ref(v_ks_194_);
return v___x_198_;
}
else
{
return v_newNode_188_;
}
}
else
{
return v_newNode_188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_201_, lean_object* v_keys_202_, lean_object* v_vals_203_, lean_object* v_i_204_, lean_object* v_entries_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_keys_202_);
v___x_207_ = lean_nat_dec_lt(v_i_204_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_i_204_);
return v_entries_205_;
}
else
{
lean_object* v_k_208_; lean_object* v_v_209_; uint64_t v___x_210_; size_t v_h_211_; size_t v___x_212_; lean_object* v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v_h_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_k_208_ = lean_array_fget_borrowed(v_keys_202_, v_i_204_);
v_v_209_ = lean_array_fget_borrowed(v_vals_203_, v_i_204_);
v___x_210_ = l_Lean_instHashableMVarId_hash(v_k_208_);
v_h_211_ = lean_uint64_to_usize(v___x_210_);
v___x_212_ = ((size_t)5ULL);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_sub(v_depth_201_, v___x_214_);
v___x_216_ = lean_usize_mul(v___x_212_, v___x_215_);
v_h_217_ = lean_usize_shift_right(v_h_211_, v___x_216_);
v___x_218_ = lean_nat_add(v_i_204_, v___x_213_);
lean_dec(v_i_204_);
lean_inc(v_v_209_);
lean_inc(v_k_208_);
v___x_219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_entries_205_, v_h_217_, v_depth_201_, v_k_208_, v_v_209_);
v_i_204_ = v___x_218_;
v_entries_205_ = v___x_219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_221_, lean_object* v_keys_222_, lean_object* v_vals_223_, lean_object* v_i_224_, lean_object* v_entries_225_){
_start:
{
size_t v_depth_boxed_226_; lean_object* v_res_227_; 
v_depth_boxed_226_ = lean_unbox_usize(v_depth_221_);
lean_dec(v_depth_221_);
v_res_227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_226_, v_keys_222_, v_vals_223_, v_i_224_, v_entries_225_);
lean_dec_ref(v_vals_223_);
lean_dec_ref(v_keys_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
size_t v_x_2368__boxed_233_; size_t v_x_2369__boxed_234_; lean_object* v_res_235_; 
v_x_2368__boxed_233_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_x_2369__boxed_234_ = lean_unbox_usize(v_x_230_);
lean_dec(v_x_230_);
v_res_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_228_, v_x_2368__boxed_233_, v_x_2369__boxed_234_, v_x_231_, v_x_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v___x_239_ = l_Lean_instHashableMVarId_hash(v_x_237_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_236_, v___x_240_, v___x_241_, v_x_237_, v_x_238_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(lean_object* v_mvarId_243_, lean_object* v_val_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v_mctx_248_; lean_object* v_cache_249_; lean_object* v_zetaDeltaFVarIds_250_; lean_object* v_postponed_251_; lean_object* v_diag_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_281_; 
v___x_247_ = lean_st_ref_take(v___y_245_);
v_mctx_248_ = lean_ctor_get(v___x_247_, 0);
v_cache_249_ = lean_ctor_get(v___x_247_, 1);
v_zetaDeltaFVarIds_250_ = lean_ctor_get(v___x_247_, 2);
v_postponed_251_ = lean_ctor_get(v___x_247_, 3);
v_diag_252_ = lean_ctor_get(v___x_247_, 4);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_281_ == 0)
{
v___x_254_ = v___x_247_;
v_isShared_255_ = v_isSharedCheck_281_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_diag_252_);
lean_inc(v_postponed_251_);
lean_inc(v_zetaDeltaFVarIds_250_);
lean_inc(v_cache_249_);
lean_inc(v_mctx_248_);
lean_dec(v___x_247_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_281_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_depth_256_; lean_object* v_levelAssignDepth_257_; lean_object* v_lmvarCounter_258_; lean_object* v_mvarCounter_259_; lean_object* v_lDecls_260_; lean_object* v_decls_261_; lean_object* v_userNames_262_; lean_object* v_lAssignment_263_; lean_object* v_eAssignment_264_; lean_object* v_dAssignment_265_; lean_object* v_instanceTypedMVars_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_280_; 
v_depth_256_ = lean_ctor_get(v_mctx_248_, 0);
v_levelAssignDepth_257_ = lean_ctor_get(v_mctx_248_, 1);
v_lmvarCounter_258_ = lean_ctor_get(v_mctx_248_, 2);
v_mvarCounter_259_ = lean_ctor_get(v_mctx_248_, 3);
v_lDecls_260_ = lean_ctor_get(v_mctx_248_, 4);
v_decls_261_ = lean_ctor_get(v_mctx_248_, 5);
v_userNames_262_ = lean_ctor_get(v_mctx_248_, 6);
v_lAssignment_263_ = lean_ctor_get(v_mctx_248_, 7);
v_eAssignment_264_ = lean_ctor_get(v_mctx_248_, 8);
v_dAssignment_265_ = lean_ctor_get(v_mctx_248_, 9);
v_instanceTypedMVars_266_ = lean_ctor_get(v_mctx_248_, 10);
v_isSharedCheck_280_ = !lean_is_exclusive(v_mctx_248_);
if (v_isSharedCheck_280_ == 0)
{
v___x_268_ = v_mctx_248_;
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_instanceTypedMVars_266_);
lean_inc(v_dAssignment_265_);
lean_inc(v_eAssignment_264_);
lean_inc(v_lAssignment_263_);
lean_inc(v_userNames_262_);
lean_inc(v_decls_261_);
lean_inc(v_lDecls_260_);
lean_inc(v_mvarCounter_259_);
lean_inc(v_lmvarCounter_258_);
lean_inc(v_levelAssignDepth_257_);
lean_inc(v_depth_256_);
lean_dec(v_mctx_248_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_box(0);
v___x_271_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_eAssignment_264_, v_mvarId_243_, v_val_244_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 8, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_depth_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_levelAssignDepth_257_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_lmvarCounter_258_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_mvarCounter_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_lDecls_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_decls_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_userNames_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_lAssignment_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v_dAssignment_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 10, v_instanceTypedMVars_266_);
v___x_273_ = v_reuseFailAlloc_279_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_273_);
v___x_275_ = v___x_254_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_zetaDeltaFVarIds_250_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_postponed_251_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_diag_252_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_put(v___y_245_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_270_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(lean_object* v_mvarId_282_, lean_object* v_val_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_282_, v_val_283_, v___y_284_);
lean_dec(v___y_284_);
return v_res_286_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__3));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__6(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__5));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__9(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__8));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object* v_mvarId_302_, lean_object* v___x_303_, lean_object* v___x_304_, uint8_t v_check_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
lean_inc(v_mvarId_302_);
v___x_311_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_302_, v___x_303_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_391_; 
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_392_);
v___x_313_ = v___x_311_;
v_isShared_314_ = v_isSharedCheck_391_;
goto v_resetjp_312_;
}
else
{
lean_dec(v___x_311_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_391_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; 
lean_inc(v_mvarId_302_);
v___x_315_ = l_Lean_MVarId_getType_x27(v_mvarId_302_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v___x_372_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__7));
v___x_373_ = lean_unsigned_to_nat(3u);
v___x_374_ = l_Lean_Expr_isAppOfArity(v_a_316_, v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_375_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_376_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__9, &l_Lean_MVarId_refl___lam__0___closed__9_once, _init_l_Lean_MVarId_refl___lam__0___closed__9);
lean_inc(v_a_316_);
v___x_377_ = l_Lean_indentExpr(v_a_316_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 1);
lean_ctor_set(v___x_313_, 0, v___x_378_);
v___x_380_ = v___x_313_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; 
lean_inc(v_mvarId_302_);
v___x_381_ = l_Lean_Meta_throwTacticEx___redArg(v___x_375_, v_mvarId_302_, v___x_380_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_dec_ref_known(v___x_381_, 1);
v___y_334_ = v___y_306_;
v___y_335_ = v___y_307_;
v___y_336_ = v___y_308_;
v___y_337_ = v___y_309_;
goto v___jp_333_;
}
else
{
lean_dec(v_a_316_);
lean_dec_ref(v___x_304_);
lean_dec(v_mvarId_302_);
return v___x_381_;
}
}
}
else
{
lean_del_object(v___x_313_);
v___y_334_ = v___y_306_;
v___y_335_ = v___y_307_;
v___y_336_ = v___y_308_;
v___y_337_ = v___y_309_;
goto v___jp_333_;
}
v___jp_317_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_324_ = l_Lean_Expr_getAppFn(v_a_316_);
lean_dec(v_a_316_);
v___x_325_ = l_Lean_Expr_constLevels_x21(v___x_324_);
lean_dec_ref(v___x_324_);
v___x_326_ = l_Lean_Expr_appFn_x21(v___y_319_);
lean_dec_ref(v___y_319_);
v___x_327_ = l_Lean_Expr_appArg_x21(v___x_326_);
lean_dec_ref(v___x_326_);
v___x_328_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__0));
v___x_329_ = l_Lean_Name_mkStr2(v___x_328_, v___x_304_);
v___x_330_ = l_Lean_mkConst(v___x_329_, v___x_325_);
v___x_331_ = l_Lean_mkAppB(v___x_330_, v___x_327_, v___y_318_);
v___x_332_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_302_, v___x_331_, v___y_321_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = l_Lean_Expr_appFn_x21(v_a_316_);
v___x_339_ = l_Lean_Expr_appArg_x21(v___x_338_);
v___x_340_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_339_, v___y_335_);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = l_Lean_Expr_appArg_x21(v_a_316_);
v___x_343_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_342_, v___y_335_);
if (v_check_305_ == 0)
{
lean_dec_ref(v___x_343_);
v___y_318_ = v_a_341_;
v___y_319_ = v___x_338_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
goto v___jp_317_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_371_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_371_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_371_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_371_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; 
lean_inc(v_a_344_);
lean_inc(v_a_341_);
v___x_348_ = l_Lean_Meta_isExprDefEq(v_a_341_, v_a_344_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; uint8_t v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = lean_unbox(v_a_349_);
lean_dec(v_a_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_351_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_352_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__4, &l_Lean_MVarId_refl___lam__0___closed__4_once, _init_l_Lean_MVarId_refl___lam__0___closed__4);
lean_inc(v_a_341_);
v___x_353_ = l_Lean_indentExpr(v_a_341_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__6, &l_Lean_MVarId_refl___lam__0___closed__6_once, _init_l_Lean_MVarId_refl___lam__0___closed__6);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_indentExpr(v_a_344_);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 1);
lean_ctor_set(v___x_346_, 0, v___x_358_);
v___x_360_ = v___x_346_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
lean_inc(v_mvarId_302_);
v___x_361_ = l_Lean_Meta_throwTacticEx___redArg(v___x_351_, v_mvarId_302_, v___x_360_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_dec_ref_known(v___x_361_, 1);
v___y_318_ = v_a_341_;
v___y_319_ = v___x_338_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
goto v___jp_317_;
}
else
{
lean_dec(v_a_341_);
lean_dec_ref(v___x_338_);
lean_dec(v_a_316_);
lean_dec_ref(v___x_304_);
lean_dec(v_mvarId_302_);
return v___x_361_;
}
}
}
else
{
lean_del_object(v___x_346_);
lean_dec(v_a_344_);
v___y_318_ = v_a_341_;
v___y_319_ = v___x_338_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
goto v___jp_317_;
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_del_object(v___x_346_);
lean_dec(v_a_344_);
lean_dec(v_a_341_);
lean_dec_ref(v___x_338_);
lean_dec(v_a_316_);
lean_dec_ref(v___x_304_);
lean_dec(v_mvarId_302_);
v_a_363_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_348_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_348_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_313_);
lean_dec_ref(v___x_304_);
lean_dec(v_mvarId_302_);
v_a_383_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_315_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_315_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_304_);
lean_dec(v_mvarId_302_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0___boxed(lean_object* v_mvarId_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_check_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v_check_boxed_402_; lean_object* v_res_403_; 
v_check_boxed_402_ = lean_unbox(v_check_396_);
v_res_403_ = l_Lean_MVarId_refl___lam__0(v_mvarId_393_, v___x_394_, v___x_395_, v_check_boxed_402_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object* v_mvarId_407_, uint8_t v_check_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Lean_MVarId_refl___closed__0));
v___x_415_ = ((lean_object*)(l_Lean_MVarId_refl___closed__1));
v___x_416_ = lean_box(v_check_408_);
lean_inc(v_mvarId_407_);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_417_, 0, v_mvarId_407_);
lean_closure_set(v___f_417_, 1, v___x_415_);
lean_closure_set(v___f_417_, 2, v___x_414_);
lean_closure_set(v___f_417_, 3, v___x_416_);
v___x_418_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_407_, v___f_417_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object* v_mvarId_419_, lean_object* v_check_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
uint8_t v_check_boxed_426_; lean_object* v_res_427_; 
v_check_boxed_426_ = lean_unbox(v_check_420_);
v_res_427_ = l_Lean_MVarId_refl(v_mvarId_419_, v_check_boxed_426_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(lean_object* v_mvarId_428_, lean_object* v_val_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_428_, v_val_429_, v___y_431_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(lean_object* v_mvarId_436_, lean_object* v_val_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(v_mvarId_436_, v_val_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(lean_object* v_00_u03b2_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_x_445_, v_x_446_, v_x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_449_, lean_object* v_x_450_, size_t v_x_451_, size_t v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_450_, v_x_451_, v_x_452_, v_x_453_, v_x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
size_t v_x_2867__boxed_462_; size_t v_x_2868__boxed_463_; lean_object* v_res_464_; 
v_x_2867__boxed_462_ = lean_unbox_usize(v_x_458_);
lean_dec(v_x_458_);
v_x_2868__boxed_463_ = lean_unbox_usize(v_x_459_);
lean_dec(v_x_459_);
v_res_464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(v_00_u03b2_456_, v_x_457_, v_x_2867__boxed_462_, v_x_2868__boxed_463_, v_x_460_, v_x_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_465_, lean_object* v_n_466_, lean_object* v_k_467_, lean_object* v_v_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_466_, v_k_467_, v_v_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_470_, size_t v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_heq_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_471_, v_keys_472_, v_vals_473_, v_i_475_, v_entries_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_478_, lean_object* v_depth_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_entries_484_){
_start:
{
size_t v_depth_boxed_485_; lean_object* v_res_486_; 
v_depth_boxed_485_ = lean_unbox_usize(v_depth_479_);
lean_dec(v_depth_479_);
v_res_486_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_478_, v_depth_boxed_485_, v_keys_480_, v_vals_481_, v_heq_482_, v_i_483_, v_entries_484_);
lean_dec_ref(v_vals_481_);
lean_dec_ref(v_keys_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_488_, v_x_489_, v_x_490_, v_x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve(lean_object* v_rfl_493_, lean_object* v_prove_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; uint8_t v_foApprox_501_; uint8_t v_ctxApprox_502_; uint8_t v_quasiPatternApprox_503_; uint8_t v_constApprox_504_; uint8_t v_isDefEqStuckEx_505_; uint8_t v_unificationHints_506_; uint8_t v_proofIrrelevance_507_; uint8_t v_assignSyntheticOpaque_508_; uint8_t v_offsetCnstrs_509_; uint8_t v_transparency_510_; uint8_t v_etaStruct_511_; uint8_t v_univApprox_512_; uint8_t v_iota_513_; uint8_t v_beta_514_; uint8_t v_proj_515_; uint8_t v_zeta_516_; uint8_t v_zetaDelta_517_; uint8_t v_zetaUnused_518_; uint8_t v_zetaHave_519_; uint8_t v_canUnfoldPredicateConfig_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_572_; 
v___x_500_ = l_Lean_Meta_Context_config(v_a_495_);
v_foApprox_501_ = lean_ctor_get_uint8(v___x_500_, 0);
v_ctxApprox_502_ = lean_ctor_get_uint8(v___x_500_, 1);
v_quasiPatternApprox_503_ = lean_ctor_get_uint8(v___x_500_, 2);
v_constApprox_504_ = lean_ctor_get_uint8(v___x_500_, 3);
v_isDefEqStuckEx_505_ = lean_ctor_get_uint8(v___x_500_, 4);
v_unificationHints_506_ = lean_ctor_get_uint8(v___x_500_, 5);
v_proofIrrelevance_507_ = lean_ctor_get_uint8(v___x_500_, 6);
v_assignSyntheticOpaque_508_ = lean_ctor_get_uint8(v___x_500_, 7);
v_offsetCnstrs_509_ = lean_ctor_get_uint8(v___x_500_, 8);
v_transparency_510_ = lean_ctor_get_uint8(v___x_500_, 9);
v_etaStruct_511_ = lean_ctor_get_uint8(v___x_500_, 10);
v_univApprox_512_ = lean_ctor_get_uint8(v___x_500_, 11);
v_iota_513_ = lean_ctor_get_uint8(v___x_500_, 12);
v_beta_514_ = lean_ctor_get_uint8(v___x_500_, 13);
v_proj_515_ = lean_ctor_get_uint8(v___x_500_, 14);
v_zeta_516_ = lean_ctor_get_uint8(v___x_500_, 15);
v_zetaDelta_517_ = lean_ctor_get_uint8(v___x_500_, 16);
v_zetaUnused_518_ = lean_ctor_get_uint8(v___x_500_, 17);
v_zetaHave_519_ = lean_ctor_get_uint8(v___x_500_, 18);
v_canUnfoldPredicateConfig_520_ = lean_ctor_get_uint8(v___x_500_, 19);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_572_ == 0)
{
v___x_522_ = v___x_500_;
v_isShared_523_ = v_isSharedCheck_572_;
goto v_resetjp_521_;
}
else
{
lean_dec(v___x_500_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_572_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v_trackZetaDelta_524_; lean_object* v_zetaDeltaSet_525_; lean_object* v_lctx_526_; lean_object* v_localInstances_527_; lean_object* v_defEqCtx_x3f_528_; lean_object* v_synthPendingDepth_529_; lean_object* v_customCanUnfoldPredicate_x3f_530_; uint8_t v_univApprox_531_; uint8_t v_inTypeClassResolution_532_; uint8_t v_cacheInferType_533_; uint8_t v___x_534_; lean_object* v___x_536_; 
v_trackZetaDelta_524_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*7);
v_zetaDeltaSet_525_ = lean_ctor_get(v_a_495_, 1);
v_lctx_526_ = lean_ctor_get(v_a_495_, 2);
v_localInstances_527_ = lean_ctor_get(v_a_495_, 3);
v_defEqCtx_x3f_528_ = lean_ctor_get(v_a_495_, 4);
v_synthPendingDepth_529_ = lean_ctor_get(v_a_495_, 5);
v_customCanUnfoldPredicate_x3f_530_ = lean_ctor_get(v_a_495_, 6);
v_univApprox_531_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_532_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*7 + 2);
v_cacheInferType_533_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*7 + 3);
v___x_534_ = 0;
if (v_isShared_523_ == 0)
{
v___x_536_ = v___x_522_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 0, v_foApprox_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 1, v_ctxApprox_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 2, v_quasiPatternApprox_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 3, v_constApprox_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 4, v_isDefEqStuckEx_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 5, v_unificationHints_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 6, v_proofIrrelevance_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 7, v_assignSyntheticOpaque_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 8, v_offsetCnstrs_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 9, v_transparency_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 10, v_etaStruct_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 11, v_univApprox_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 12, v_iota_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 13, v_beta_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 14, v_proj_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 15, v_zeta_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 16, v_zetaDelta_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 17, v_zetaUnused_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 18, v_zetaHave_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 19, v_canUnfoldPredicateConfig_520_);
v___x_536_ = v_reuseFailAlloc_571_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
uint64_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_ctor_set_uint8(v___x_536_, 20, v___x_534_);
v___x_537_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint64(v___x_538_, sizeof(void*)*1, v___x_537_);
lean_inc(v_customCanUnfoldPredicate_x3f_530_);
lean_inc(v_synthPendingDepth_529_);
lean_inc(v_defEqCtx_x3f_528_);
lean_inc_ref(v_localInstances_527_);
lean_inc_ref(v_lctx_526_);
lean_inc(v_zetaDeltaSet_525_);
v___x_539_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_zetaDeltaSet_525_);
lean_ctor_set(v___x_539_, 2, v_lctx_526_);
lean_ctor_set(v___x_539_, 3, v_localInstances_527_);
lean_ctor_set(v___x_539_, 4, v_defEqCtx_x3f_528_);
lean_ctor_set(v___x_539_, 5, v_synthPendingDepth_529_);
lean_ctor_set(v___x_539_, 6, v_customCanUnfoldPredicate_x3f_530_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7, v_trackZetaDelta_524_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 1, v_univApprox_531_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 2, v_inTypeClassResolution_532_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 3, v_cacheInferType_533_);
lean_inc_ref(v_rfl_493_);
lean_inc(v_a_498_);
lean_inc_ref(v_a_497_);
lean_inc(v_a_496_);
v___x_540_ = lean_apply_5(v_rfl_493_, v___x_539_, v_a_496_, v_a_497_, v_a_498_, lean_box(0));
if (lean_obj_tag(v___x_540_) == 0)
{
lean_dec_ref(v_prove_494_);
lean_dec_ref(v_rfl_493_);
return v___x_540_;
}
else
{
lean_object* v_a_541_; uint8_t v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
v___x_542_ = l_Lean_Exception_isInterrupt(v_a_541_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Exception_isRuntime(v_a_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_540_, 1);
v___x_544_ = l_Lean_Meta_saveState___redArg(v_a_496_, v_a_498_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
lean_inc(v_a_498_);
lean_inc_ref(v_a_497_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
v___x_546_ = lean_apply_5(v_prove_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, lean_box(0));
if (lean_obj_tag(v___x_546_) == 0)
{
lean_dec(v_a_545_);
lean_dec_ref(v_rfl_493_);
return v___x_546_;
}
else
{
lean_object* v_a_547_; uint8_t v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
v___x_548_ = l_Lean_Exception_isInterrupt(v_a_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
lean_inc(v_a_547_);
v___x_549_ = l_Lean_Exception_isRuntime(v_a_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_550_ = l_Lean_Meta_SavedState_restore___redArg(v_a_545_, v_a_496_, v_a_498_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; 
lean_dec_ref_known(v___x_550_, 1);
lean_inc(v_a_498_);
lean_inc_ref(v_a_497_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
v___x_551_ = lean_apply_5(v_rfl_493_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, lean_box(0));
if (lean_obj_tag(v___x_551_) == 0)
{
lean_dec(v_a_547_);
return v___x_551_;
}
else
{
lean_object* v_a_552_; uint8_t v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
v___x_553_ = l_Lean_Exception_isInterrupt(v_a_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Exception_isRuntime(v_a_552_);
if (v___x_554_ == 0)
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_562_);
v___x_556_ = v___x_551_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_dec(v___x_551_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_a_547_);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_547_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_dec(v_a_547_);
return v___x_551_;
}
}
else
{
lean_dec(v_a_552_);
lean_dec(v_a_547_);
return v___x_551_;
}
}
}
else
{
lean_dec(v_a_547_);
lean_dec_ref(v_rfl_493_);
return v___x_550_;
}
}
else
{
lean_dec(v_a_547_);
lean_dec(v_a_545_);
lean_dec_ref(v_rfl_493_);
return v___x_546_;
}
}
else
{
lean_dec(v_a_547_);
lean_dec(v_a_545_);
lean_dec_ref(v_rfl_493_);
return v___x_546_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_prove_494_);
lean_dec_ref(v_rfl_493_);
v_a_563_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_544_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_544_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_dec_ref(v_prove_494_);
lean_dec_ref(v_rfl_493_);
return v___x_540_;
}
}
else
{
lean_dec(v_a_541_);
lean_dec_ref(v_prove_494_);
lean_dec_ref(v_rfl_493_);
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve___boxed(lean_object* v_rfl_573_, lean_object* v_prove_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_reflOrProve(v_rfl_573_, v_prove_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(lean_object* v_x_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_saveState___redArg(v___y_583_, v___y_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
v___x_589_ = lean_apply_5(v_x_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_a_588_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v_a_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_629_; 
v_a_599_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_629_ == 0)
{
v___x_601_ = v___x_589_;
v_isShared_602_ = v_isSharedCheck_629_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_629_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_Exception_isInterrupt(v_a_599_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
lean_inc(v_a_599_);
v___x_604_ = l_Lean_Exception_isRuntime(v_a_599_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_del_object(v___x_601_);
lean_dec(v_a_599_);
v___x_605_ = l_Lean_Meta_SavedState_restore___redArg(v_a_588_, v___y_583_, v___y_585_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_605_, 0);
lean_dec(v_unused_614_);
v___x_607_ = v___x_605_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_dec(v___x_605_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_605_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_a_588_);
if (v_isShared_602_ == 0)
{
v___x_624_ = v___x_601_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_599_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_a_588_);
if (v_isShared_602_ == 0)
{
v___x_627_ = v___x_601_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_599_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_x_581_);
v_a_630_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_587_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_587_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(lean_object* v_00_u03b1_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(lean_object* v_00_u03b1_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(v_00_u03b1_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object* v_mvarId_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Meta_mkFreshLevelMVar(v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__1));
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_675_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_mkConst(v___x_676_, v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_681_ = lean_box(0);
v___x_682_ = l_Lean_MVarId_apply(v_mvarId_668_, v___x_679_, v___x_680_, v___x_681_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_mvarId_668_);
v_a_683_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_674_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_674_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object* v_mvarId_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_MVarId_heqOfEq___lam__0(v_mvarId_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object* v___f_698_, lean_object* v_mvarId_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_698_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_725_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_725_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
if (lean_obj_tag(v_a_706_) == 1)
{
lean_object* v_val_710_; 
v_val_710_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v_a_706_, 1);
if (lean_obj_tag(v_val_710_) == 1)
{
lean_object* v_tail_711_; 
v_tail_711_ = lean_ctor_get(v_val_710_, 1);
if (lean_obj_tag(v_tail_711_) == 0)
{
lean_object* v_head_712_; lean_object* v___x_714_; 
lean_dec(v_mvarId_699_);
v_head_712_ = lean_ctor_get(v_val_710_, 0);
lean_inc(v_head_712_);
lean_dec_ref_known(v_val_710_, 2);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_head_712_);
v___x_714_ = v___x_708_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_head_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec_ref_known(v_val_710_, 2);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_mvarId_699_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_mvarId_699_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_720_; 
lean_dec(v_val_710_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_mvarId_699_);
v___x_720_ = v___x_708_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_mvarId_699_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_mvarId_699_);
v___x_723_ = v___x_708_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_mvarId_699_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_mvarId_699_);
v_a_726_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_705_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_705_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1___boxed(lean_object* v___f_734_, lean_object* v_mvarId_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_MVarId_heqOfEq___lam__1(v___f_734_, v_mvarId_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object* v_mvarId_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
lean_inc_n(v_mvarId_742_, 2);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_748_, 0, v_mvarId_742_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_749_, 0, v___f_748_);
lean_closure_set(v___f_749_, 1, v_mvarId_742_);
v___x_750_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_742_, v___f_749_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object* v_mvarId_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_MVarId_heqOfEq(v_mvarId_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object* v_mvarId_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_mkFreshLevelMVar(v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = ((lean_object*)(l_Lean_MVarId_eqOfHEq___lam__0___closed__1));
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v_a_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_mkConst(v___x_769_, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_774_ = lean_box(0);
v___x_775_ = l_Lean_MVarId_apply(v_mvarId_761_, v___x_772_, v___x_773_, v___x_774_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_mvarId_761_);
v_a_776_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_767_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object* v_mvarId_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_MVarId_eqOfHEq___lam__0(v_mvarId_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object* v_mvarId_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; 
lean_inc_n(v_mvarId_791_, 2);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_797_, 0, v_mvarId_791_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_798_, 0, v___f_797_);
lean_closure_set(v___f_798_, 1, v_mvarId_791_);
v___x_799_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_791_, v___f_798_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object* v_mvarId_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_MVarId_eqOfHEq(v_mvarId_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object* v_mvarId_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_mkFreshLevelMVar(v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__0___closed__1));
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_mkConst(v___x_819_, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_MVarId_apply(v_mvarId_811_, v___x_822_, v___x_823_, v___x_824_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_825_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_mvarId_811_);
v_a_826_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_817_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_817_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object* v_mvarId_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_MVarId_hrefl___lam__0(v_mvarId_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object* v_mvarId_844_, lean_object* v___f_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_a_856_) == 1)
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_a_856_, 1);
if (lean_obj_tag(v_val_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v_mvarId_844_);
v___x_861_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_dec(v_val_860_);
lean_del_object(v___x_858_);
goto v___jp_851_;
}
}
else
{
lean_del_object(v___x_858_);
lean_dec(v_a_856_);
goto v___jp_851_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_mvarId_844_);
v_a_866_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_855_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
v___jp_851_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__1___closed__1));
v___x_853_ = lean_box(0);
v___x_854_ = l_Lean_Meta_throwTacticEx___redArg(v___x_852_, v_mvarId_844_, v___x_853_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1___boxed(lean_object* v_mvarId_874_, lean_object* v___f_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_MVarId_hrefl___lam__1(v_mvarId_874_, v___f_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object* v_mvarId_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_890_; 
lean_inc_n(v_mvarId_882_, 2);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_888_, 0, v_mvarId_882_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_889_, 0, v_mvarId_882_);
lean_closure_set(v___f_889_, 1, v___f_888_);
v___x_890_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_882_, v___f_889_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object* v_mvarId_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_MVarId_hrefl(v_mvarId_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_897_;
}
}
lean_object* runtime_initialize_Lean_Meta_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Refl(builtin);
}
#ifdef __cplusplus
}
#endif
