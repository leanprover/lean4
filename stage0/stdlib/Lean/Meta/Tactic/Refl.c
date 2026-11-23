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
size_t v_x_2364__boxed_233_; size_t v_x_2365__boxed_234_; lean_object* v_res_235_; 
v_x_2364__boxed_233_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_x_2365__boxed_234_ = lean_unbox_usize(v_x_230_);
lean_dec(v_x_230_);
v_res_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_228_, v_x_2364__boxed_233_, v_x_2365__boxed_234_, v_x_231_, v_x_232_);
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
lean_object* v___x_247_; lean_object* v_mctx_248_; lean_object* v_cache_249_; lean_object* v_zetaDeltaFVarIds_250_; lean_object* v_postponed_251_; lean_object* v_diag_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_280_; 
v___x_247_ = lean_st_ref_take(v___y_245_);
v_mctx_248_ = lean_ctor_get(v___x_247_, 0);
v_cache_249_ = lean_ctor_get(v___x_247_, 1);
v_zetaDeltaFVarIds_250_ = lean_ctor_get(v___x_247_, 2);
v_postponed_251_ = lean_ctor_get(v___x_247_, 3);
v_diag_252_ = lean_ctor_get(v___x_247_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_280_ == 0)
{
v___x_254_ = v___x_247_;
v_isShared_255_ = v_isSharedCheck_280_;
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
v_isShared_255_ = v_isSharedCheck_280_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_depth_256_; lean_object* v_levelAssignDepth_257_; lean_object* v_lmvarCounter_258_; lean_object* v_mvarCounter_259_; lean_object* v_lDecls_260_; lean_object* v_decls_261_; lean_object* v_userNames_262_; lean_object* v_lAssignment_263_; lean_object* v_eAssignment_264_; lean_object* v_dAssignment_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_279_; 
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
v_isSharedCheck_279_ = !lean_is_exclusive(v_mctx_248_);
if (v_isSharedCheck_279_ == 0)
{
v___x_267_ = v_mctx_248_;
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
else
{
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
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = lean_box(0);
v___x_270_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_eAssignment_264_, v_mvarId_243_, v_val_244_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 8, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_depth_256_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_levelAssignDepth_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_lmvarCounter_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_mvarCounter_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_lDecls_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_decls_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_userNames_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_lAssignment_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 8, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_278_, 9, v_dAssignment_265_);
v___x_272_ = v_reuseFailAlloc_278_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_272_);
v___x_274_ = v___x_254_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_zetaDeltaFVarIds_250_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_postponed_251_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_diag_252_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_put(v___y_245_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_269_);
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(lean_object* v_mvarId_281_, lean_object* v_val_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_281_, v_val_282_, v___y_283_);
lean_dec(v___y_283_);
return v_res_285_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__3));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__6(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__5));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__9(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__8));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object* v_mvarId_301_, lean_object* v___x_302_, lean_object* v___x_303_, uint8_t v_check_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
lean_inc(v_mvarId_301_);
v___x_310_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_301_, v___x_302_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_390_; 
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_391_);
v___x_312_ = v___x_310_;
v_isShared_313_ = v_isSharedCheck_390_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_310_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_390_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; 
lean_inc(v_mvarId_301_);
v___x_314_ = l_Lean_MVarId_getType_x27(v_mvarId_301_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_371_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__7));
v___x_372_ = lean_unsigned_to_nat(3u);
v___x_373_ = l_Lean_Expr_isAppOfArity(v_a_315_, v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_374_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_375_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__9, &l_Lean_MVarId_refl___lam__0___closed__9_once, _init_l_Lean_MVarId_refl___lam__0___closed__9);
lean_inc(v_a_315_);
v___x_376_ = l_Lean_indentExpr(v_a_315_);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 0, v___x_377_);
v___x_379_ = v___x_312_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
lean_inc(v_mvarId_301_);
v___x_380_ = l_Lean_Meta_throwTacticEx___redArg(v___x_374_, v_mvarId_301_, v___x_379_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_dec_ref_known(v___x_380_, 1);
v___y_333_ = v___y_305_;
v___y_334_ = v___y_306_;
v___y_335_ = v___y_307_;
v___y_336_ = v___y_308_;
goto v___jp_332_;
}
else
{
lean_dec(v_a_315_);
lean_dec_ref(v___x_303_);
lean_dec(v_mvarId_301_);
return v___x_380_;
}
}
}
else
{
lean_del_object(v___x_312_);
v___y_333_ = v___y_305_;
v___y_334_ = v___y_306_;
v___y_335_ = v___y_307_;
v___y_336_ = v___y_308_;
goto v___jp_332_;
}
v___jp_316_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_323_ = l_Lean_Expr_getAppFn(v_a_315_);
lean_dec(v_a_315_);
v___x_324_ = l_Lean_Expr_constLevels_x21(v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = l_Lean_Expr_appFn_x21(v___y_318_);
lean_dec_ref(v___y_318_);
v___x_326_ = l_Lean_Expr_appArg_x21(v___x_325_);
lean_dec_ref(v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__0));
v___x_328_ = l_Lean_Name_mkStr2(v___x_327_, v___x_303_);
v___x_329_ = l_Lean_mkConst(v___x_328_, v___x_324_);
v___x_330_ = l_Lean_mkAppB(v___x_329_, v___x_326_, v___y_317_);
v___x_331_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_301_, v___x_330_, v___y_320_);
return v___x_331_;
}
v___jp_332_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = l_Lean_Expr_appFn_x21(v_a_315_);
v___x_338_ = l_Lean_Expr_appArg_x21(v___x_337_);
v___x_339_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_338_, v___y_334_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
v___x_341_ = l_Lean_Expr_appArg_x21(v_a_315_);
v___x_342_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_341_, v___y_334_);
if (v_check_304_ == 0)
{
lean_dec_ref(v___x_342_);
v___y_317_ = v_a_340_;
v___y_318_ = v___x_337_;
v___y_319_ = v___y_333_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
goto v___jp_316_;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_370_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_370_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_370_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_370_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; 
lean_inc(v_a_343_);
lean_inc(v_a_340_);
v___x_347_ = l_Lean_Meta_isExprDefEq(v_a_340_, v_a_343_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; uint8_t v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_350_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_351_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__4, &l_Lean_MVarId_refl___lam__0___closed__4_once, _init_l_Lean_MVarId_refl___lam__0___closed__4);
lean_inc(v_a_340_);
v___x_352_ = l_Lean_indentExpr(v_a_340_);
v___x_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__6, &l_Lean_MVarId_refl___lam__0___closed__6_once, _init_l_Lean_MVarId_refl___lam__0___closed__6);
v___x_355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_indentExpr(v_a_343_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 1);
lean_ctor_set(v___x_345_, 0, v___x_357_);
v___x_359_ = v___x_345_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
lean_inc(v_mvarId_301_);
v___x_360_ = l_Lean_Meta_throwTacticEx___redArg(v___x_350_, v_mvarId_301_, v___x_359_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_dec_ref_known(v___x_360_, 1);
v___y_317_ = v_a_340_;
v___y_318_ = v___x_337_;
v___y_319_ = v___y_333_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
goto v___jp_316_;
}
else
{
lean_dec(v_a_340_);
lean_dec_ref(v___x_337_);
lean_dec(v_a_315_);
lean_dec_ref(v___x_303_);
lean_dec(v_mvarId_301_);
return v___x_360_;
}
}
}
else
{
lean_del_object(v___x_345_);
lean_dec(v_a_343_);
v___y_317_ = v_a_340_;
v___y_318_ = v___x_337_;
v___y_319_ = v___y_333_;
v___y_320_ = v___y_334_;
v___y_321_ = v___y_335_;
v___y_322_ = v___y_336_;
goto v___jp_316_;
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_del_object(v___x_345_);
lean_dec(v_a_343_);
lean_dec(v_a_340_);
lean_dec_ref(v___x_337_);
lean_dec(v_a_315_);
lean_dec_ref(v___x_303_);
lean_dec(v_mvarId_301_);
v_a_362_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_347_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_347_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_del_object(v___x_312_);
lean_dec_ref(v___x_303_);
lean_dec(v_mvarId_301_);
v_a_382_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_314_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_314_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_303_);
lean_dec(v_mvarId_301_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0___boxed(lean_object* v_mvarId_392_, lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_check_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v_check_boxed_401_; lean_object* v_res_402_; 
v_check_boxed_401_ = lean_unbox(v_check_395_);
v_res_402_ = l_Lean_MVarId_refl___lam__0(v_mvarId_392_, v___x_393_, v___x_394_, v_check_boxed_401_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object* v_mvarId_406_, uint8_t v_check_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___x_417_; 
v___x_413_ = ((lean_object*)(l_Lean_MVarId_refl___closed__0));
v___x_414_ = ((lean_object*)(l_Lean_MVarId_refl___closed__1));
v___x_415_ = lean_box(v_check_407_);
lean_inc(v_mvarId_406_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_416_, 0, v_mvarId_406_);
lean_closure_set(v___f_416_, 1, v___x_414_);
lean_closure_set(v___f_416_, 2, v___x_413_);
lean_closure_set(v___f_416_, 3, v___x_415_);
v___x_417_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_406_, v___f_416_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object* v_mvarId_418_, lean_object* v_check_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_check_boxed_425_; lean_object* v_res_426_; 
v_check_boxed_425_ = lean_unbox(v_check_419_);
v_res_426_ = l_Lean_MVarId_refl(v_mvarId_418_, v_check_boxed_425_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(lean_object* v_mvarId_427_, lean_object* v_val_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_427_, v_val_428_, v___y_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(lean_object* v_mvarId_435_, lean_object* v_val_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(v_mvarId_435_, v_val_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, size_t v_x_450_, size_t v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_449_, v_x_450_, v_x_451_, v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
size_t v_x_2863__boxed_461_; size_t v_x_2864__boxed_462_; lean_object* v_res_463_; 
v_x_2863__boxed_461_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_x_2864__boxed_462_ = lean_unbox_usize(v_x_458_);
lean_dec(v_x_458_);
v_res_463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(v_00_u03b2_455_, v_x_456_, v_x_2863__boxed_461_, v_x_2864__boxed_462_, v_x_459_, v_x_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_464_, lean_object* v_n_465_, lean_object* v_k_466_, lean_object* v_v_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_465_, v_k_466_, v_v_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_469_, size_t v_depth_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_470_, v_keys_471_, v_vals_472_, v_i_474_, v_entries_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_477_, lean_object* v_depth_478_, lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_heq_481_, lean_object* v_i_482_, lean_object* v_entries_483_){
_start:
{
size_t v_depth_boxed_484_; lean_object* v_res_485_; 
v_depth_boxed_484_ = lean_unbox_usize(v_depth_478_);
lean_dec(v_depth_478_);
v_res_485_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_477_, v_depth_boxed_484_, v_keys_479_, v_vals_480_, v_heq_481_, v_i_482_, v_entries_483_);
lean_dec_ref(v_vals_480_);
lean_dec_ref(v_keys_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_487_, v_x_488_, v_x_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve(lean_object* v_rfl_492_, lean_object* v_prove_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; uint8_t v_foApprox_500_; uint8_t v_ctxApprox_501_; uint8_t v_quasiPatternApprox_502_; uint8_t v_constApprox_503_; uint8_t v_isDefEqStuckEx_504_; uint8_t v_unificationHints_505_; uint8_t v_proofIrrelevance_506_; uint8_t v_assignSyntheticOpaque_507_; uint8_t v_offsetCnstrs_508_; uint8_t v_transparency_509_; uint8_t v_etaStruct_510_; uint8_t v_univApprox_511_; uint8_t v_iota_512_; uint8_t v_beta_513_; uint8_t v_proj_514_; uint8_t v_zeta_515_; uint8_t v_zetaDelta_516_; uint8_t v_zetaUnused_517_; uint8_t v_zetaHave_518_; uint8_t v_canUnfoldPredicateConfig_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_571_; 
v___x_499_ = l_Lean_Meta_Context_config(v_a_494_);
v_foApprox_500_ = lean_ctor_get_uint8(v___x_499_, 0);
v_ctxApprox_501_ = lean_ctor_get_uint8(v___x_499_, 1);
v_quasiPatternApprox_502_ = lean_ctor_get_uint8(v___x_499_, 2);
v_constApprox_503_ = lean_ctor_get_uint8(v___x_499_, 3);
v_isDefEqStuckEx_504_ = lean_ctor_get_uint8(v___x_499_, 4);
v_unificationHints_505_ = lean_ctor_get_uint8(v___x_499_, 5);
v_proofIrrelevance_506_ = lean_ctor_get_uint8(v___x_499_, 6);
v_assignSyntheticOpaque_507_ = lean_ctor_get_uint8(v___x_499_, 7);
v_offsetCnstrs_508_ = lean_ctor_get_uint8(v___x_499_, 8);
v_transparency_509_ = lean_ctor_get_uint8(v___x_499_, 9);
v_etaStruct_510_ = lean_ctor_get_uint8(v___x_499_, 10);
v_univApprox_511_ = lean_ctor_get_uint8(v___x_499_, 11);
v_iota_512_ = lean_ctor_get_uint8(v___x_499_, 12);
v_beta_513_ = lean_ctor_get_uint8(v___x_499_, 13);
v_proj_514_ = lean_ctor_get_uint8(v___x_499_, 14);
v_zeta_515_ = lean_ctor_get_uint8(v___x_499_, 15);
v_zetaDelta_516_ = lean_ctor_get_uint8(v___x_499_, 16);
v_zetaUnused_517_ = lean_ctor_get_uint8(v___x_499_, 17);
v_zetaHave_518_ = lean_ctor_get_uint8(v___x_499_, 18);
v_canUnfoldPredicateConfig_519_ = lean_ctor_get_uint8(v___x_499_, 19);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_571_ == 0)
{
v___x_521_ = v___x_499_;
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_499_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v_trackZetaDelta_523_; lean_object* v_zetaDeltaSet_524_; lean_object* v_lctx_525_; lean_object* v_localInstances_526_; lean_object* v_defEqCtx_x3f_527_; lean_object* v_synthPendingDepth_528_; lean_object* v_customCanUnfoldPredicate_x3f_529_; uint8_t v_univApprox_530_; uint8_t v_inTypeClassResolution_531_; uint8_t v_cacheInferType_532_; uint8_t v___x_533_; lean_object* v___x_535_; 
v_trackZetaDelta_523_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*7);
v_zetaDeltaSet_524_ = lean_ctor_get(v_a_494_, 1);
v_lctx_525_ = lean_ctor_get(v_a_494_, 2);
v_localInstances_526_ = lean_ctor_get(v_a_494_, 3);
v_defEqCtx_x3f_527_ = lean_ctor_get(v_a_494_, 4);
v_synthPendingDepth_528_ = lean_ctor_get(v_a_494_, 5);
v_customCanUnfoldPredicate_x3f_529_ = lean_ctor_get(v_a_494_, 6);
v_univApprox_530_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_531_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*7 + 2);
v_cacheInferType_532_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*7 + 3);
v___x_533_ = 0;
if (v_isShared_522_ == 0)
{
v___x_535_ = v___x_521_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 0, v_foApprox_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 1, v_ctxApprox_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 2, v_quasiPatternApprox_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 3, v_constApprox_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 4, v_isDefEqStuckEx_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 5, v_unificationHints_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 6, v_proofIrrelevance_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 7, v_assignSyntheticOpaque_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 8, v_offsetCnstrs_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 9, v_transparency_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 10, v_etaStruct_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 11, v_univApprox_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 12, v_iota_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 13, v_beta_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 14, v_proj_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 15, v_zeta_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 16, v_zetaDelta_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 17, v_zetaUnused_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 18, v_zetaHave_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, 19, v_canUnfoldPredicateConfig_519_);
v___x_535_ = v_reuseFailAlloc_570_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
uint64_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_ctor_set_uint8(v___x_535_, 20, v___x_533_);
v___x_536_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set_uint64(v___x_537_, sizeof(void*)*1, v___x_536_);
lean_inc(v_customCanUnfoldPredicate_x3f_529_);
lean_inc(v_synthPendingDepth_528_);
lean_inc(v_defEqCtx_x3f_527_);
lean_inc_ref(v_localInstances_526_);
lean_inc_ref(v_lctx_525_);
lean_inc(v_zetaDeltaSet_524_);
v___x_538_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_zetaDeltaSet_524_);
lean_ctor_set(v___x_538_, 2, v_lctx_525_);
lean_ctor_set(v___x_538_, 3, v_localInstances_526_);
lean_ctor_set(v___x_538_, 4, v_defEqCtx_x3f_527_);
lean_ctor_set(v___x_538_, 5, v_synthPendingDepth_528_);
lean_ctor_set(v___x_538_, 6, v_customCanUnfoldPredicate_x3f_529_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7, v_trackZetaDelta_523_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 1, v_univApprox_530_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 2, v_inTypeClassResolution_531_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*7 + 3, v_cacheInferType_532_);
lean_inc_ref(v_rfl_492_);
lean_inc(v_a_497_);
lean_inc_ref(v_a_496_);
lean_inc(v_a_495_);
v___x_539_ = lean_apply_5(v_rfl_492_, v___x_538_, v_a_495_, v_a_496_, v_a_497_, lean_box(0));
if (lean_obj_tag(v___x_539_) == 0)
{
lean_dec_ref(v_prove_493_);
lean_dec_ref(v_rfl_492_);
return v___x_539_;
}
else
{
lean_object* v_a_540_; uint8_t v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
v___x_541_ = l_Lean_Exception_isInterrupt(v_a_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Exception_isRuntime(v_a_540_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref_known(v___x_539_, 1);
v___x_543_ = l_Lean_Meta_saveState___redArg(v_a_495_, v_a_497_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
lean_inc(v_a_497_);
lean_inc_ref(v_a_496_);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
v___x_545_ = lean_apply_5(v_prove_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, lean_box(0));
if (lean_obj_tag(v___x_545_) == 0)
{
lean_dec(v_a_544_);
lean_dec_ref(v_rfl_492_);
return v___x_545_;
}
else
{
lean_object* v_a_546_; uint8_t v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
v___x_547_ = l_Lean_Exception_isInterrupt(v_a_546_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; 
lean_inc(v_a_546_);
v___x_548_ = l_Lean_Exception_isRuntime(v_a_546_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec_ref_known(v___x_545_, 1);
v___x_549_ = l_Lean_Meta_SavedState_restore___redArg(v_a_544_, v_a_495_, v_a_497_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_549_, 1);
lean_inc(v_a_497_);
lean_inc_ref(v_a_496_);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
v___x_550_ = lean_apply_5(v_rfl_492_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, lean_box(0));
if (lean_obj_tag(v___x_550_) == 0)
{
lean_dec(v_a_546_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; uint8_t v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
v___x_552_ = l_Lean_Exception_isInterrupt(v_a_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Exception_isRuntime(v_a_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v___x_550_, 0);
lean_dec(v_unused_561_);
v___x_555_ = v___x_550_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_dec(v___x_550_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_a_546_);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_546_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_dec(v_a_546_);
return v___x_550_;
}
}
else
{
lean_dec(v_a_551_);
lean_dec(v_a_546_);
return v___x_550_;
}
}
}
else
{
lean_dec(v_a_546_);
lean_dec_ref(v_rfl_492_);
return v___x_549_;
}
}
else
{
lean_dec(v_a_546_);
lean_dec(v_a_544_);
lean_dec_ref(v_rfl_492_);
return v___x_545_;
}
}
else
{
lean_dec(v_a_546_);
lean_dec(v_a_544_);
lean_dec_ref(v_rfl_492_);
return v___x_545_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_prove_493_);
lean_dec_ref(v_rfl_492_);
v_a_562_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_543_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_543_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_dec_ref(v_prove_493_);
lean_dec_ref(v_rfl_492_);
return v___x_539_;
}
}
else
{
lean_dec(v_a_540_);
lean_dec_ref(v_prove_493_);
lean_dec_ref(v_rfl_492_);
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reflOrProve___boxed(lean_object* v_rfl_572_, lean_object* v_prove_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_reflOrProve(v_rfl_572_, v_prove_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_saveState___redArg(v___y_582_, v___y_584_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
v___x_588_ = lean_apply_5(v_x_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, lean_box(0));
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_587_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_a_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_628_; 
v_a_598_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_628_ == 0)
{
v___x_600_ = v___x_588_;
v_isShared_601_ = v_isSharedCheck_628_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_628_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_Exception_isInterrupt(v_a_598_);
if (v___x_602_ == 0)
{
uint8_t v___x_603_; 
lean_inc(v_a_598_);
v___x_603_ = l_Lean_Exception_isRuntime(v_a_598_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
v___x_604_ = l_Lean_Meta_SavedState_restore___redArg(v_a_587_, v___y_582_, v___y_584_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_613_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_a_587_);
if (v_isShared_601_ == 0)
{
v___x_623_ = v___x_600_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_598_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v___x_626_; 
lean_dec(v_a_587_);
if (v_isShared_601_ == 0)
{
v___x_626_ = v___x_600_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_598_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_x_580_);
v_a_629_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_586_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_586_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(lean_object* v_00_u03b1_644_, lean_object* v_x_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(lean_object* v_00_u03b1_652_, lean_object* v_x_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(v_00_u03b1_652_, v_x_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object* v_mvarId_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_mkFreshLevelMVar(v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__1));
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v_a_674_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_mkConst(v___x_675_, v___x_677_);
v___x_679_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_680_ = lean_box(0);
v___x_681_ = l_Lean_MVarId_apply(v_mvarId_667_, v___x_678_, v___x_679_, v___x_680_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v___x_681_;
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_mvarId_667_);
v_a_682_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object* v_mvarId_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_MVarId_heqOfEq___lam__0(v_mvarId_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object* v___f_697_, lean_object* v_mvarId_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_697_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_724_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_709_; 
v_val_709_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_a_705_, 1);
if (lean_obj_tag(v_val_709_) == 1)
{
lean_object* v_tail_710_; 
v_tail_710_ = lean_ctor_get(v_val_709_, 1);
if (lean_obj_tag(v_tail_710_) == 0)
{
lean_object* v_head_711_; lean_object* v___x_713_; 
lean_dec(v_mvarId_698_);
v_head_711_ = lean_ctor_get(v_val_709_, 0);
lean_inc(v_head_711_);
lean_dec_ref_known(v_val_709_, 2);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_head_711_);
v___x_713_ = v___x_707_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_head_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_716_; 
lean_dec_ref_known(v_val_709_, 2);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_mvarId_698_);
v___x_716_ = v___x_707_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_mvarId_698_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v___x_719_; 
lean_dec(v_val_709_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_mvarId_698_);
v___x_719_ = v___x_707_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_mvarId_698_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v_a_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_mvarId_698_);
v___x_722_ = v___x_707_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_mvarId_698_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_mvarId_698_);
v_a_725_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_704_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_704_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1___boxed(lean_object* v___f_733_, lean_object* v_mvarId_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_MVarId_heqOfEq___lam__1(v___f_733_, v_mvarId_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object* v_mvarId_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___x_749_; 
lean_inc_n(v_mvarId_741_, 2);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_747_, 0, v_mvarId_741_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_748_, 0, v___f_747_);
lean_closure_set(v___f_748_, 1, v_mvarId_741_);
v___x_749_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_741_, v___f_748_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object* v_mvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_MVarId_heqOfEq(v_mvarId_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object* v_mvarId_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_mkFreshLevelMVar(v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = ((lean_object*)(l_Lean_MVarId_eqOfHEq___lam__0___closed__1));
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v_a_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l_Lean_mkConst(v___x_768_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_MVarId_apply(v_mvarId_760_, v___x_771_, v___x_772_, v___x_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v___x_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_mvarId_760_);
v_a_775_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_766_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_766_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object* v_mvarId_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_MVarId_eqOfHEq___lam__0(v_mvarId_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object* v_mvarId_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; 
lean_inc_n(v_mvarId_790_, 2);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_796_, 0, v_mvarId_790_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_797_, 0, v___f_796_);
lean_closure_set(v___f_797_, 1, v_mvarId_790_);
v___x_798_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_790_, v___f_797_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object* v_mvarId_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_MVarId_eqOfHEq(v_mvarId_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object* v_mvarId_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_mkFreshLevelMVar(v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__0___closed__1));
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_817_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_mkConst(v___x_818_, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_823_ = lean_box(0);
v___x_824_ = l_Lean_MVarId_apply(v_mvarId_810_, v___x_821_, v___x_822_, v___x_823_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_824_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_mvarId_810_);
v_a_825_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_816_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_816_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object* v_mvarId_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_MVarId_hrefl___lam__0(v_mvarId_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object* v_mvarId_843_, lean_object* v___f_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
if (lean_obj_tag(v_a_855_) == 1)
{
lean_object* v_val_859_; 
v_val_859_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_a_855_, 1);
if (lean_obj_tag(v_val_859_) == 0)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_mvarId_843_);
v___x_860_ = lean_box(0);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_dec(v_val_859_);
lean_del_object(v___x_857_);
goto v___jp_850_;
}
}
else
{
lean_del_object(v___x_857_);
lean_dec(v_a_855_);
goto v___jp_850_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_mvarId_843_);
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
v___jp_850_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__1___closed__1));
v___x_852_ = lean_box(0);
v___x_853_ = l_Lean_Meta_throwTacticEx___redArg(v___x_851_, v_mvarId_843_, v___x_852_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1___boxed(lean_object* v_mvarId_873_, lean_object* v___f_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_MVarId_hrefl___lam__1(v_mvarId_873_, v___f_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object* v_mvarId_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
lean_inc_n(v_mvarId_881_, 2);
v___f_887_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_887_, 0, v_mvarId_881_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_888_, 0, v_mvarId_881_);
lean_closure_set(v___f_888_, 1, v___f_887_);
v___x_889_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_881_, v___f_888_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object* v_mvarId_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_MVarId_hrefl(v_mvarId_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_896_;
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
