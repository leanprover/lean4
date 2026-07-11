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
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(lean_object* v_mvarId_45_, lean_object* v_x_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_45_, v_x_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_52_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_52_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg___boxed(lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(lean_object* v_00_u03b1_77_, lean_object* v_mvarId_78_, lean_object* v_x_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_78_, v_x_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___boxed(lean_object* v_00_u03b1_86_, lean_object* v_mvarId_87_, lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2(v_00_u03b1_86_, v_mvarId_87_, v_x_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_ks_99_; lean_object* v_vs_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_124_; 
v_ks_99_ = lean_ctor_get(v_x_95_, 0);
v_vs_100_ = lean_ctor_get(v_x_95_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_95_);
if (v_isSharedCheck_124_ == 0)
{
v___x_102_ = v_x_95_;
v_isShared_103_ = v_isSharedCheck_124_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_vs_100_);
lean_inc(v_ks_99_);
lean_dec(v_x_95_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_124_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_get_size(v_ks_99_);
v___x_105_ = lean_nat_dec_lt(v_x_96_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_x_96_);
v___x_106_ = lean_array_push(v_ks_99_, v_x_97_);
v___x_107_ = lean_array_push(v_vs_100_, v_x_98_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_107_);
lean_ctor_set(v___x_102_, 0, v___x_106_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v_k_x27_111_; uint8_t v___x_112_; 
v_k_x27_111_ = lean_array_fget_borrowed(v_ks_99_, v_x_96_);
v___x_112_ = l_Lean_instBEqMVarId_beq(v_x_97_, v_k_x27_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_114_; 
if (v_isShared_103_ == 0)
{
v___x_114_ = v___x_102_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_ks_99_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_vs_100_);
v___x_114_ = v_reuseFailAlloc_118_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_x_96_, v___x_115_);
lean_dec(v_x_96_);
v_x_95_ = v___x_114_;
v_x_96_ = v___x_116_;
goto _start;
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_119_ = lean_array_fset(v_ks_99_, v_x_96_, v_x_97_);
v___x_120_ = lean_array_fset(v_vs_100_, v_x_96_, v_x_98_);
lean_dec(v_x_96_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_120_);
lean_ctor_set(v___x_102_, 0, v___x_119_);
v___x_122_ = v___x_102_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_125_, lean_object* v_k_126_, lean_object* v_v_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_125_, v___x_128_, v_k_126_, v_v_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(lean_object* v_x_131_, size_t v_x_132_, size_t v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v_es_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v_j_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_es_136_ = lean_ctor_get(v_x_131_, 0);
v___x_137_ = ((size_t)31ULL);
v___x_138_ = lean_usize_land(v_x_132_, v___x_137_);
v_j_139_ = lean_usize_to_nat(v___x_138_);
v___x_140_ = lean_array_get_size(v_es_136_);
v___x_141_ = lean_nat_dec_lt(v_j_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v_j_139_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
return v_x_131_;
}
else
{
lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_180_; 
lean_inc_ref(v_es_136_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v_x_131_, 0);
lean_dec(v_unused_181_);
v___x_143_ = v_x_131_;
v_isShared_144_ = v_isSharedCheck_180_;
goto v_resetjp_142_;
}
else
{
lean_dec(v_x_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_180_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_v_145_; lean_object* v___x_146_; lean_object* v_xs_x27_147_; lean_object* v___y_149_; 
v_v_145_ = lean_array_fget(v_es_136_, v_j_139_);
v___x_146_ = lean_box(0);
v_xs_x27_147_ = lean_array_fset(v_es_136_, v_j_139_, v___x_146_);
switch(lean_obj_tag(v_v_145_))
{
case 0:
{
lean_object* v_key_154_; lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_165_; 
v_key_154_ = lean_ctor_get(v_v_145_, 0);
v_val_155_ = lean_ctor_get(v_v_145_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_v_145_);
if (v_isSharedCheck_165_ == 0)
{
v___x_157_ = v_v_145_;
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_inc(v_key_154_);
lean_dec(v_v_145_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_instBEqMVarId_beq(v_x_134_, v_key_154_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_del_object(v___x_157_);
v___x_160_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_154_, v_val_155_, v_x_134_, v_x_135_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
v___y_149_ = v___x_161_;
goto v___jp_148_;
}
else
{
lean_object* v___x_163_; 
lean_dec(v_val_155_);
lean_dec(v_key_154_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v_x_135_);
lean_ctor_set(v___x_157_, 0, v_x_134_);
v___x_163_ = v___x_157_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_x_134_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_x_135_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
v___y_149_ = v___x_163_;
goto v___jp_148_;
}
}
}
}
case 1:
{
lean_object* v_node_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_178_; 
v_node_166_ = lean_ctor_get(v_v_145_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_v_145_);
if (v_isSharedCheck_178_ == 0)
{
v___x_168_ = v_v_145_;
v_isShared_169_ = v_isSharedCheck_178_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_node_166_);
lean_dec(v_v_145_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_178_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_usize_shift_right(v_x_132_, v___x_170_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_add(v_x_133_, v___x_172_);
v___x_174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_node_166_, v___x_171_, v___x_173_, v_x_134_, v_x_135_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_174_);
v___x_176_ = v___x_168_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
v___y_149_ = v___x_176_;
goto v___jp_148_;
}
}
}
default: 
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_x_134_);
lean_ctor_set(v___x_179_, 1, v_x_135_);
v___y_149_ = v___x_179_;
goto v___jp_148_;
}
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_array_fset(v_xs_x27_147_, v_j_139_, v___y_149_);
lean_dec(v_j_139_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_150_);
v___x_152_ = v___x_143_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
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
else
{
lean_object* v_ks_182_; lean_object* v_vs_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_203_; 
v_ks_182_ = lean_ctor_get(v_x_131_, 0);
v_vs_183_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_203_ == 0)
{
v___x_185_ = v_x_131_;
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_vs_183_);
lean_inc(v_ks_182_);
lean_dec(v_x_131_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_ks_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_vs_183_);
v___x_188_ = v_reuseFailAlloc_202_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v_newNode_189_; uint8_t v___y_191_; size_t v___x_197_; uint8_t v___x_198_; 
v_newNode_189_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_188_, v_x_134_, v_x_135_);
v___x_197_ = ((size_t)7ULL);
v___x_198_ = lean_usize_dec_le(v___x_197_, v_x_133_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_189_);
v___x_200_ = lean_unsigned_to_nat(4u);
v___x_201_ = lean_nat_dec_lt(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___y_191_ = v___x_201_;
goto v___jp_190_;
}
else
{
v___y_191_ = v___x_198_;
goto v___jp_190_;
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
lean_object* v_ks_192_; lean_object* v_vs_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_ks_192_ = lean_ctor_get(v_newNode_189_, 0);
lean_inc_ref(v_ks_192_);
v_vs_193_ = lean_ctor_get(v_newNode_189_, 1);
lean_inc_ref(v_vs_193_);
lean_dec_ref(v_newNode_189_);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_196_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_133_, v_ks_192_, v_vs_193_, v___x_194_, v___x_195_);
lean_dec_ref(v_vs_193_);
lean_dec_ref(v_ks_192_);
return v___x_196_;
}
else
{
return v_newNode_189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_204_, lean_object* v_keys_205_, lean_object* v_vals_206_, lean_object* v_i_207_, lean_object* v_entries_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_array_get_size(v_keys_205_);
v___x_210_ = lean_nat_dec_lt(v_i_207_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v_i_207_);
return v_entries_208_;
}
else
{
lean_object* v_k_211_; lean_object* v_v_212_; uint64_t v___x_213_; size_t v_h_214_; size_t v___x_215_; lean_object* v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v_h_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_k_211_ = lean_array_fget_borrowed(v_keys_205_, v_i_207_);
v_v_212_ = lean_array_fget_borrowed(v_vals_206_, v_i_207_);
v___x_213_ = l_Lean_instHashableMVarId_hash(v_k_211_);
v_h_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = ((size_t)5ULL);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v_depth_204_, v___x_217_);
v___x_219_ = lean_usize_mul(v___x_215_, v___x_218_);
v_h_220_ = lean_usize_shift_right(v_h_214_, v___x_219_);
v___x_221_ = lean_nat_add(v_i_207_, v___x_216_);
lean_dec(v_i_207_);
lean_inc(v_v_212_);
lean_inc(v_k_211_);
v___x_222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_entries_208_, v_h_220_, v_depth_204_, v_k_211_, v_v_212_);
v_i_207_ = v___x_221_;
v_entries_208_ = v___x_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_224_, lean_object* v_keys_225_, lean_object* v_vals_226_, lean_object* v_i_227_, lean_object* v_entries_228_){
_start:
{
size_t v_depth_boxed_229_; lean_object* v_res_230_; 
v_depth_boxed_229_ = lean_unbox_usize(v_depth_224_);
lean_dec(v_depth_224_);
v_res_230_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_229_, v_keys_225_, v_vals_226_, v_i_227_, v_entries_228_);
lean_dec_ref(v_vals_226_);
lean_dec_ref(v_keys_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
size_t v_x_2574__boxed_236_; size_t v_x_2575__boxed_237_; lean_object* v_res_238_; 
v_x_2574__boxed_236_ = lean_unbox_usize(v_x_232_);
lean_dec(v_x_232_);
v_x_2575__boxed_237_ = lean_unbox_usize(v_x_233_);
lean_dec(v_x_233_);
v_res_238_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_231_, v_x_2574__boxed_236_, v_x_2575__boxed_237_, v_x_234_, v_x_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint64_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v___x_242_ = l_Lean_instHashableMVarId_hash(v_x_240_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_239_, v___x_243_, v___x_244_, v_x_240_, v_x_241_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; lean_object* v_mctx_251_; lean_object* v_cache_252_; lean_object* v_zetaDeltaFVarIds_253_; lean_object* v_postponed_254_; lean_object* v_diag_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_283_; 
v___x_250_ = lean_st_ref_take(v___y_248_);
v_mctx_251_ = lean_ctor_get(v___x_250_, 0);
v_cache_252_ = lean_ctor_get(v___x_250_, 1);
v_zetaDeltaFVarIds_253_ = lean_ctor_get(v___x_250_, 2);
v_postponed_254_ = lean_ctor_get(v___x_250_, 3);
v_diag_255_ = lean_ctor_get(v___x_250_, 4);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_283_ == 0)
{
v___x_257_ = v___x_250_;
v_isShared_258_ = v_isSharedCheck_283_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_diag_255_);
lean_inc(v_postponed_254_);
lean_inc(v_zetaDeltaFVarIds_253_);
lean_inc(v_cache_252_);
lean_inc(v_mctx_251_);
lean_dec(v___x_250_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_283_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_depth_259_; lean_object* v_levelAssignDepth_260_; lean_object* v_lmvarCounter_261_; lean_object* v_mvarCounter_262_; lean_object* v_lDecls_263_; lean_object* v_decls_264_; lean_object* v_userNames_265_; lean_object* v_lAssignment_266_; lean_object* v_eAssignment_267_; lean_object* v_dAssignment_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_282_; 
v_depth_259_ = lean_ctor_get(v_mctx_251_, 0);
v_levelAssignDepth_260_ = lean_ctor_get(v_mctx_251_, 1);
v_lmvarCounter_261_ = lean_ctor_get(v_mctx_251_, 2);
v_mvarCounter_262_ = lean_ctor_get(v_mctx_251_, 3);
v_lDecls_263_ = lean_ctor_get(v_mctx_251_, 4);
v_decls_264_ = lean_ctor_get(v_mctx_251_, 5);
v_userNames_265_ = lean_ctor_get(v_mctx_251_, 6);
v_lAssignment_266_ = lean_ctor_get(v_mctx_251_, 7);
v_eAssignment_267_ = lean_ctor_get(v_mctx_251_, 8);
v_dAssignment_268_ = lean_ctor_get(v_mctx_251_, 9);
v_isSharedCheck_282_ = !lean_is_exclusive(v_mctx_251_);
if (v_isSharedCheck_282_ == 0)
{
v___x_270_ = v_mctx_251_;
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_dAssignment_268_);
lean_inc(v_eAssignment_267_);
lean_inc(v_lAssignment_266_);
lean_inc(v_userNames_265_);
lean_inc(v_decls_264_);
lean_inc(v_lDecls_263_);
lean_inc(v_mvarCounter_262_);
lean_inc(v_lmvarCounter_261_);
lean_inc(v_levelAssignDepth_260_);
lean_inc(v_depth_259_);
lean_dec(v_mctx_251_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_eAssignment_267_, v_mvarId_246_, v_val_247_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 8, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_depth_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_levelAssignDepth_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_lmvarCounter_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_mvarCounter_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_lDecls_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_decls_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_userNames_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_lAssignment_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_dAssignment_268_);
v___x_274_ = v_reuseFailAlloc_281_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_274_);
v___x_276_ = v___x_257_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_cache_252_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_zetaDeltaFVarIds_253_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_postponed_254_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_diag_255_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_st_ref_set(v___y_248_, v___x_276_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(lean_object* v_mvarId_284_, lean_object* v_val_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_284_, v_val_285_, v___y_286_);
lean_dec(v___y_286_);
return v_res_288_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__3));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__6(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__5));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__9(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__8));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object* v_mvarId_304_, lean_object* v___x_305_, lean_object* v___x_306_, uint8_t v_check_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
lean_inc(v_mvarId_304_);
v___x_313_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_304_, v___x_305_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_393_; 
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_394_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_393_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_393_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; 
lean_inc(v_mvarId_304_);
v___x_317_ = l_Lean_MVarId_getType_x27(v_mvarId_304_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___x_374_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__7));
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = l_Lean_Expr_isAppOfArity(v_a_318_, v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_377_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_378_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__9, &l_Lean_MVarId_refl___lam__0___closed__9_once, _init_l_Lean_MVarId_refl___lam__0___closed__9);
lean_inc(v_a_318_);
v___x_379_ = l_Lean_indentExpr(v_a_318_);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 0, v___x_380_);
v___x_382_ = v___x_315_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
lean_inc(v_mvarId_304_);
v___x_383_ = l_Lean_Meta_throwTacticEx___redArg(v___x_377_, v_mvarId_304_, v___x_382_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_dec_ref_known(v___x_383_, 1);
v___y_336_ = v___y_308_;
v___y_337_ = v___y_309_;
v___y_338_ = v___y_310_;
v___y_339_ = v___y_311_;
goto v___jp_335_;
}
else
{
lean_dec(v_a_318_);
lean_dec_ref(v___x_306_);
lean_dec(v_mvarId_304_);
return v___x_383_;
}
}
}
else
{
lean_del_object(v___x_315_);
v___y_336_ = v___y_308_;
v___y_337_ = v___y_309_;
v___y_338_ = v___y_310_;
v___y_339_ = v___y_311_;
goto v___jp_335_;
}
v___jp_319_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_326_ = l_Lean_Expr_getAppFn(v_a_318_);
lean_dec(v_a_318_);
v___x_327_ = l_Lean_Expr_constLevels_x21(v___x_326_);
lean_dec_ref(v___x_326_);
v___x_328_ = l_Lean_Expr_appFn_x21(v___y_320_);
lean_dec_ref(v___y_320_);
v___x_329_ = l_Lean_Expr_appArg_x21(v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__0));
v___x_331_ = l_Lean_Name_mkStr2(v___x_330_, v___x_306_);
v___x_332_ = l_Lean_mkConst(v___x_331_, v___x_327_);
v___x_333_ = l_Lean_mkAppB(v___x_332_, v___x_329_, v___y_321_);
v___x_334_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_304_, v___x_333_, v___y_323_);
return v___x_334_;
}
v___jp_335_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_340_ = l_Lean_Expr_appFn_x21(v_a_318_);
v___x_341_ = l_Lean_Expr_appArg_x21(v___x_340_);
v___x_342_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_341_, v___y_337_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref(v___x_342_);
v___x_344_ = l_Lean_Expr_appArg_x21(v_a_318_);
v___x_345_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_344_, v___y_337_);
if (v_check_307_ == 0)
{
lean_dec_ref(v___x_345_);
v___y_320_ = v___x_340_;
v___y_321_ = v_a_343_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
v___y_324_ = v___y_338_;
v___y_325_ = v___y_339_;
goto v___jp_319_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_373_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_373_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_373_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_373_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; 
lean_inc(v_a_346_);
lean_inc(v_a_343_);
v___x_350_ = l_Lean_Meta_isExprDefEq(v_a_343_, v_a_346_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; uint8_t v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_353_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_354_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__4, &l_Lean_MVarId_refl___lam__0___closed__4_once, _init_l_Lean_MVarId_refl___lam__0___closed__4);
lean_inc(v_a_343_);
v___x_355_ = l_Lean_indentExpr(v_a_343_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__6, &l_Lean_MVarId_refl___lam__0___closed__6_once, _init_l_Lean_MVarId_refl___lam__0___closed__6);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_indentExpr(v_a_346_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 1);
lean_ctor_set(v___x_348_, 0, v___x_360_);
v___x_362_ = v___x_348_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
lean_inc(v_mvarId_304_);
v___x_363_ = l_Lean_Meta_throwTacticEx___redArg(v___x_353_, v_mvarId_304_, v___x_362_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_dec_ref_known(v___x_363_, 1);
v___y_320_ = v___x_340_;
v___y_321_ = v_a_343_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
v___y_324_ = v___y_338_;
v___y_325_ = v___y_339_;
goto v___jp_319_;
}
else
{
lean_dec(v_a_343_);
lean_dec_ref(v___x_340_);
lean_dec(v_a_318_);
lean_dec_ref(v___x_306_);
lean_dec(v_mvarId_304_);
return v___x_363_;
}
}
}
else
{
lean_del_object(v___x_348_);
lean_dec(v_a_346_);
v___y_320_ = v___x_340_;
v___y_321_ = v_a_343_;
v___y_322_ = v___y_336_;
v___y_323_ = v___y_337_;
v___y_324_ = v___y_338_;
v___y_325_ = v___y_339_;
goto v___jp_319_;
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_del_object(v___x_348_);
lean_dec(v_a_346_);
lean_dec(v_a_343_);
lean_dec_ref(v___x_340_);
lean_dec(v_a_318_);
lean_dec_ref(v___x_306_);
lean_dec(v_mvarId_304_);
v_a_365_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_350_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_350_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_del_object(v___x_315_);
lean_dec_ref(v___x_306_);
lean_dec(v_mvarId_304_);
v_a_385_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_317_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_317_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_306_);
lean_dec(v_mvarId_304_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0___boxed(lean_object* v_mvarId_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v_check_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v_check_boxed_404_; lean_object* v_res_405_; 
v_check_boxed_404_ = lean_unbox(v_check_398_);
v_res_405_ = l_Lean_MVarId_refl___lam__0(v_mvarId_395_, v___x_396_, v___x_397_, v_check_boxed_404_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object* v_mvarId_409_, uint8_t v_check_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
v___x_416_ = ((lean_object*)(l_Lean_MVarId_refl___closed__0));
v___x_417_ = ((lean_object*)(l_Lean_MVarId_refl___closed__1));
v___x_418_ = lean_box(v_check_410_);
lean_inc(v_mvarId_409_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_419_, 0, v_mvarId_409_);
lean_closure_set(v___f_419_, 1, v___x_417_);
lean_closure_set(v___f_419_, 2, v___x_416_);
lean_closure_set(v___f_419_, 3, v___x_418_);
v___x_420_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_409_, v___f_419_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object* v_mvarId_421_, lean_object* v_check_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
uint8_t v_check_boxed_428_; lean_object* v_res_429_; 
v_check_boxed_428_ = lean_unbox(v_check_422_);
v_res_429_ = l_Lean_MVarId_refl(v_mvarId_421_, v_check_boxed_428_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(lean_object* v_mvarId_430_, lean_object* v_val_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_430_, v_val_431_, v___y_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(lean_object* v_mvarId_438_, lean_object* v_val_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(v_mvarId_438_, v_val_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_x_447_, v_x_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, size_t v_x_453_, size_t v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_452_, v_x_453_, v_x_454_, v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
size_t v_x_3077__boxed_464_; size_t v_x_3078__boxed_465_; lean_object* v_res_466_; 
v_x_3077__boxed_464_ = lean_unbox_usize(v_x_460_);
lean_dec(v_x_460_);
v_x_3078__boxed_465_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_res_466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(v_00_u03b2_458_, v_x_459_, v_x_3077__boxed_464_, v_x_3078__boxed_465_, v_x_462_, v_x_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_467_, lean_object* v_n_468_, lean_object* v_k_469_, lean_object* v_v_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_468_, v_k_469_, v_v_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_472_, size_t v_depth_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_entries_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_473_, v_keys_474_, v_vals_475_, v_i_477_, v_entries_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_480_, lean_object* v_depth_481_, lean_object* v_keys_482_, lean_object* v_vals_483_, lean_object* v_heq_484_, lean_object* v_i_485_, lean_object* v_entries_486_){
_start:
{
size_t v_depth_boxed_487_; lean_object* v_res_488_; 
v_depth_boxed_487_ = lean_unbox_usize(v_depth_481_);
lean_dec(v_depth_481_);
v_res_488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_480_, v_depth_boxed_487_, v_keys_482_, v_vals_483_, v_heq_484_, v_i_485_, v_entries_486_);
lean_dec_ref(v_vals_483_);
lean_dec_ref(v_keys_482_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_490_, v_x_491_, v_x_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_saveState___redArg(v___y_497_, v___y_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
v___x_503_ = lean_apply_5(v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, lean_box(0));
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_502_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_542_; 
v_a_513_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_542_ == 0)
{
v___x_515_ = v___x_503_;
v_isShared_516_ = v_isSharedCheck_542_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_542_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
uint8_t v___y_518_; uint8_t v___x_540_; 
v___x_540_ = l_Lean_Exception_isInterrupt(v_a_513_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
lean_inc(v_a_513_);
v___x_541_ = l_Lean_Exception_isRuntime(v_a_513_);
v___y_518_ = v___x_541_;
goto v___jp_517_;
}
else
{
v___y_518_ = v___x_540_;
goto v___jp_517_;
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; 
lean_del_object(v___x_515_);
lean_dec(v_a_513_);
v___x_519_ = l_Lean_Meta_SavedState_restore___redArg(v_a_502_, v___y_497_, v___y_499_);
lean_dec(v_a_502_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_528_);
v___x_521_ = v___x_519_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_519_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_519_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_519_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_538_; 
lean_dec(v_a_502_);
if (v_isShared_516_ == 0)
{
v___x_538_ = v___x_515_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_513_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v_x_495_);
v_a_543_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_501_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_501_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(lean_object* v_00_u03b1_558_, lean_object* v_x_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(lean_object* v_00_u03b1_566_, lean_object* v_x_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(v_00_u03b1_566_, v_x_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object* v_mvarId_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_mkFreshLevelMVar(v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__1));
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_mkConst(v___x_589_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_594_ = lean_box(0);
v___x_595_ = l_Lean_MVarId_apply(v_mvarId_581_, v___x_592_, v___x_593_, v___x_594_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_mvarId_581_);
v_a_596_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object* v_mvarId_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_MVarId_heqOfEq___lam__0(v_mvarId_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object* v___f_611_, lean_object* v_mvarId_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_611_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_638_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_638_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_638_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_638_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
if (lean_obj_tag(v_a_619_) == 1)
{
lean_object* v_val_623_; 
v_val_623_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v_a_619_, 1);
if (lean_obj_tag(v_val_623_) == 1)
{
lean_object* v_tail_624_; 
v_tail_624_ = lean_ctor_get(v_val_623_, 1);
if (lean_obj_tag(v_tail_624_) == 0)
{
lean_object* v_head_625_; lean_object* v___x_627_; 
lean_dec(v_mvarId_612_);
v_head_625_ = lean_ctor_get(v_val_623_, 0);
lean_inc(v_head_625_);
lean_dec_ref_known(v_val_623_, 2);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_head_625_);
v___x_627_ = v___x_621_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_head_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref_known(v_val_623_, 2);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_mvarId_612_);
v___x_630_ = v___x_621_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_mvarId_612_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_val_623_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_mvarId_612_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_mvarId_612_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_a_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_mvarId_612_);
v___x_636_ = v___x_621_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_mvarId_612_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_mvarId_612_);
v_a_639_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_618_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1___boxed(lean_object* v___f_647_, lean_object* v_mvarId_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_MVarId_heqOfEq___lam__1(v___f_647_, v_mvarId_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object* v_mvarId_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_663_; 
lean_inc_n(v_mvarId_655_, 2);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_661_, 0, v_mvarId_655_);
v___f_662_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_662_, 0, v___f_661_);
lean_closure_set(v___f_662_, 1, v_mvarId_655_);
v___x_663_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_655_, v___f_662_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object* v_mvarId_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_MVarId_heqOfEq(v_mvarId_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object* v_mvarId_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_mkFreshLevelMVar(v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = ((lean_object*)(l_Lean_MVarId_eqOfHEq___lam__0___closed__1));
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v_a_681_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_mkConst(v___x_682_, v___x_684_);
v___x_686_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_MVarId_apply(v_mvarId_674_, v___x_685_, v___x_686_, v___x_687_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_688_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_mvarId_674_);
v_a_689_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object* v_mvarId_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_MVarId_eqOfHEq___lam__0(v_mvarId_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1(lean_object* v___f_704_, lean_object* v_mvarId_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_704_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
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
if (lean_obj_tag(v_a_712_) == 1)
{
lean_object* v_val_716_; 
v_val_716_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_val_716_);
lean_dec_ref_known(v_a_712_, 1);
if (lean_obj_tag(v_val_716_) == 1)
{
lean_object* v_tail_717_; 
v_tail_717_ = lean_ctor_get(v_val_716_, 1);
if (lean_obj_tag(v_tail_717_) == 0)
{
lean_object* v_head_718_; lean_object* v___x_720_; 
lean_dec(v_mvarId_705_);
v_head_718_ = lean_ctor_get(v_val_716_, 0);
lean_inc(v_head_718_);
lean_dec_ref_known(v_val_716_, 2);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_head_718_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_head_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec_ref_known(v_val_716_, 2);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_mvarId_705_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_mvarId_705_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v_val_716_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_mvarId_705_);
v___x_726_ = v___x_714_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_mvarId_705_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v___x_729_; 
lean_dec(v_a_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_mvarId_705_);
v___x_729_ = v___x_714_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_mvarId_705_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_mvarId_705_);
v_a_732_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_711_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_711_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1___boxed(lean_object* v___f_740_, lean_object* v_mvarId_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_MVarId_eqOfHEq___lam__1(v___f_740_, v_mvarId_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object* v_mvarId_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
lean_inc_n(v_mvarId_748_, 2);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_754_, 0, v_mvarId_748_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_755_, 0, v___f_754_);
lean_closure_set(v___f_755_, 1, v_mvarId_748_);
v___x_756_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_748_, v___f_755_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object* v_mvarId_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_MVarId_eqOfHEq(v_mvarId_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object* v_mvarId_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_mkFreshLevelMVar(v___y_769_, v___y_770_, v___y_771_, v___y_772_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__0___closed__1));
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v_a_775_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_mkConst(v___x_776_, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_781_ = lean_box(0);
v___x_782_ = l_Lean_MVarId_apply(v_mvarId_768_, v___x_779_, v___x_780_, v___x_781_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_mvarId_768_);
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object* v_mvarId_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_MVarId_hrefl___lam__0(v_mvarId_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object* v___f_801_, lean_object* v_mvarId_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_801_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
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
lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; 
if (lean_obj_tag(v_a_809_) == 1)
{
lean_object* v_val_821_; 
v_val_821_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_a_809_, 1);
if (lean_obj_tag(v_val_821_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_mvarId_802_);
v___x_822_ = lean_box(0);
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
else
{
lean_dec(v_val_821_);
lean_del_object(v___x_811_);
v___y_814_ = v___y_803_;
v___y_815_ = v___y_804_;
v___y_816_ = v___y_805_;
v___y_817_ = v___y_806_;
goto v___jp_813_;
}
}
else
{
lean_del_object(v___x_811_);
lean_dec(v_a_809_);
v___y_814_ = v___y_803_;
v___y_815_ = v___y_804_;
v___y_816_ = v___y_805_;
v___y_817_ = v___y_806_;
goto v___jp_813_;
}
v___jp_813_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__1___closed__1));
v___x_819_ = lean_box(0);
v___x_820_ = l_Lean_Meta_throwTacticEx___redArg(v___x_818_, v_mvarId_802_, v___x_819_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_820_;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_mvarId_802_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1___boxed(lean_object* v___f_835_, lean_object* v_mvarId_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_MVarId_hrefl___lam__1(v___f_835_, v_mvarId_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object* v_mvarId_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; 
lean_inc_n(v_mvarId_843_, 2);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_849_, 0, v_mvarId_843_);
v___f_850_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_850_, 0, v___f_849_);
lean_closure_set(v___f_850_, 1, v_mvarId_843_);
v___x_851_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_843_, v___f_850_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object* v_mvarId_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_MVarId_hrefl(v_mvarId_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_858_;
}
}
lean_object* runtime_initialize_Lean_Meta_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
