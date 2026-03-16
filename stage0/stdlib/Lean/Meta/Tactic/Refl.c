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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2;
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; 
v___x_129_ = ((size_t)5ULL);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_shift_left(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; 
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_134_ = lean_usize_sub(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(lean_object* v_x_136_, size_t v_x_137_, size_t v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_es_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_j_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_es_141_ = lean_ctor_get(v_x_136_, 0);
v___x_142_ = ((size_t)5ULL);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_145_ = lean_usize_land(v_x_137_, v___x_144_);
v_j_146_ = lean_usize_to_nat(v___x_145_);
v___x_147_ = lean_array_get_size(v_es_141_);
v___x_148_ = lean_nat_dec_lt(v_j_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_j_146_);
lean_dec(v_x_140_);
lean_dec(v_x_139_);
return v_x_136_;
}
else
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_185_; 
lean_inc_ref(v_es_141_);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_x_136_, 0);
lean_dec(v_unused_186_);
v___x_150_ = v_x_136_;
v_isShared_151_ = v_isSharedCheck_185_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_x_136_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_185_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_v_152_; lean_object* v___x_153_; lean_object* v_xs_x27_154_; lean_object* v___y_156_; 
v_v_152_ = lean_array_fget(v_es_141_, v_j_146_);
v___x_153_ = lean_box(0);
v_xs_x27_154_ = lean_array_fset(v_es_141_, v_j_146_, v___x_153_);
switch(lean_obj_tag(v_v_152_))
{
case 0:
{
lean_object* v_key_161_; lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_key_161_ = lean_ctor_get(v_v_152_, 0);
v_val_162_ = lean_ctor_get(v_v_152_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v_v_152_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_inc(v_key_161_);
lean_dec(v_v_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_instBEqMVarId_beq(v_x_139_, v_key_161_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_del_object(v___x_164_);
v___x_167_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_161_, v_val_162_, v_x_139_, v_x_140_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___y_156_ = v___x_168_;
goto v___jp_155_;
}
else
{
lean_object* v___x_170_; 
lean_dec(v_val_162_);
lean_dec(v_key_161_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_x_140_);
lean_ctor_set(v___x_164_, 0, v_x_139_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_x_139_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_x_140_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
}
}
}
case 1:
{
lean_object* v_node_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v_node_173_ = lean_ctor_get(v_v_152_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_183_ == 0)
{
v___x_175_ = v_v_152_;
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_node_173_);
lean_dec(v_v_152_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_177_ = lean_usize_shift_right(v_x_137_, v___x_142_);
v___x_178_ = lean_usize_add(v_x_138_, v___x_143_);
v___x_179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_node_173_, v___x_177_, v___x_178_, v_x_139_, v_x_140_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_179_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v___y_156_ = v___x_181_;
goto v___jp_155_;
}
}
}
default: 
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_x_139_);
lean_ctor_set(v___x_184_, 1, v_x_140_);
v___y_156_ = v___x_184_;
goto v___jp_155_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_array_fset(v_xs_x27_154_, v_j_146_, v___y_156_);
lean_dec(v_j_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_157_);
v___x_159_ = v___x_150_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
else
{
lean_object* v_ks_187_; lean_object* v_vs_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_208_; 
v_ks_187_ = lean_ctor_get(v_x_136_, 0);
v_vs_188_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_208_ == 0)
{
v___x_190_ = v_x_136_;
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_vs_188_);
lean_inc(v_ks_187_);
lean_dec(v_x_136_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_ks_187_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_vs_188_);
v___x_193_ = v_reuseFailAlloc_207_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v_newNode_194_; uint8_t v___y_196_; size_t v___x_202_; uint8_t v___x_203_; 
v_newNode_194_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_193_, v_x_139_, v_x_140_);
v___x_202_ = ((size_t)7ULL);
v___x_203_ = lean_usize_dec_le(v___x_202_, v_x_138_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_194_);
v___x_205_ = lean_unsigned_to_nat(4u);
v___x_206_ = lean_nat_dec_lt(v___x_204_, v___x_205_);
lean_dec(v___x_204_);
v___y_196_ = v___x_206_;
goto v___jp_195_;
}
else
{
v___y_196_ = v___x_203_;
goto v___jp_195_;
}
v___jp_195_:
{
if (v___y_196_ == 0)
{
lean_object* v_ks_197_; lean_object* v_vs_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_ks_197_ = lean_ctor_get(v_newNode_194_, 0);
lean_inc_ref(v_ks_197_);
v_vs_198_ = lean_ctor_get(v_newNode_194_, 1);
lean_inc_ref(v_vs_198_);
lean_dec_ref(v_newNode_194_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_138_, v_ks_197_, v_vs_198_, v___x_199_, v___x_200_);
lean_dec_ref(v_vs_198_);
lean_dec_ref(v_ks_197_);
return v___x_201_;
}
else
{
return v_newNode_194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_209_, lean_object* v_keys_210_, lean_object* v_vals_211_, lean_object* v_i_212_, lean_object* v_entries_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_array_get_size(v_keys_210_);
v___x_215_ = lean_nat_dec_lt(v_i_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec(v_i_212_);
return v_entries_213_;
}
else
{
lean_object* v_k_216_; lean_object* v_v_217_; uint64_t v___x_218_; size_t v_h_219_; size_t v___x_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v_h_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_k_216_ = lean_array_fget_borrowed(v_keys_210_, v_i_212_);
v_v_217_ = lean_array_fget_borrowed(v_vals_211_, v_i_212_);
v___x_218_ = l_Lean_instHashableMVarId_hash(v_k_216_);
v_h_219_ = lean_uint64_to_usize(v___x_218_);
v___x_220_ = ((size_t)5ULL);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v_depth_209_, v___x_222_);
v___x_224_ = lean_usize_mul(v___x_220_, v___x_223_);
v_h_225_ = lean_usize_shift_right(v_h_219_, v___x_224_);
v___x_226_ = lean_nat_add(v_i_212_, v___x_221_);
lean_dec(v_i_212_);
lean_inc(v_v_217_);
lean_inc(v_k_216_);
v___x_227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_entries_213_, v_h_225_, v_depth_209_, v_k_216_, v_v_217_);
v_i_212_ = v___x_226_;
v_entries_213_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_229_, lean_object* v_keys_230_, lean_object* v_vals_231_, lean_object* v_i_232_, lean_object* v_entries_233_){
_start:
{
size_t v_depth_boxed_234_; lean_object* v_res_235_; 
v_depth_boxed_234_ = lean_unbox_usize(v_depth_229_);
lean_dec(v_depth_229_);
v_res_235_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_234_, v_keys_230_, v_vals_231_, v_i_232_, v_entries_233_);
lean_dec_ref(v_vals_231_);
lean_dec_ref(v_keys_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
size_t v_x_2612__boxed_241_; size_t v_x_2613__boxed_242_; lean_object* v_res_243_; 
v_x_2612__boxed_241_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_x_2613__boxed_242_ = lean_unbox_usize(v_x_238_);
lean_dec(v_x_238_);
v_res_243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_236_, v_x_2612__boxed_241_, v_x_2613__boxed_242_, v_x_239_, v_x_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
uint64_t v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; 
v___x_247_ = l_Lean_instHashableMVarId_hash(v_x_245_);
v___x_248_ = lean_uint64_to_usize(v___x_247_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_244_, v___x_248_, v___x_249_, v_x_245_, v_x_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(lean_object* v_mvarId_251_, lean_object* v_val_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_mctx_256_; lean_object* v_cache_257_; lean_object* v_zetaDeltaFVarIds_258_; lean_object* v_postponed_259_; lean_object* v_diag_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_287_; 
v___x_255_ = lean_st_ref_take(v___y_253_);
v_mctx_256_ = lean_ctor_get(v___x_255_, 0);
v_cache_257_ = lean_ctor_get(v___x_255_, 1);
v_zetaDeltaFVarIds_258_ = lean_ctor_get(v___x_255_, 2);
v_postponed_259_ = lean_ctor_get(v___x_255_, 3);
v_diag_260_ = lean_ctor_get(v___x_255_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_287_ == 0)
{
v___x_262_ = v___x_255_;
v_isShared_263_ = v_isSharedCheck_287_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_diag_260_);
lean_inc(v_postponed_259_);
lean_inc(v_zetaDeltaFVarIds_258_);
lean_inc(v_cache_257_);
lean_inc(v_mctx_256_);
lean_dec(v___x_255_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_287_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_depth_264_; lean_object* v_levelAssignDepth_265_; lean_object* v_mvarCounter_266_; lean_object* v_lDepth_267_; lean_object* v_decls_268_; lean_object* v_userNames_269_; lean_object* v_lAssignment_270_; lean_object* v_eAssignment_271_; lean_object* v_dAssignment_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_286_; 
v_depth_264_ = lean_ctor_get(v_mctx_256_, 0);
v_levelAssignDepth_265_ = lean_ctor_get(v_mctx_256_, 1);
v_mvarCounter_266_ = lean_ctor_get(v_mctx_256_, 2);
v_lDepth_267_ = lean_ctor_get(v_mctx_256_, 3);
v_decls_268_ = lean_ctor_get(v_mctx_256_, 4);
v_userNames_269_ = lean_ctor_get(v_mctx_256_, 5);
v_lAssignment_270_ = lean_ctor_get(v_mctx_256_, 6);
v_eAssignment_271_ = lean_ctor_get(v_mctx_256_, 7);
v_dAssignment_272_ = lean_ctor_get(v_mctx_256_, 8);
v_isSharedCheck_286_ = !lean_is_exclusive(v_mctx_256_);
if (v_isSharedCheck_286_ == 0)
{
v___x_274_ = v_mctx_256_;
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_dAssignment_272_);
lean_inc(v_eAssignment_271_);
lean_inc(v_lAssignment_270_);
lean_inc(v_userNames_269_);
lean_inc(v_decls_268_);
lean_inc(v_lDepth_267_);
lean_inc(v_mvarCounter_266_);
lean_inc(v_levelAssignDepth_265_);
lean_inc(v_depth_264_);
lean_dec(v_mctx_256_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_eAssignment_271_, v_mvarId_251_, v_val_252_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 7, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_depth_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_levelAssignDepth_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_mvarCounter_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_lDepth_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_decls_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v_userNames_269_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_lAssignment_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 7, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_285_, 8, v_dAssignment_272_);
v___x_278_ = v_reuseFailAlloc_285_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_278_);
v___x_280_ = v___x_262_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_cache_257_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_zetaDeltaFVarIds_258_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_postponed_259_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_diag_260_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_st_ref_set(v___y_253_, v___x_280_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg___boxed(lean_object* v_mvarId_288_, lean_object* v_val_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_288_, v_val_289_, v___y_290_);
lean_dec(v___y_290_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__3));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__6(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__5));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_MVarId_refl___lam__0___closed__9(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__8));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0(lean_object* v_mvarId_308_, lean_object* v___x_309_, lean_object* v___x_310_, uint8_t v_check_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v_mvarId_308_);
v___x_317_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_308_, v___x_309_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_398_);
v___x_319_ = v___x_317_;
v_isShared_320_ = v_isSharedCheck_397_;
goto v_resetjp_318_;
}
else
{
lean_dec(v___x_317_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_397_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; 
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v_mvarId_308_);
v___x_321_ = l_Lean_MVarId_getType_x27(v_mvarId_308_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v___x_378_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__7));
v___x_379_ = lean_unsigned_to_nat(3u);
v___x_380_ = l_Lean_Expr_isAppOfArity(v_a_322_, v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_382_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__9, &l_Lean_MVarId_refl___lam__0___closed__9_once, _init_l_Lean_MVarId_refl___lam__0___closed__9);
lean_inc(v_a_322_);
v___x_383_ = l_Lean_indentExpr(v_a_322_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 1);
lean_ctor_set(v___x_319_, 0, v___x_384_);
v___x_386_ = v___x_319_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
lean_inc(v_mvarId_308_);
v___x_387_ = l_Lean_Meta_throwTacticEx___redArg(v___x_381_, v_mvarId_308_, v___x_386_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_dec_ref(v___x_387_);
v___y_340_ = v___y_312_;
v___y_341_ = v___y_313_;
v___y_342_ = v___y_314_;
v___y_343_ = v___y_315_;
goto v___jp_339_;
}
else
{
lean_dec(v_a_322_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v___x_310_);
lean_dec(v_mvarId_308_);
return v___x_387_;
}
}
}
else
{
lean_del_object(v___x_319_);
v___y_340_ = v___y_312_;
v___y_341_ = v___y_313_;
v___y_342_ = v___y_314_;
v___y_343_ = v___y_315_;
goto v___jp_339_;
}
v___jp_323_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec_ref(v___y_326_);
v___x_330_ = l_Lean_Expr_getAppFn(v_a_322_);
lean_dec(v_a_322_);
v___x_331_ = l_Lean_Expr_constLevels_x21(v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = l_Lean_Expr_appFn_x21(v___y_325_);
lean_dec_ref(v___y_325_);
v___x_333_ = l_Lean_Expr_appArg_x21(v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__0));
v___x_335_ = l_Lean_Name_mkStr2(v___x_334_, v___x_310_);
v___x_336_ = l_Lean_mkConst(v___x_335_, v___x_331_);
v___x_337_ = l_Lean_mkAppB(v___x_336_, v___x_333_, v___y_324_);
v___x_338_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_308_, v___x_337_, v___y_327_);
lean_dec(v___y_327_);
return v___x_338_;
}
v___jp_339_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = l_Lean_Expr_appFn_x21(v_a_322_);
v___x_345_ = l_Lean_Expr_appArg_x21(v___x_344_);
v___x_346_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_345_, v___y_341_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v___x_348_ = l_Lean_Expr_appArg_x21(v_a_322_);
v___x_349_ = l_Lean_instantiateMVars___at___00Lean_MVarId_refl_spec__0___redArg(v___x_348_, v___y_341_);
if (v_check_311_ == 0)
{
lean_dec_ref(v___x_349_);
v___y_324_ = v_a_347_;
v___y_325_ = v___x_344_;
v___y_326_ = v___y_340_;
v___y_327_ = v___y_341_;
v___y_328_ = v___y_342_;
v___y_329_ = v___y_343_;
goto v___jp_323_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_377_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_377_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
lean_inc(v_a_350_);
lean_inc(v_a_347_);
v___x_354_ = l_Lean_Meta_isExprDefEq(v_a_347_, v_a_350_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; uint8_t v___x_356_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___x_356_ = lean_unbox(v_a_355_);
lean_dec(v_a_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_357_ = ((lean_object*)(l_Lean_MVarId_refl___lam__0___closed__2));
v___x_358_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__4, &l_Lean_MVarId_refl___lam__0___closed__4_once, _init_l_Lean_MVarId_refl___lam__0___closed__4);
lean_inc(v_a_347_);
v___x_359_ = l_Lean_indentExpr(v_a_347_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_MVarId_refl___lam__0___closed__6, &l_Lean_MVarId_refl___lam__0___closed__6_once, _init_l_Lean_MVarId_refl___lam__0___closed__6);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_indentExpr(v_a_350_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_364_);
v___x_366_ = v___x_352_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; 
lean_inc(v_mvarId_308_);
v___x_367_ = l_Lean_Meta_throwTacticEx___redArg(v___x_357_, v_mvarId_308_, v___x_366_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_dec_ref(v___x_367_);
v___y_324_ = v_a_347_;
v___y_325_ = v___x_344_;
v___y_326_ = v___y_340_;
v___y_327_ = v___y_341_;
v___y_328_ = v___y_342_;
v___y_329_ = v___y_343_;
goto v___jp_323_;
}
else
{
lean_dec(v_a_347_);
lean_dec_ref(v___x_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v_a_322_);
lean_dec_ref(v___x_310_);
lean_dec(v_mvarId_308_);
return v___x_367_;
}
}
}
else
{
lean_del_object(v___x_352_);
lean_dec(v_a_350_);
v___y_324_ = v_a_347_;
v___y_325_ = v___x_344_;
v___y_326_ = v___y_340_;
v___y_327_ = v___y_341_;
v___y_328_ = v___y_342_;
v___y_329_ = v___y_343_;
goto v___jp_323_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_352_);
lean_dec(v_a_350_);
lean_dec(v_a_347_);
lean_dec_ref(v___x_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v_a_322_);
lean_dec_ref(v___x_310_);
lean_dec(v_mvarId_308_);
v_a_369_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_354_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_354_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_del_object(v___x_319_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v___x_310_);
lean_dec(v_mvarId_308_);
v_a_389_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_321_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_321_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v___x_310_);
lean_dec(v_mvarId_308_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___lam__0___boxed(lean_object* v_mvarId_399_, lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v_check_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v_check_boxed_408_; lean_object* v_res_409_; 
v_check_boxed_408_ = lean_unbox(v_check_402_);
v_res_409_ = l_Lean_MVarId_refl___lam__0(v_mvarId_399_, v___x_400_, v___x_401_, v_check_boxed_408_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl(lean_object* v_mvarId_413_, uint8_t v_check_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Lean_MVarId_refl___closed__0));
v___x_421_ = ((lean_object*)(l_Lean_MVarId_refl___closed__1));
v___x_422_ = lean_box(v_check_414_);
lean_inc(v_mvarId_413_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_MVarId_refl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_423_, 0, v_mvarId_413_);
lean_closure_set(v___f_423_, 1, v___x_421_);
lean_closure_set(v___f_423_, 2, v___x_420_);
lean_closure_set(v___f_423_, 3, v___x_422_);
v___x_424_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_413_, v___f_423_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_refl___boxed(lean_object* v_mvarId_425_, lean_object* v_check_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_check_boxed_432_; lean_object* v_res_433_; 
v_check_boxed_432_ = lean_unbox(v_check_426_);
v_res_433_ = l_Lean_MVarId_refl(v_mvarId_425_, v_check_boxed_432_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(lean_object* v_mvarId_434_, lean_object* v_val_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___redArg(v_mvarId_434_, v_val_435_, v___y_437_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1___boxed(lean_object* v_mvarId_442_, lean_object* v_val_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1(v_mvarId_442_, v_val_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1___redArg(v_x_451_, v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, size_t v_x_457_, size_t v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___redArg(v_x_456_, v_x_457_, v_x_458_, v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
size_t v_x_3133__boxed_468_; size_t v_x_3134__boxed_469_; lean_object* v_res_470_; 
v_x_3133__boxed_468_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_x_3134__boxed_469_ = lean_unbox_usize(v_x_465_);
lean_dec(v_x_465_);
v_res_470_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3(v_00_u03b2_462_, v_x_463_, v_x_3133__boxed_468_, v_x_3134__boxed_469_, v_x_466_, v_x_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_471_, lean_object* v_n_472_, lean_object* v_k_473_, lean_object* v_v_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_472_, v_k_473_, v_v_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_476_, size_t v_depth_477_, lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_heq_480_, lean_object* v_i_481_, lean_object* v_entries_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_477_, v_keys_478_, v_vals_479_, v_i_481_, v_entries_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_484_, lean_object* v_depth_485_, lean_object* v_keys_486_, lean_object* v_vals_487_, lean_object* v_heq_488_, lean_object* v_i_489_, lean_object* v_entries_490_){
_start:
{
size_t v_depth_boxed_491_; lean_object* v_res_492_; 
v_depth_boxed_491_ = lean_unbox_usize(v_depth_485_);
lean_dec(v_depth_485_);
v_res_492_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_484_, v_depth_boxed_491_, v_keys_486_, v_vals_487_, v_heq_488_, v_i_489_, v_entries_490_);
lean_dec_ref(v_vals_487_);
lean_dec_ref(v_keys_486_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_refl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_494_, v_x_495_, v_x_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_saveState___redArg(v___y_501_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
lean_inc(v___y_503_);
lean_inc(v___y_501_);
v___x_507_ = lean_apply_5(v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, lean_box(0));
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_506_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v_a_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_546_; 
v_a_517_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_546_ == 0)
{
v___x_519_ = v___x_507_;
v_isShared_520_ = v_isSharedCheck_546_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_507_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_546_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___y_522_; uint8_t v___x_544_; 
v___x_544_ = l_Lean_Exception_isInterrupt(v_a_517_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
lean_inc(v_a_517_);
v___x_545_ = l_Lean_Exception_isRuntime(v_a_517_);
v___y_522_ = v___x_545_;
goto v___jp_521_;
}
else
{
v___y_522_ = v___x_544_;
goto v___jp_521_;
}
v___jp_521_:
{
if (v___y_522_ == 0)
{
lean_object* v___x_523_; 
lean_del_object(v___x_519_);
lean_dec(v_a_517_);
v___x_523_ = l_Lean_Meta_SavedState_restore___redArg(v_a_506_, v___y_501_, v___y_503_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
lean_dec(v_a_506_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_532_);
v___x_525_ = v___x_523_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_523_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_523_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_523_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
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
else
{
lean_object* v___x_542_; 
lean_dec(v_a_506_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
if (v_isShared_520_ == 0)
{
v___x_542_ = v___x_519_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_517_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_x_499_);
v_a_547_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_505_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_505_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg___boxed(lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(lean_object* v_00_u03b1_562_, lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___boxed(lean_object* v_00_u03b1_570_, lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0(v_00_u03b1_570_, v_x_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0(lean_object* v_mvarId_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_mkFreshLevelMVar(v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__1));
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v_a_592_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_mkConst(v___x_593_, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_598_ = lean_box(0);
v___x_599_ = l_Lean_MVarId_apply(v_mvarId_585_, v___x_596_, v___x_597_, v___x_598_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_599_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v_mvarId_585_);
v_a_600_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__0___boxed(lean_object* v_mvarId_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_MVarId_heqOfEq___lam__0(v_mvarId_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1(lean_object* v___f_615_, lean_object* v_mvarId_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_642_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_642_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_642_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_642_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
if (lean_obj_tag(v_a_623_) == 1)
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v_a_623_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v_a_623_);
if (lean_obj_tag(v_val_627_) == 1)
{
lean_object* v_tail_628_; 
v_tail_628_ = lean_ctor_get(v_val_627_, 1);
if (lean_obj_tag(v_tail_628_) == 0)
{
lean_object* v_head_629_; lean_object* v___x_631_; 
lean_dec(v_mvarId_616_);
v_head_629_ = lean_ctor_get(v_val_627_, 0);
lean_inc(v_head_629_);
lean_dec_ref(v_val_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_head_629_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_head_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_634_; 
lean_dec_ref(v_val_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_mvarId_616_);
v___x_634_ = v___x_625_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_mvarId_616_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v___x_637_; 
lean_dec(v_val_627_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_mvarId_616_);
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_mvarId_616_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_a_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_mvarId_616_);
v___x_640_ = v___x_625_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_mvarId_616_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_mvarId_616_);
v_a_643_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_622_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_622_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___lam__1___boxed(lean_object* v___f_651_, lean_object* v_mvarId_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_MVarId_heqOfEq___lam__1(v___f_651_, v_mvarId_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq(lean_object* v_mvarId_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___x_667_; 
lean_inc(v_mvarId_659_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_665_, 0, v_mvarId_659_);
lean_inc(v_mvarId_659_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_MVarId_heqOfEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_666_, 0, v___f_665_);
lean_closure_set(v___f_666_, 1, v_mvarId_659_);
v___x_667_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_659_, v___f_666_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_heqOfEq___boxed(lean_object* v_mvarId_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_MVarId_heqOfEq(v_mvarId_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0(lean_object* v_mvarId_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_mkFreshLevelMVar(v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
v___x_686_ = ((lean_object*)(l_Lean_MVarId_eqOfHEq___lam__0___closed__1));
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_a_685_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_mkConst(v___x_686_, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_691_ = lean_box(0);
v___x_692_ = l_Lean_MVarId_apply(v_mvarId_678_, v___x_689_, v___x_690_, v___x_691_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_692_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v_mvarId_678_);
v_a_693_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_684_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_684_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__0___boxed(lean_object* v_mvarId_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_MVarId_eqOfHEq___lam__0(v_mvarId_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1(lean_object* v___f_708_, lean_object* v_mvarId_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_735_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_735_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
if (lean_obj_tag(v_a_716_) == 1)
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v_a_716_);
if (lean_obj_tag(v_val_720_) == 1)
{
lean_object* v_tail_721_; 
v_tail_721_ = lean_ctor_get(v_val_720_, 1);
if (lean_obj_tag(v_tail_721_) == 0)
{
lean_object* v_head_722_; lean_object* v___x_724_; 
lean_dec(v_mvarId_709_);
v_head_722_ = lean_ctor_get(v_val_720_, 0);
lean_inc(v_head_722_);
lean_dec_ref(v_val_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_head_722_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_head_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec_ref(v_val_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_mvarId_709_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_mvarId_709_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v___x_730_; 
lean_dec(v_val_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_mvarId_709_);
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_mvarId_709_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_mvarId_709_);
v___x_733_ = v___x_718_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_mvarId_709_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_mvarId_709_);
v_a_736_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_715_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_715_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___lam__1___boxed(lean_object* v___f_744_, lean_object* v_mvarId_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_MVarId_eqOfHEq___lam__1(v___f_744_, v_mvarId_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq(lean_object* v_mvarId_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___x_760_; 
lean_inc(v_mvarId_752_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_758_, 0, v_mvarId_752_);
lean_inc(v_mvarId_752_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_MVarId_eqOfHEq___lam__1___boxed), 7, 2);
lean_closure_set(v___f_759_, 0, v___f_758_);
lean_closure_set(v___f_759_, 1, v_mvarId_752_);
v___x_760_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_752_, v___f_759_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eqOfHEq___boxed(lean_object* v_mvarId_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_MVarId_eqOfHEq(v_mvarId_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0(lean_object* v_mvarId_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_mkFreshLevelMVar(v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__0___closed__1));
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_mkConst(v___x_780_, v___x_782_);
v___x_784_ = ((lean_object*)(l_Lean_MVarId_heqOfEq___lam__0___closed__2));
v___x_785_ = lean_box(0);
v___x_786_ = l_Lean_MVarId_apply(v_mvarId_772_, v___x_783_, v___x_784_, v___x_785_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v_mvarId_772_);
v_a_787_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_778_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_778_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__0___boxed(lean_object* v_mvarId_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_MVarId_hrefl___lam__0(v_mvarId_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1(lean_object* v___f_805_, lean_object* v_mvarId_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_812_ = l_Lean_observing_x3f___at___00Lean_MVarId_heqOfEq_spec__0___redArg(v___f_805_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_830_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; 
if (lean_obj_tag(v_a_813_) == 1)
{
lean_object* v_val_825_; 
v_val_825_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v_a_813_);
if (lean_obj_tag(v_val_825_) == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_mvarId_806_);
v___x_826_ = lean_box(0);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_826_);
v___x_828_ = v___x_815_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_dec(v_val_825_);
lean_del_object(v___x_815_);
v___y_818_ = v___y_807_;
v___y_819_ = v___y_808_;
v___y_820_ = v___y_809_;
v___y_821_ = v___y_810_;
goto v___jp_817_;
}
}
else
{
lean_del_object(v___x_815_);
lean_dec(v_a_813_);
v___y_818_ = v___y_807_;
v___y_819_ = v___y_808_;
v___y_820_ = v___y_809_;
v___y_821_ = v___y_810_;
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l_Lean_MVarId_hrefl___lam__1___closed__1));
v___x_823_ = lean_box(0);
v___x_824_ = l_Lean_Meta_throwTacticEx___redArg(v___x_822_, v_mvarId_806_, v___x_823_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v___x_824_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_mvarId_806_);
v_a_831_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_812_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_812_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___lam__1___boxed(lean_object* v___f_839_, lean_object* v_mvarId_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_MVarId_hrefl___lam__1(v___f_839_, v_mvarId_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl(lean_object* v_mvarId_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_855_; 
lean_inc(v_mvarId_847_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__0___boxed), 6, 1);
lean_closure_set(v___f_853_, 0, v_mvarId_847_);
lean_inc(v_mvarId_847_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_MVarId_hrefl___lam__1___boxed), 7, 2);
lean_closure_set(v___f_854_, 0, v___f_853_);
lean_closure_set(v___f_854_, 1, v_mvarId_847_);
v___x_855_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_refl_spec__2___redArg(v_mvarId_847_, v___f_854_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hrefl___boxed(lean_object* v_mvarId_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_MVarId_hrefl(v_mvarId_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v_res_862_;
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
