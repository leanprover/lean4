// Lean compiler output
// Module: Lean.Meta.Tactic.Generalize
// Imports: public import Lean.Meta.KAbstract public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.Tactic.Revert import Lean.Meta.AppBuilder
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedGeneralizeArg;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "result is not type correct"};
static const lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "generalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 87, 171, 88, 232, 182, 211, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_generalizeHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_generalizeHyp___closed__0 = (const lean_object*)&l_Lean_MVarId_generalizeHyp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_obj_once(&l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2, &l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2_once, _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2);
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_7_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3, &l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3_once, _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(lean_object* v_e_12_, lean_object* v___y_13_){
_start:
{
uint8_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = l_Lean_Expr_hasMVar(v_e_12_);
v___x_16_ = lean_bool_not(v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v_mctx_18_; lean_object* v___x_19_; lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_22_; lean_object* v_cache_23_; lean_object* v_zetaDeltaFVarIds_24_; lean_object* v_postponed_25_; lean_object* v_diag_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_35_; 
v___x_17_ = lean_st_ref_get(v___y_13_);
v_mctx_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_mctx_18_);
lean_dec(v___x_17_);
v___x_19_ = l_Lean_instantiateMVarsCore(v_mctx_18_, v_e_12_);
v_fst_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_fst_20_);
v_snd_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_snd_21_);
lean_dec_ref(v___x_19_);
v___x_22_ = lean_st_ref_take(v___y_13_);
v_cache_23_ = lean_ctor_get(v___x_22_, 1);
v_zetaDeltaFVarIds_24_ = lean_ctor_get(v___x_22_, 2);
v_postponed_25_ = lean_ctor_get(v___x_22_, 3);
v_diag_26_ = lean_ctor_get(v___x_22_, 4);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_35_ == 0)
{
lean_object* v_unused_36_; 
v_unused_36_ = lean_ctor_get(v___x_22_, 0);
lean_dec(v_unused_36_);
v___x_28_ = v___x_22_;
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_diag_26_);
lean_inc(v_postponed_25_);
lean_inc(v_zetaDeltaFVarIds_24_);
lean_inc(v_cache_23_);
lean_dec(v___x_22_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v_snd_21_);
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_snd_21_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_cache_23_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v_zetaDeltaFVarIds_24_);
lean_ctor_set(v_reuseFailAlloc_34_, 3, v_postponed_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 4, v_diag_26_);
v___x_31_ = v_reuseFailAlloc_34_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_st_ref_set(v___y_13_, v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v_fst_20_);
return v___x_33_;
}
}
}
else
{
lean_object* v___x_37_; 
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_e_12_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_38_, v___y_39_);
lean_dec(v___y_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_42_, v___y_44_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object* v_e_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(v_e_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object* v_args_59_, uint8_t v_transparency_60_, lean_object* v_target_61_, lean_object* v_i_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_array_get_size(v_args_59_);
v___x_69_ = lean_nat_dec_lt(v_i_62_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v_target_61_);
return v___x_70_;
}
else
{
lean_object* v_arg_71_; lean_object* v_expr_72_; lean_object* v_xName_x3f_73_; lean_object* v___x_74_; 
v_arg_71_ = lean_array_fget_borrowed(v_args_59_, v_i_62_);
v_expr_72_ = lean_ctor_get(v_arg_71_, 0);
v_xName_x3f_73_ = lean_ctor_get(v_arg_71_, 1);
lean_inc_ref(v_expr_72_);
v___x_74_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_72_, v_a_64_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_n(v_a_75_, 2);
lean_dec_ref_known(v___x_74_, 1);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
v___x_76_ = lean_infer_type(v_a_75_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_78_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_77_, v_a_64_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_i_62_, v___x_80_);
v___x_82_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_59_, v_transparency_60_, v_target_61_, v___x_81_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v___x_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v_xName_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_82_, 1);
if (lean_obj_tag(v_xName_x3f_73_) == 1)
{
lean_object* v_val_146_; 
v_val_146_ = lean_ctor_get(v_xName_x3f_73_, 0);
lean_inc(v_val_146_);
v_xName_85_ = v_val_146_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
v___y_89_ = v_a_66_;
goto v___jp_84_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
v___x_148_ = l_Lean_Core_mkFreshUserName(v___x_147_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v_xName_85_ = v_a_149_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
v___y_89_ = v_a_66_;
goto v___jp_84_;
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_a_83_);
lean_dec(v_a_79_);
lean_dec(v_a_75_);
v_a_150_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_148_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
v___jp_84_:
{
lean_object* v___x_90_; uint8_t v_foApprox_91_; uint8_t v_ctxApprox_92_; uint8_t v_quasiPatternApprox_93_; uint8_t v_constApprox_94_; uint8_t v_isDefEqStuckEx_95_; uint8_t v_unificationHints_96_; uint8_t v_proofIrrelevance_97_; uint8_t v_assignSyntheticOpaque_98_; uint8_t v_offsetCnstrs_99_; uint8_t v_etaStruct_100_; uint8_t v_univApprox_101_; uint8_t v_iota_102_; uint8_t v_beta_103_; uint8_t v_proj_104_; uint8_t v_zeta_105_; uint8_t v_zetaDelta_106_; uint8_t v_zetaUnused_107_; uint8_t v_zetaHave_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_145_; 
v___x_90_ = l_Lean_Meta_Context_config(v___y_86_);
v_foApprox_91_ = lean_ctor_get_uint8(v___x_90_, 0);
v_ctxApprox_92_ = lean_ctor_get_uint8(v___x_90_, 1);
v_quasiPatternApprox_93_ = lean_ctor_get_uint8(v___x_90_, 2);
v_constApprox_94_ = lean_ctor_get_uint8(v___x_90_, 3);
v_isDefEqStuckEx_95_ = lean_ctor_get_uint8(v___x_90_, 4);
v_unificationHints_96_ = lean_ctor_get_uint8(v___x_90_, 5);
v_proofIrrelevance_97_ = lean_ctor_get_uint8(v___x_90_, 6);
v_assignSyntheticOpaque_98_ = lean_ctor_get_uint8(v___x_90_, 7);
v_offsetCnstrs_99_ = lean_ctor_get_uint8(v___x_90_, 8);
v_etaStruct_100_ = lean_ctor_get_uint8(v___x_90_, 10);
v_univApprox_101_ = lean_ctor_get_uint8(v___x_90_, 11);
v_iota_102_ = lean_ctor_get_uint8(v___x_90_, 12);
v_beta_103_ = lean_ctor_get_uint8(v___x_90_, 13);
v_proj_104_ = lean_ctor_get_uint8(v___x_90_, 14);
v_zeta_105_ = lean_ctor_get_uint8(v___x_90_, 15);
v_zetaDelta_106_ = lean_ctor_get_uint8(v___x_90_, 16);
v_zetaUnused_107_ = lean_ctor_get_uint8(v___x_90_, 17);
v_zetaHave_108_ = lean_ctor_get_uint8(v___x_90_, 18);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_145_ == 0)
{
v___x_110_ = v___x_90_;
v_isShared_111_ = v_isSharedCheck_145_;
goto v_resetjp_109_;
}
else
{
lean_dec(v___x_90_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_145_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
uint8_t v_trackZetaDelta_112_; lean_object* v_zetaDeltaSet_113_; lean_object* v_lctx_114_; lean_object* v_localInstances_115_; lean_object* v_defEqCtx_x3f_116_; lean_object* v_synthPendingDepth_117_; lean_object* v_canUnfold_x3f_118_; uint8_t v_univApprox_119_; uint8_t v_inTypeClassResolution_120_; uint8_t v_cacheInferType_121_; lean_object* v_config_123_; 
v_trackZetaDelta_112_ = lean_ctor_get_uint8(v___y_86_, sizeof(void*)*7);
v_zetaDeltaSet_113_ = lean_ctor_get(v___y_86_, 1);
v_lctx_114_ = lean_ctor_get(v___y_86_, 2);
v_localInstances_115_ = lean_ctor_get(v___y_86_, 3);
v_defEqCtx_x3f_116_ = lean_ctor_get(v___y_86_, 4);
v_synthPendingDepth_117_ = lean_ctor_get(v___y_86_, 5);
v_canUnfold_x3f_118_ = lean_ctor_get(v___y_86_, 6);
v_univApprox_119_ = lean_ctor_get_uint8(v___y_86_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_120_ = lean_ctor_get_uint8(v___y_86_, sizeof(void*)*7 + 2);
v_cacheInferType_121_ = lean_ctor_get_uint8(v___y_86_, sizeof(void*)*7 + 3);
if (v_isShared_111_ == 0)
{
v_config_123_ = v___x_110_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 0, v_foApprox_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 1, v_ctxApprox_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 2, v_quasiPatternApprox_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 3, v_constApprox_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 4, v_isDefEqStuckEx_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 5, v_unificationHints_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 6, v_proofIrrelevance_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 7, v_assignSyntheticOpaque_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 8, v_offsetCnstrs_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 10, v_etaStruct_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 11, v_univApprox_101_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 12, v_iota_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 13, v_beta_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 14, v_proj_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 15, v_zeta_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 16, v_zetaDelta_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 17, v_zetaUnused_107_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, 18, v_zetaHave_108_);
v_config_123_ = v_reuseFailAlloc_144_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v_key_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
lean_ctor_set_uint8(v_config_123_, 9, v_transparency_60_);
v___x_124_ = l_Lean_Meta_Context_configKey(v___y_86_);
v___x_125_ = 3ULL;
v___x_126_ = lean_uint64_shift_right(v___x_124_, v___x_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_uint64_shift_left(v___x_126_, v___x_125_);
v___x_129_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_60_);
v_key_130_ = lean_uint64_lor(v___x_128_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_131_, 0, v_config_123_);
lean_ctor_set_uint64(v___x_131_, sizeof(void*)*1, v_key_130_);
lean_inc(v_canUnfold_x3f_118_);
lean_inc(v_synthPendingDepth_117_);
lean_inc(v_defEqCtx_x3f_116_);
lean_inc_ref(v_localInstances_115_);
lean_inc_ref(v_lctx_114_);
lean_inc(v_zetaDeltaSet_113_);
v___x_132_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_zetaDeltaSet_113_);
lean_ctor_set(v___x_132_, 2, v_lctx_114_);
lean_ctor_set(v___x_132_, 3, v_localInstances_115_);
lean_ctor_set(v___x_132_, 4, v_defEqCtx_x3f_116_);
lean_ctor_set(v___x_132_, 5, v_synthPendingDepth_117_);
lean_ctor_set(v___x_132_, 6, v_canUnfold_x3f_118_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*7, v_trackZetaDelta_112_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*7 + 1, v_univApprox_119_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*7 + 2, v_inTypeClassResolution_120_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*7 + 3, v_cacheInferType_121_);
v___x_133_ = l_Lean_Meta_kabstract(v_a_83_, v_a_75_, v___x_127_, v___x_132_, v___y_87_, v___y_88_, v___y_89_);
lean_dec_ref_known(v___x_132_, 7);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_143_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = 0;
v___x_139_ = l_Lean_mkForall(v_xName_85_, v___x_138_, v_a_79_, v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_139_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_dec(v_xName_85_);
lean_dec(v_a_79_);
return v___x_133_;
}
}
}
}
}
else
{
lean_dec(v_a_79_);
lean_dec(v_a_75_);
return v___x_82_;
}
}
else
{
lean_dec(v_a_75_);
lean_dec_ref(v_target_61_);
return v___x_78_;
}
}
else
{
lean_dec(v_a_75_);
lean_dec_ref(v_target_61_);
return v___x_76_;
}
}
else
{
lean_dec_ref(v_target_61_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_158_, lean_object* v_transparency_159_, lean_object* v_target_160_, lean_object* v_i_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_transparency_boxed_167_; lean_object* v_res_168_; 
v_transparency_boxed_167_ = lean_unbox(v_transparency_159_);
v_res_168_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_158_, v_transparency_boxed_167_, v_target_160_, v_i_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_i_161_);
lean_dec_ref(v_args_158_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_169_, lean_object* v_xs_170_, lean_object* v_type_171_, lean_object* v_i_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_array_get_size(v_xs_170_);
v___x_179_ = lean_nat_dec_lt(v_i_172_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_i_172_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_type_171_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v_arg_184_; lean_object* v_hName_x3f_185_; 
v___x_183_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_184_ = lean_array_get_borrowed(v___x_183_, v_args_169_, v_i_172_);
v_hName_x3f_185_ = lean_ctor_get(v_arg_184_, 2);
if (lean_obj_tag(v_hName_x3f_185_) == 1)
{
lean_object* v_expr_186_; lean_object* v_val_187_; lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_expr_186_ = lean_ctor_get(v_arg_184_, 0);
v_val_187_ = lean_ctor_get(v_hName_x3f_185_, 0);
v___x_218_ = lean_array_fget_borrowed(v_xs_170_, v_i_172_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v___x_218_);
v___x_219_ = lean_infer_type(v___x_218_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_221_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_219_, 1);
lean_inc_ref(v_expr_186_);
v___x_221_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_186_, v_a_174_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_n(v_a_222_, 2);
lean_dec_ref_known(v___x_221_, 1);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
v___x_223_ = lean_infer_type(v_a_222_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_224_, v_a_174_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_Meta_isExprDefEq(v_a_220_, v_a_226_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; uint8_t v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = lean_unbox(v_a_228_);
lean_dec(v_a_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_inc(v___x_218_);
lean_inc(v_a_222_);
v___x_230_ = l_Lean_Meta_mkHEq(v_a_222_, v___x_218_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Meta_mkHEqRefl(v_a_222_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v_fst_189_ = v_a_231_;
v_snd_190_ = v_a_233_;
v___y_191_ = v_a_173_;
v___y_192_ = v_a_174_;
v___y_193_ = v_a_175_;
v___y_194_ = v_a_176_;
goto v___jp_188_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_a_231_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_234_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_a_222_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_242_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v___x_250_; 
lean_inc(v___x_218_);
lean_inc(v_a_222_);
v___x_250_ = l_Lean_Meta_mkEq(v_a_222_, v___x_218_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = l_Lean_Meta_mkEqRefl(v_a_222_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v_fst_189_ = v_a_251_;
v_snd_190_ = v_a_253_;
v___y_191_ = v_a_173_;
v___y_192_ = v_a_174_;
v___y_193_ = v_a_175_;
v___y_194_ = v_a_176_;
goto v___jp_188_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_a_251_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_254_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_252_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_a_222_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_262_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_250_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_250_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_222_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_270_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_227_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_227_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec(v_a_222_);
lean_dec(v_a_220_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_278_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_225_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_225_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_a_222_);
lean_dec(v_a_220_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_286_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_223_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_223_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_a_220_);
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_294_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_221_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_221_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_i_172_);
lean_dec_ref(v_type_171_);
v_a_302_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_219_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_219_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
v___jp_188_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_add(v_i_172_, v___x_195_);
lean_dec(v_i_172_);
v___x_197_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_169_, v_xs_170_, v_type_171_, v___x_196_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_217_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_217_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_217_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_217_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v_fst_202_ = lean_ctor_get(v_a_198_, 0);
v_snd_203_ = lean_ctor_get(v_a_198_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_205_ = v_a_198_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_snd_203_);
lean_inc(v_fst_202_);
lean_dec(v_a_198_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v_snd_190_);
lean_ctor_set(v___x_207_, 1, v_fst_202_);
v___x_208_ = 0;
lean_inc(v_val_187_);
v___x_209_ = l_Lean_mkForall(v_val_187_, v___x_208_, v_fst_189_, v_snd_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_209_);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_211_);
v___x_213_ = v___x_200_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_190_);
lean_dec_ref(v_fst_189_);
return v___x_197_;
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_i_172_, v___x_310_);
lean_dec(v_i_172_);
v_i_172_ = v___x_311_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_313_, lean_object* v_xs_314_, lean_object* v_type_315_, lean_object* v_i_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_313_, v_xs_314_, v_type_315_, v_i_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec_ref(v_xs_314_);
lean_dec_ref(v_args_313_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0(lean_object* v_k_323_, lean_object* v_b_324_, lean_object* v_c_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
v___x_331_ = lean_apply_7(v_k_323_, v_b_324_, v_c_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0___boxed(lean_object* v_k_332_, lean_object* v_b_333_, lean_object* v_c_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0(v_k_332_, v_b_333_, v_c_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_type_341_, lean_object* v_maxFVars_x3f_342_, lean_object* v_k_343_, uint8_t v_cleanupAnnotations_344_, uint8_t v_whnfType_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___f_351_; lean_object* v___x_352_; 
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_351_, 0, v_k_343_);
v___x_352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_341_, v_maxFVars_x3f_342_, v___f_351_, v_cleanupAnnotations_344_, v_whnfType_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_352_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_type_369_, lean_object* v_maxFVars_x3f_370_, lean_object* v_k_371_, lean_object* v_cleanupAnnotations_372_, lean_object* v_whnfType_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_379_; uint8_t v_whnfType_boxed_380_; lean_object* v_res_381_; 
v_cleanupAnnotations_boxed_379_ = lean_unbox(v_cleanupAnnotations_372_);
v_whnfType_boxed_380_ = lean_unbox(v_whnfType_373_);
v_res_381_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_type_369_, v_maxFVars_x3f_370_, v_k_371_, v_cleanupAnnotations_boxed_379_, v_whnfType_boxed_380_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_type_383_, lean_object* v_maxFVars_x3f_384_, lean_object* v_k_385_, uint8_t v_cleanupAnnotations_386_, uint8_t v_whnfType_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_type_383_, v_maxFVars_x3f_384_, v_k_385_, v_cleanupAnnotations_386_, v_whnfType_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_00_u03b1_394_, lean_object* v_type_395_, lean_object* v_maxFVars_x3f_396_, lean_object* v_k_397_, lean_object* v_cleanupAnnotations_398_, lean_object* v_whnfType_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_405_; uint8_t v_whnfType_boxed_406_; lean_object* v_res_407_; 
v_cleanupAnnotations_boxed_405_ = lean_unbox(v_cleanupAnnotations_398_);
v_whnfType_boxed_406_ = lean_unbox(v_whnfType_399_);
v_res_407_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_00_u03b1_394_, v_type_395_, v_maxFVars_x3f_396_, v_k_397_, v_cleanupAnnotations_boxed_405_, v_whnfType_boxed_406_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_408_, lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_408_, v_x_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_415_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_432_, lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_432_, v_x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_440_, lean_object* v_mvarId_441_, lean_object* v_x_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_441_, v_x_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_449_, lean_object* v_mvarId_450_, lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_449_, v_mvarId_450_, v_x_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_458_, lean_object* v___x_459_, uint8_t v___x_460_, uint8_t v___x_461_, lean_object* v_xs_462_, lean_object* v_type_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_458_, v_xs_462_, v_type_463_, v___x_459_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_497_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v_fst_471_ = lean_ctor_get(v_a_470_, 0);
v_snd_472_ = lean_ctor_get(v_a_470_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_497_ == 0)
{
v___x_474_ = v_a_470_;
v_isShared_475_ = v_isSharedCheck_497_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v_a_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_497_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
uint8_t v___x_476_; lean_object* v___x_477_; 
v___x_476_ = 1;
v___x_477_ = l_Lean_Meta_mkForallFVars(v_xs_462_, v_snd_472_, v___x_460_, v___x_461_, v___x_461_, v___x_476_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_488_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_488_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_488_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_a_478_);
v___x_483_ = v___x_474_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_a_478_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_474_);
lean_dec(v_fst_471_);
v_a_489_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_477_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_477_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
else
{
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_498_, lean_object* v___x_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v_xs_502_, lean_object* v_type_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_4517__boxed_509_; uint8_t v___x_4518__boxed_510_; lean_object* v_res_511_; 
v___x_4517__boxed_509_ = lean_unbox(v___x_500_);
v___x_4518__boxed_510_ = lean_unbox(v___x_501_);
v_res_511_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_498_, v___x_499_, v___x_4517__boxed_509_, v___x_4518__boxed_510_, v_xs_502_, v_type_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_xs_502_);
lean_dec_ref(v_args_498_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_as_512_, size_t v_i_513_, size_t v_stop_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_eq(v_i_513_, v_stop_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_hName_x3f_517_; uint8_t v___x_518_; 
v___x_516_ = lean_array_uget_borrowed(v_as_512_, v_i_513_);
v_hName_x3f_517_ = lean_ctor_get(v___x_516_, 2);
v___x_518_ = 1;
if (lean_obj_tag(v_hName_x3f_517_) == 0)
{
if (v___x_515_ == 0)
{
size_t v___x_519_; size_t v___x_520_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_513_, v___x_519_);
v_i_513_ = v___x_520_;
goto _start;
}
else
{
return v___x_518_;
}
}
else
{
return v___x_518_;
}
}
else
{
uint8_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_as_523_, lean_object* v_i_524_, lean_object* v_stop_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; uint8_t v_res_528_; lean_object* v_r_529_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_525_);
lean_dec(v_stop_525_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_as_523_, v_i_boxed_526_, v_stop_boxed_527_);
lean_dec_ref(v_as_523_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_ks_534_; lean_object* v_vs_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_559_; 
v_ks_534_ = lean_ctor_get(v_x_530_, 0);
v_vs_535_ = lean_ctor_get(v_x_530_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_559_ == 0)
{
v___x_537_ = v_x_530_;
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_vs_535_);
lean_inc(v_ks_534_);
lean_dec(v_x_530_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_get_size(v_ks_534_);
v___x_540_ = lean_nat_dec_lt(v_x_531_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_dec(v_x_531_);
v___x_541_ = lean_array_push(v_ks_534_, v_x_532_);
v___x_542_ = lean_array_push(v_vs_535_, v_x_533_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v___x_542_);
lean_ctor_set(v___x_537_, 0, v___x_541_);
v___x_544_ = v___x_537_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v_k_x27_546_; uint8_t v___x_547_; 
v_k_x27_546_ = lean_array_fget_borrowed(v_ks_534_, v_x_531_);
v___x_547_ = l_Lean_instBEqMVarId_beq(v_x_532_, v_k_x27_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_549_; 
if (v_isShared_538_ == 0)
{
v___x_549_ = v___x_537_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_ks_534_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vs_535_);
v___x_549_ = v_reuseFailAlloc_553_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_x_531_, v___x_550_);
lean_dec(v_x_531_);
v_x_530_ = v___x_549_;
v_x_531_ = v___x_551_;
goto _start;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = lean_array_fset(v_ks_534_, v_x_531_, v_x_532_);
v___x_555_ = lean_array_fset(v_vs_535_, v_x_531_, v_x_533_);
lean_dec(v_x_531_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v___x_555_);
lean_ctor_set(v___x_537_, 0, v___x_554_);
v___x_557_ = v___x_537_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6___redArg(lean_object* v_n_560_, lean_object* v_k_561_, lean_object* v_v_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7___redArg(v_n_560_, v___x_563_, v_k_561_, v_v_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(lean_object* v_x_566_, size_t v_x_567_, size_t v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v_es_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v_j_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_es_571_ = lean_ctor_get(v_x_566_, 0);
v___x_572_ = ((size_t)31ULL);
v___x_573_ = lean_usize_land(v_x_567_, v___x_572_);
v_j_574_ = lean_usize_to_nat(v___x_573_);
v___x_575_ = lean_array_get_size(v_es_571_);
v___x_576_ = lean_nat_dec_lt(v_j_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec(v_j_574_);
lean_dec(v_x_570_);
lean_dec(v_x_569_);
return v_x_566_;
}
else
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_615_; 
lean_inc_ref(v_es_571_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_x_566_, 0);
lean_dec(v_unused_616_);
v___x_578_ = v_x_566_;
v_isShared_579_ = v_isSharedCheck_615_;
goto v_resetjp_577_;
}
else
{
lean_dec(v_x_566_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_615_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_v_580_; lean_object* v___x_581_; lean_object* v_xs_x27_582_; lean_object* v___y_584_; 
v_v_580_ = lean_array_fget(v_es_571_, v_j_574_);
v___x_581_ = lean_box(0);
v_xs_x27_582_ = lean_array_fset(v_es_571_, v_j_574_, v___x_581_);
switch(lean_obj_tag(v_v_580_))
{
case 0:
{
lean_object* v_key_589_; lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_600_; 
v_key_589_ = lean_ctor_get(v_v_580_, 0);
v_val_590_ = lean_ctor_get(v_v_580_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_v_580_);
if (v_isSharedCheck_600_ == 0)
{
v___x_592_ = v_v_580_;
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_inc(v_key_589_);
lean_dec(v_v_580_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_instBEqMVarId_beq(v_x_569_, v_key_589_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_592_);
v___x_595_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_589_, v_val_590_, v_x_569_, v_x_570_);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___y_584_ = v___x_596_;
goto v___jp_583_;
}
else
{
lean_object* v___x_598_; 
lean_dec(v_val_590_);
lean_dec(v_key_589_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_x_570_);
lean_ctor_set(v___x_592_, 0, v_x_569_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_x_569_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_x_570_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v___y_584_ = v___x_598_;
goto v___jp_583_;
}
}
}
}
case 1:
{
lean_object* v_node_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_613_; 
v_node_601_ = lean_ctor_get(v_v_580_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_v_580_);
if (v_isSharedCheck_613_ == 0)
{
v___x_603_ = v_v_580_;
v_isShared_604_ = v_isSharedCheck_613_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_node_601_);
lean_dec(v_v_580_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_613_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_605_ = ((size_t)5ULL);
v___x_606_ = lean_usize_shift_right(v_x_567_, v___x_605_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_x_568_, v___x_607_);
v___x_609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(v_node_601_, v___x_606_, v___x_608_, v_x_569_, v_x_570_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_609_);
v___x_611_ = v___x_603_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v___y_584_ = v___x_611_;
goto v___jp_583_;
}
}
}
default: 
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_x_569_);
lean_ctor_set(v___x_614_, 1, v_x_570_);
v___y_584_ = v___x_614_;
goto v___jp_583_;
}
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_array_fset(v_xs_x27_582_, v_j_574_, v___y_584_);
lean_dec(v_j_574_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_585_);
v___x_587_ = v___x_578_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_object* v_ks_617_; lean_object* v_vs_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_638_; 
v_ks_617_ = lean_ctor_get(v_x_566_, 0);
v_vs_618_ = lean_ctor_get(v_x_566_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_638_ == 0)
{
v___x_620_ = v_x_566_;
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_vs_618_);
lean_inc(v_ks_617_);
lean_dec(v_x_566_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_ks_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_vs_618_);
v___x_623_ = v_reuseFailAlloc_637_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v_newNode_624_; uint8_t v___y_626_; size_t v___x_632_; uint8_t v___x_633_; 
v_newNode_624_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6___redArg(v___x_623_, v_x_569_, v_x_570_);
v___x_632_ = ((size_t)7ULL);
v___x_633_ = lean_usize_dec_le(v___x_632_, v_x_568_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_624_);
v___x_635_ = lean_unsigned_to_nat(4u);
v___x_636_ = lean_nat_dec_lt(v___x_634_, v___x_635_);
lean_dec(v___x_634_);
v___y_626_ = v___x_636_;
goto v___jp_625_;
}
else
{
v___y_626_ = v___x_633_;
goto v___jp_625_;
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
lean_object* v_ks_627_; lean_object* v_vs_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_ks_627_ = lean_ctor_get(v_newNode_624_, 0);
lean_inc_ref(v_ks_627_);
v_vs_628_ = lean_ctor_get(v_newNode_624_, 1);
lean_inc_ref(v_vs_628_);
lean_dec_ref(v_newNode_624_);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg(v_x_568_, v_ks_627_, v_vs_628_, v___x_629_, v___x_630_);
lean_dec_ref(v_vs_628_);
lean_dec_ref(v_ks_627_);
return v___x_631_;
}
else
{
return v_newNode_624_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg(size_t v_depth_639_, lean_object* v_keys_640_, lean_object* v_vals_641_, lean_object* v_i_642_, lean_object* v_entries_643_){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_array_get_size(v_keys_640_);
v___x_645_ = lean_nat_dec_lt(v_i_642_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v_i_642_);
return v_entries_643_;
}
else
{
lean_object* v_k_646_; lean_object* v_v_647_; uint64_t v___x_648_; size_t v_h_649_; size_t v___x_650_; lean_object* v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v_h_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_k_646_ = lean_array_fget_borrowed(v_keys_640_, v_i_642_);
v_v_647_ = lean_array_fget_borrowed(v_vals_641_, v_i_642_);
v___x_648_ = l_Lean_instHashableMVarId_hash(v_k_646_);
v_h_649_ = lean_uint64_to_usize(v___x_648_);
v___x_650_ = ((size_t)5ULL);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_sub(v_depth_639_, v___x_652_);
v___x_654_ = lean_usize_mul(v___x_650_, v___x_653_);
v_h_655_ = lean_usize_shift_right(v_h_649_, v___x_654_);
v___x_656_ = lean_nat_add(v_i_642_, v___x_651_);
lean_dec(v_i_642_);
lean_inc(v_v_647_);
lean_inc(v_k_646_);
v___x_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(v_entries_643_, v_h_655_, v_depth_639_, v_k_646_, v_v_647_);
v_i_642_ = v___x_656_;
v_entries_643_ = v___x_657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_depth_659_, lean_object* v_keys_660_, lean_object* v_vals_661_, lean_object* v_i_662_, lean_object* v_entries_663_){
_start:
{
size_t v_depth_boxed_664_; lean_object* v_res_665_; 
v_depth_boxed_664_ = lean_unbox_usize(v_depth_659_);
lean_dec(v_depth_659_);
v_res_665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg(v_depth_boxed_664_, v_keys_660_, v_vals_661_, v_i_662_, v_entries_663_);
lean_dec_ref(v_vals_661_);
lean_dec_ref(v_keys_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
size_t v_x_4691__boxed_671_; size_t v_x_4692__boxed_672_; lean_object* v_res_673_; 
v_x_4691__boxed_671_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_x_4692__boxed_672_ = lean_unbox_usize(v_x_668_);
lean_dec(v_x_668_);
v_res_673_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(v_x_666_, v_x_4691__boxed_671_, v_x_4692__boxed_672_, v_x_669_, v_x_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2___redArg(lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
uint64_t v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v___x_677_ = l_Lean_instHashableMVarId_hash(v_x_675_);
v___x_678_ = lean_uint64_to_usize(v___x_677_);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(v_x_674_, v___x_678_, v___x_679_, v_x_675_, v_x_676_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(lean_object* v_mvarId_681_, lean_object* v_val_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_mctx_686_; lean_object* v_cache_687_; lean_object* v_zetaDeltaFVarIds_688_; lean_object* v_postponed_689_; lean_object* v_diag_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_718_; 
v___x_685_ = lean_st_ref_take(v___y_683_);
v_mctx_686_ = lean_ctor_get(v___x_685_, 0);
v_cache_687_ = lean_ctor_get(v___x_685_, 1);
v_zetaDeltaFVarIds_688_ = lean_ctor_get(v___x_685_, 2);
v_postponed_689_ = lean_ctor_get(v___x_685_, 3);
v_diag_690_ = lean_ctor_get(v___x_685_, 4);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_718_ == 0)
{
v___x_692_ = v___x_685_;
v_isShared_693_ = v_isSharedCheck_718_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_diag_690_);
lean_inc(v_postponed_689_);
lean_inc(v_zetaDeltaFVarIds_688_);
lean_inc(v_cache_687_);
lean_inc(v_mctx_686_);
lean_dec(v___x_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_718_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_depth_694_; lean_object* v_levelAssignDepth_695_; lean_object* v_lmvarCounter_696_; lean_object* v_mvarCounter_697_; lean_object* v_lDecls_698_; lean_object* v_decls_699_; lean_object* v_userNames_700_; lean_object* v_lAssignment_701_; lean_object* v_eAssignment_702_; lean_object* v_dAssignment_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_717_; 
v_depth_694_ = lean_ctor_get(v_mctx_686_, 0);
v_levelAssignDepth_695_ = lean_ctor_get(v_mctx_686_, 1);
v_lmvarCounter_696_ = lean_ctor_get(v_mctx_686_, 2);
v_mvarCounter_697_ = lean_ctor_get(v_mctx_686_, 3);
v_lDecls_698_ = lean_ctor_get(v_mctx_686_, 4);
v_decls_699_ = lean_ctor_get(v_mctx_686_, 5);
v_userNames_700_ = lean_ctor_get(v_mctx_686_, 6);
v_lAssignment_701_ = lean_ctor_get(v_mctx_686_, 7);
v_eAssignment_702_ = lean_ctor_get(v_mctx_686_, 8);
v_dAssignment_703_ = lean_ctor_get(v_mctx_686_, 9);
v_isSharedCheck_717_ = !lean_is_exclusive(v_mctx_686_);
if (v_isSharedCheck_717_ == 0)
{
v___x_705_ = v_mctx_686_;
v_isShared_706_ = v_isSharedCheck_717_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_dAssignment_703_);
lean_inc(v_eAssignment_702_);
lean_inc(v_lAssignment_701_);
lean_inc(v_userNames_700_);
lean_inc(v_decls_699_);
lean_inc(v_lDecls_698_);
lean_inc(v_mvarCounter_697_);
lean_inc(v_lmvarCounter_696_);
lean_inc(v_levelAssignDepth_695_);
lean_inc(v_depth_694_);
lean_dec(v_mctx_686_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_717_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2___redArg(v_eAssignment_702_, v_mvarId_681_, v_val_682_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 8, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_depth_694_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_levelAssignDepth_695_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_lmvarCounter_696_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_mvarCounter_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_lDecls_698_);
lean_ctor_set(v_reuseFailAlloc_716_, 5, v_decls_699_);
lean_ctor_set(v_reuseFailAlloc_716_, 6, v_userNames_700_);
lean_ctor_set(v_reuseFailAlloc_716_, 7, v_lAssignment_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 8, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_716_, 9, v_dAssignment_703_);
v___x_709_ = v_reuseFailAlloc_716_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_709_);
v___x_711_ = v___x_692_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_cache_687_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_zetaDeltaFVarIds_688_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_postponed_689_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_diag_690_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_st_ref_set(v___y_683_, v___x_711_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg___boxed(lean_object* v_mvarId_719_, lean_object* v_val_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(v_mvarId_719_, v_val_720_, v___y_721_);
lean_dec(v___y_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_724_, size_t v_i_725_, lean_object* v_bs_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_727_ == 0)
{
return v_bs_726_;
}
else
{
lean_object* v_v_728_; lean_object* v_expr_729_; lean_object* v___x_730_; lean_object* v_bs_x27_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v_v_728_ = lean_array_uget_borrowed(v_bs_726_, v_i_725_);
v_expr_729_ = lean_ctor_get(v_v_728_, 0);
lean_inc_ref(v_expr_729_);
v___x_730_ = lean_unsigned_to_nat(0u);
v_bs_x27_731_ = lean_array_uset(v_bs_726_, v_i_725_, v___x_730_);
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_725_, v___x_732_);
v___x_734_ = lean_array_uset(v_bs_x27_731_, v_i_725_, v_expr_729_);
v_i_725_ = v___x_733_;
v_bs_726_ = v___x_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_736_, lean_object* v_i_737_, lean_object* v_bs_738_){
_start:
{
size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_sz_boxed_739_ = lean_unbox_usize(v_sz_736_);
lean_dec(v_sz_736_);
v_i_boxed_740_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_739_, v_i_boxed_740_, v_bs_738_);
return v_res_741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_745_, lean_object* v___x_746_, lean_object* v_args_747_, uint8_t v_transparency_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
lean_inc(v___x_746_);
lean_inc(v_mvarId_745_);
v___x_754_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_745_, v___x_746_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; 
lean_dec_ref_known(v___x_754_, 1);
lean_inc(v_mvarId_745_);
v___x_755_ = l_Lean_MVarId_getTag(v_mvarId_745_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
lean_inc(v_mvarId_745_);
v___x_757_ = l_Lean_MVarId_getType(v_mvarId_745_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_874_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_758_, v___y_750_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_874_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_874_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_874_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_747_, v_transparency_748_, v_a_760_, v___x_764_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; uint8_t v___y_774_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___x_842_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc_n(v_a_766_, 2);
lean_dec_ref_known(v___x_765_, 1);
v___x_842_ = l_Lean_Meta_isTypeCorrect(v_a_766_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; uint8_t v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_766_);
v___x_846_ = l_Lean_indentExpr(v_a_766_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_inc(v_mvarId_745_);
v___x_849_ = l_Lean_Meta_throwTacticEx___redArg(v___x_746_, v_mvarId_745_, v___x_848_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_dec_ref_known(v___x_849_, 1);
v___y_831_ = v___y_749_;
v___y_832_ = v___y_750_;
v___y_833_ = v___y_751_;
v___y_834_ = v___y_752_;
goto v___jp_830_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_766_);
lean_del_object(v___x_762_);
lean_dec(v_a_756_);
lean_dec_ref(v_args_747_);
lean_dec(v_mvarId_745_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_dec(v___x_746_);
v___y_831_ = v___y_749_;
v___y_832_ = v___y_750_;
v___y_833_ = v___y_751_;
v___y_834_ = v___y_752_;
goto v___jp_830_;
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_766_);
lean_del_object(v___x_762_);
lean_dec(v_a_756_);
lean_dec_ref(v_args_747_);
lean_dec(v___x_746_);
lean_dec(v_mvarId_745_);
v_a_858_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_842_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_842_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
v___jp_767_:
{
uint8_t v___x_775_; 
v___x_775_ = lean_bool_not(v___y_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_781_; 
v___x_776_ = 1;
v___x_777_ = lean_box(v___x_775_);
v___x_778_ = lean_box(v___x_776_);
v___f_779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_779_, 0, v_args_747_);
lean_closure_set(v___f_779_, 1, v___x_764_);
lean_closure_set(v___f_779_, 2, v___x_777_);
lean_closure_set(v___f_779_, 3, v___x_778_);
lean_inc(v___y_773_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 1);
lean_ctor_set(v___x_762_, 0, v___y_773_);
v___x_781_ = v___x_762_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___y_773_);
v___x_781_ = v_reuseFailAlloc_813_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_a_766_, v___x_781_, v___f_779_, v___x_775_, v___x_775_, v___y_769_, v___y_768_, v___y_772_, v___y_771_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v___x_786_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v_fst_784_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_fst_784_);
v_snd_785_ = lean_ctor_get(v_a_783_, 1);
lean_inc(v_snd_785_);
lean_dec(v_a_783_);
v___x_786_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_785_, v_a_756_, v___y_769_, v___y_768_, v___y_772_, v___y_771_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_n(v_a_787_, 2);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = l_Lean_mkAppN(v_a_787_, v___y_770_);
lean_dec_ref(v___y_770_);
lean_inc(v_fst_784_);
v___x_789_ = lean_array_mk(v_fst_784_);
v___x_790_ = l_Lean_mkAppN(v___x_788_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(v_mvarId_745_, v___x_790_, v___y_768_);
lean_dec_ref(v___x_791_);
v___x_792_ = l_Lean_Expr_mvarId_x21(v_a_787_);
lean_dec(v_a_787_);
v___x_793_ = l_List_lengthTR___redArg(v_fst_784_);
lean_dec(v_fst_784_);
v___x_794_ = lean_nat_add(v___y_773_, v___x_793_);
lean_dec(v___x_793_);
lean_dec(v___y_773_);
v___x_795_ = lean_box(0);
v___x_796_ = l_Lean_Meta_introNCore(v___x_792_, v___x_794_, v___x_795_, v___x_775_, v___x_776_, v___y_769_, v___y_768_, v___y_772_, v___y_771_);
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_fst_784_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_770_);
lean_dec(v_mvarId_745_);
v_a_797_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_786_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_786_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v___y_773_);
lean_dec_ref(v___y_770_);
lean_dec(v_a_756_);
lean_dec(v_mvarId_745_);
v_a_805_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_782_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_782_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
else
{
lean_object* v___x_814_; 
lean_del_object(v___x_762_);
lean_dec_ref(v_args_747_);
v___x_814_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_766_, v_a_756_, v___y_769_, v___y_768_, v___y_772_, v___y_771_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc_n(v_a_815_, 2);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = l_Lean_mkAppN(v_a_815_, v___y_770_);
lean_dec_ref(v___y_770_);
v___x_817_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(v_mvarId_745_, v___x_816_, v___y_768_);
lean_dec_ref(v___x_817_);
v___x_818_ = l_Lean_Expr_mvarId_x21(v_a_815_);
lean_dec(v_a_815_);
v___x_819_ = lean_box(0);
v___x_820_ = 0;
v___x_821_ = l_Lean_Meta_introNCore(v___x_818_, v___y_773_, v___x_819_, v___x_820_, v___x_775_, v___y_769_, v___y_768_, v___y_772_, v___y_771_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v___y_773_);
lean_dec_ref(v___y_770_);
lean_dec(v_mvarId_745_);
v_a_822_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_814_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_814_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
v___jp_830_:
{
size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_sz_835_ = lean_array_size(v_args_747_);
v___x_836_ = ((size_t)0ULL);
lean_inc_ref(v_args_747_);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_835_, v___x_836_, v_args_747_);
v___x_838_ = lean_array_get_size(v_args_747_);
v___x_839_ = lean_nat_dec_lt(v___x_764_, v___x_838_);
if (v___x_839_ == 0)
{
v___y_768_ = v___y_832_;
v___y_769_ = v___y_831_;
v___y_770_ = v___x_837_;
v___y_771_ = v___y_834_;
v___y_772_ = v___y_833_;
v___y_773_ = v___x_838_;
v___y_774_ = v___x_839_;
goto v___jp_767_;
}
else
{
if (v___x_839_ == 0)
{
v___y_768_ = v___y_832_;
v___y_769_ = v___y_831_;
v___y_770_ = v___x_837_;
v___y_771_ = v___y_834_;
v___y_772_ = v___y_833_;
v___y_773_ = v___x_838_;
v___y_774_ = v___x_839_;
goto v___jp_767_;
}
else
{
size_t v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_usize_of_nat(v___x_838_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_args_747_, v___x_836_, v___x_840_);
v___y_768_ = v___y_832_;
v___y_769_ = v___y_831_;
v___y_770_ = v___x_837_;
v___y_771_ = v___y_834_;
v___y_772_ = v___y_833_;
v___y_773_ = v___x_838_;
v___y_774_ = v___x_841_;
goto v___jp_767_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_del_object(v___x_762_);
lean_dec(v_a_756_);
lean_dec_ref(v_args_747_);
lean_dec(v___x_746_);
lean_dec(v_mvarId_745_);
v_a_866_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_765_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_765_);
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
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_756_);
lean_dec_ref(v_args_747_);
lean_dec(v___x_746_);
lean_dec(v_mvarId_745_);
v_a_875_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_757_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_757_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_args_747_);
lean_dec(v___x_746_);
lean_dec(v_mvarId_745_);
v_a_883_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_755_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_755_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_args_747_);
lean_dec(v___x_746_);
lean_dec(v_mvarId_745_);
v_a_891_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_754_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_754_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_899_, lean_object* v___x_900_, lean_object* v_args_901_, lean_object* v_transparency_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v_transparency_boxed_908_; lean_object* v_res_909_; 
v_transparency_boxed_908_ = lean_unbox(v_transparency_902_);
v_res_909_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_899_, v___x_900_, v_args_901_, v_transparency_boxed_908_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_913_, lean_object* v_args_914_, uint8_t v_transparency_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_922_ = lean_box(v_transparency_915_);
lean_inc(v_mvarId_913_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_923_, 0, v_mvarId_913_);
lean_closure_set(v___f_923_, 1, v___x_921_);
lean_closure_set(v___f_923_, 2, v_args_914_);
lean_closure_set(v___f_923_, 3, v___x_922_);
v___x_924_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_913_, v___f_923_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_925_, lean_object* v_args_926_, lean_object* v_transparency_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_transparency_boxed_933_; lean_object* v_res_934_; 
v_transparency_boxed_933_ = lean_unbox(v_transparency_927_);
v_res_934_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_925_, v_args_926_, v_transparency_boxed_933_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_mvarId_935_, lean_object* v_val_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___redArg(v_mvarId_935_, v_val_936_, v___y_938_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_mvarId_943_, lean_object* v_val_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_mvarId_943_, v_val_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2___redArg(v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, size_t v_x_958_, size_t v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___redArg(v_x_957_, v_x_958_, v_x_959_, v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
size_t v_x_5284__boxed_969_; size_t v_x_5285__boxed_970_; lean_object* v_res_971_; 
v_x_5284__boxed_969_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_x_5285__boxed_970_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_res_971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4(v_00_u03b2_963_, v_x_964_, v_x_5284__boxed_969_, v_x_5285__boxed_970_, v_x_967_, v_x_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_972_, lean_object* v_n_973_, lean_object* v_k_974_, lean_object* v_v_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6___redArg(v_n_973_, v_k_974_, v_v_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_977_, size_t v_depth_978_, lean_object* v_keys_979_, lean_object* v_vals_980_, lean_object* v_heq_981_, lean_object* v_i_982_, lean_object* v_entries_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___redArg(v_depth_978_, v_keys_979_, v_vals_980_, v_i_982_, v_entries_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_985_, lean_object* v_depth_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_entries_991_){
_start:
{
size_t v_depth_boxed_992_; lean_object* v_res_993_; 
v_depth_boxed_992_ = lean_unbox_usize(v_depth_986_);
lean_dec(v_depth_986_);
v_res_993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_985_, v_depth_boxed_992_, v_keys_987_, v_vals_988_, v_heq_989_, v_i_990_, v_entries_991_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_spec__2_spec__4_spec__6_spec__7___redArg(v_x_995_, v_x_996_, v_x_997_, v_x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_1000_, lean_object* v_args_1001_, uint8_t v_transparency_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1000_, v_args_1001_, v_transparency_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_1009_, lean_object* v_args_1010_, lean_object* v_transparency_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
uint8_t v_transparency_boxed_1017_; lean_object* v_res_1018_; 
v_transparency_boxed_1017_ = lean_unbox(v_transparency_1011_);
v_res_1018_ = l_Lean_MVarId_generalize(v_mvarId_1009_, v_args_1010_, v_transparency_boxed_1017_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1019_, size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_b_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1023_ == 0)
{
return v_b_1022_;
}
else
{
lean_object* v_snd_1024_; lean_object* v_fst_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1058_; 
v_snd_1024_ = lean_ctor_get(v_b_1022_, 1);
v_fst_1025_ = lean_ctor_get(v_b_1022_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_b_1022_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1027_ = v_b_1022_;
v_isShared_1028_ = v_isSharedCheck_1058_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snd_1024_);
lean_inc(v_fst_1025_);
lean_dec(v_b_1022_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1058_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_array_1029_; lean_object* v_start_1030_; lean_object* v_stop_1031_; uint8_t v___x_1032_; 
v_array_1029_ = lean_ctor_get(v_snd_1024_, 0);
v_start_1030_ = lean_ctor_get(v_snd_1024_, 1);
v_stop_1031_ = lean_ctor_get(v_snd_1024_, 2);
v___x_1032_ = lean_nat_dec_lt(v_start_1030_, v_stop_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1034_; 
if (v_isShared_1028_ == 0)
{
v___x_1034_ = v___x_1027_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_fst_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_snd_1024_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1054_; 
lean_inc(v_stop_1031_);
lean_inc(v_start_1030_);
lean_inc_ref(v_array_1029_);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_snd_1024_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; lean_object* v_unused_1056_; lean_object* v_unused_1057_; 
v_unused_1055_ = lean_ctor_get(v_snd_1024_, 2);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_snd_1024_, 1);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_snd_1024_, 0);
lean_dec(v_unused_1057_);
v___x_1037_ = v_snd_1024_;
v_isShared_1038_ = v_isSharedCheck_1054_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_snd_1024_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1054_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_a_1039_ = lean_array_uget_borrowed(v_as_1019_, v_i_1021_);
v___x_1040_ = lean_array_fget(v_array_1029_, v_start_1030_);
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = lean_nat_add(v_start_1030_, v___x_1041_);
lean_dec(v_start_1030_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1042_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_array_1029_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_stop_1031_);
v___x_1044_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = l_Lean_mkFVar(v___x_1040_);
lean_inc(v_a_1039_);
v___x_1046_ = l_Lean_Meta_FVarSubst_insert(v_fst_1025_, v_a_1039_, v___x_1045_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v___x_1044_);
lean_ctor_set(v___x_1027_, 0, v___x_1046_);
v___x_1048_ = v___x_1027_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1044_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
size_t v___x_1049_; size_t v___x_1050_; 
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_add(v_i_1021_, v___x_1049_);
v_i_1021_ = v___x_1050_;
v_b_1022_ = v___x_1048_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1059_, lean_object* v_sz_1060_, lean_object* v_i_1061_, lean_object* v_b_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1059_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1062_);
lean_dec_ref(v_as_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1066_, size_t v_i_1067_, lean_object* v_bs_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1067_, v_sz_1066_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_bs_1068_);
return v___x_1072_;
}
else
{
lean_object* v_v_1073_; lean_object* v_expr_1074_; lean_object* v_xName_x3f_1075_; lean_object* v_hName_x3f_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1099_; 
v_v_1073_ = lean_array_uget(v_bs_1068_, v_i_1067_);
v_expr_1074_ = lean_ctor_get(v_v_1073_, 0);
v_xName_x3f_1075_ = lean_ctor_get(v_v_1073_, 1);
v_hName_x3f_1076_ = lean_ctor_get(v_v_1073_, 2);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_v_1073_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1078_ = v_v_1073_;
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_hName_x3f_1076_);
lean_inc(v_xName_x3f_1075_);
lean_inc(v_expr_1074_);
lean_dec(v_v_1073_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1074_, v___y_1069_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v_bs_x27_1083_; lean_object* v___x_1085_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = lean_unsigned_to_nat(0u);
v_bs_x27_1083_ = lean_array_uset(v_bs_1068_, v_i_1067_, v___x_1082_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_a_1081_);
v___x_1085_ = v___x_1078_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_xName_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_hName_x3f_1076_);
v___x_1085_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1067_, v___x_1086_);
v___x_1088_ = lean_array_uset(v_bs_x27_1083_, v_i_1067_, v___x_1085_);
v_i_1067_ = v___x_1087_;
v_bs_1068_ = v___x_1088_;
goto _start;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_del_object(v___x_1078_);
lean_dec(v_hName_x3f_1076_);
lean_dec(v_xName_x3f_1075_);
lean_dec_ref(v_bs_1068_);
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1080_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1080_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_bs_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
size_t v_sz_boxed_1105_; size_t v_i_boxed_1106_; lean_object* v_res_1107_; 
v_sz_boxed_1105_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1106_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1105_, v_i_boxed_1106_, v_bs_1102_, v___y_1103_);
lean_dec(v___y_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1108_, lean_object* v_a_1109_, lean_object* v_as_1110_, size_t v_i_1111_, size_t v_stop_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_usize_dec_eq(v_i_1111_, v_stop_1112_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v_expr_1120_; lean_object* v___x_1121_; uint8_t v_foApprox_1122_; uint8_t v_ctxApprox_1123_; uint8_t v_quasiPatternApprox_1124_; uint8_t v_constApprox_1125_; uint8_t v_isDefEqStuckEx_1126_; uint8_t v_unificationHints_1127_; uint8_t v_proofIrrelevance_1128_; uint8_t v_assignSyntheticOpaque_1129_; uint8_t v_offsetCnstrs_1130_; uint8_t v_etaStruct_1131_; uint8_t v_univApprox_1132_; uint8_t v_iota_1133_; uint8_t v_beta_1134_; uint8_t v_proj_1135_; uint8_t v_zeta_1136_; uint8_t v_zetaDelta_1137_; uint8_t v_zetaUnused_1138_; uint8_t v_zetaHave_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1187_; 
v___x_1119_ = lean_array_uget_borrowed(v_as_1110_, v_i_1111_);
v_expr_1120_ = lean_ctor_get(v___x_1119_, 0);
v___x_1121_ = l_Lean_Meta_Context_config(v___y_1113_);
v_foApprox_1122_ = lean_ctor_get_uint8(v___x_1121_, 0);
v_ctxApprox_1123_ = lean_ctor_get_uint8(v___x_1121_, 1);
v_quasiPatternApprox_1124_ = lean_ctor_get_uint8(v___x_1121_, 2);
v_constApprox_1125_ = lean_ctor_get_uint8(v___x_1121_, 3);
v_isDefEqStuckEx_1126_ = lean_ctor_get_uint8(v___x_1121_, 4);
v_unificationHints_1127_ = lean_ctor_get_uint8(v___x_1121_, 5);
v_proofIrrelevance_1128_ = lean_ctor_get_uint8(v___x_1121_, 6);
v_assignSyntheticOpaque_1129_ = lean_ctor_get_uint8(v___x_1121_, 7);
v_offsetCnstrs_1130_ = lean_ctor_get_uint8(v___x_1121_, 8);
v_etaStruct_1131_ = lean_ctor_get_uint8(v___x_1121_, 10);
v_univApprox_1132_ = lean_ctor_get_uint8(v___x_1121_, 11);
v_iota_1133_ = lean_ctor_get_uint8(v___x_1121_, 12);
v_beta_1134_ = lean_ctor_get_uint8(v___x_1121_, 13);
v_proj_1135_ = lean_ctor_get_uint8(v___x_1121_, 14);
v_zeta_1136_ = lean_ctor_get_uint8(v___x_1121_, 15);
v_zetaDelta_1137_ = lean_ctor_get_uint8(v___x_1121_, 16);
v_zetaUnused_1138_ = lean_ctor_get_uint8(v___x_1121_, 17);
v_zetaHave_1139_ = lean_ctor_get_uint8(v___x_1121_, 18);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1141_ = v___x_1121_;
v_isShared_1142_ = v_isSharedCheck_1187_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1121_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1187_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v_trackZetaDelta_1143_; lean_object* v_zetaDeltaSet_1144_; lean_object* v_lctx_1145_; lean_object* v_localInstances_1146_; lean_object* v_defEqCtx_x3f_1147_; lean_object* v_synthPendingDepth_1148_; lean_object* v_canUnfold_x3f_1149_; uint8_t v_univApprox_1150_; uint8_t v_inTypeClassResolution_1151_; uint8_t v_cacheInferType_1152_; lean_object* v_config_1154_; 
v_trackZetaDelta_1143_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*7);
v_zetaDeltaSet_1144_ = lean_ctor_get(v___y_1113_, 1);
v_lctx_1145_ = lean_ctor_get(v___y_1113_, 2);
v_localInstances_1146_ = lean_ctor_get(v___y_1113_, 3);
v_defEqCtx_x3f_1147_ = lean_ctor_get(v___y_1113_, 4);
v_synthPendingDepth_1148_ = lean_ctor_get(v___y_1113_, 5);
v_canUnfold_x3f_1149_ = lean_ctor_get(v___y_1113_, 6);
v_univApprox_1150_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1151_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*7 + 2);
v_cacheInferType_1152_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*7 + 3);
if (v_isShared_1142_ == 0)
{
v_config_1154_ = v___x_1141_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 0, v_foApprox_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 1, v_ctxApprox_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 2, v_quasiPatternApprox_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 3, v_constApprox_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 4, v_isDefEqStuckEx_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 5, v_unificationHints_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 6, v_proofIrrelevance_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 7, v_assignSyntheticOpaque_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 8, v_offsetCnstrs_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 10, v_etaStruct_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 11, v_univApprox_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 12, v_iota_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 13, v_beta_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 14, v_proj_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 15, v_zeta_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 16, v_zetaDelta_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 17, v_zetaUnused_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, 18, v_zetaHave_1139_);
v_config_1154_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; lean_object* v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v_key_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_ctor_set_uint8(v_config_1154_, 9, v_transparency_1108_);
v___x_1155_ = l_Lean_Meta_Context_configKey(v___y_1113_);
v___x_1156_ = 3ULL;
v___x_1157_ = lean_uint64_shift_right(v___x_1155_, v___x_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_uint64_shift_left(v___x_1157_, v___x_1156_);
v___x_1160_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1108_);
v_key_1161_ = lean_uint64_lor(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1162_, 0, v_config_1154_);
lean_ctor_set_uint64(v___x_1162_, sizeof(void*)*1, v_key_1161_);
lean_inc(v_canUnfold_x3f_1149_);
lean_inc(v_synthPendingDepth_1148_);
lean_inc(v_defEqCtx_x3f_1147_);
lean_inc_ref(v_localInstances_1146_);
lean_inc_ref(v_lctx_1145_);
lean_inc(v_zetaDeltaSet_1144_);
v___x_1163_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_zetaDeltaSet_1144_);
lean_ctor_set(v___x_1163_, 2, v_lctx_1145_);
lean_ctor_set(v___x_1163_, 3, v_localInstances_1146_);
lean_ctor_set(v___x_1163_, 4, v_defEqCtx_x3f_1147_);
lean_ctor_set(v___x_1163_, 5, v_synthPendingDepth_1148_);
lean_ctor_set(v___x_1163_, 6, v_canUnfold_x3f_1149_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*7, v_trackZetaDelta_1143_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*7 + 1, v_univApprox_1150_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1151_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*7 + 3, v_cacheInferType_1152_);
lean_inc_ref(v_expr_1120_);
lean_inc_ref(v_a_1109_);
v___x_1164_ = l_Lean_Meta_kabstract(v_a_1109_, v_expr_1120_, v___x_1158_, v___x_1163_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref_known(v___x_1163_, 7);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1177_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; 
v___x_1169_ = l_Lean_Expr_hasLooseBVars(v_a_1165_);
lean_dec(v_a_1165_);
if (v___x_1169_ == 0)
{
size_t v___x_1170_; size_t v___x_1171_; 
lean_del_object(v___x_1167_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1111_, v___x_1170_);
v_i_1111_ = v___x_1171_;
goto _start;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec_ref(v_a_1109_);
v___x_1173_ = lean_box(v___x_1169_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1173_);
v___x_1175_ = v___x_1167_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_a_1109_);
v_a_1178_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1164_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1164_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
else
{
uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec_ref(v_a_1109_);
v___x_1188_ = 0;
v___x_1189_ = lean_box(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1191_, lean_object* v_a_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v_transparency_boxed_1201_; size_t v_i_boxed_1202_; size_t v_stop_boxed_1203_; lean_object* v_res_1204_; 
v_transparency_boxed_1201_ = lean_unbox(v_transparency_1191_);
v_i_boxed_1202_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1203_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1201_, v_a_1192_, v_as_1193_, v_i_boxed_1202_, v_stop_boxed_1203_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_as_1193_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1205_, lean_object* v___x_1206_, uint8_t v_transparency_1207_, lean_object* v_as_1208_, size_t v_i_1209_, size_t v_stop_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_a_1218_; uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_eq(v_i_1209_, v_stop_1210_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; uint8_t v_a_1225_; lean_object* v___x_1227_; 
v___x_1223_ = lean_array_uget_borrowed(v_as_1208_, v_i_1209_);
lean_inc(v___x_1223_);
v___x_1227_ = l_Lean_FVarId_getType___redArg(v___x_1223_, v___y_1212_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1228_, v___y_1213_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_nat_dec_eq(v___x_1206_, v___x_1231_);
v___x_1233_ = lean_array_get_size(v_a_1205_);
v___x_1234_ = lean_nat_dec_lt(v___x_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_a_1230_);
v_a_1225_ = v___x_1232_;
goto v___jp_1224_;
}
else
{
if (v___x_1234_ == 0)
{
lean_dec(v_a_1230_);
v_a_1225_ = v___x_1232_;
goto v___jp_1224_;
}
else
{
size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = ((size_t)0ULL);
v___x_1236_ = lean_usize_of_nat(v___x_1233_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1207_, v_a_1230_, v_a_1205_, v___x_1235_, v___x_1236_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; uint8_t v___x_1239_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = lean_unbox(v_a_1238_);
lean_dec(v_a_1238_);
v_a_1225_ = v___x_1239_;
goto v___jp_1224_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_b_1211_);
v_a_1240_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1237_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1237_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_b_1211_);
v_a_1248_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1229_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1229_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_b_1211_);
v_a_1256_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1227_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1227_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
v___jp_1224_:
{
if (v_a_1225_ == 0)
{
v_a_1218_ = v_b_1211_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1226_; 
lean_inc(v___x_1223_);
v___x_1226_ = lean_array_push(v_b_1211_, v___x_1223_);
v_a_1218_ = v___x_1226_;
goto v___jp_1217_;
}
}
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1211_);
return v___x_1264_;
}
v___jp_1217_:
{
size_t v___x_1219_; size_t v___x_1220_; 
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_i_1209_, v___x_1219_);
v_i_1209_ = v___x_1220_;
v_b_1211_ = v_a_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1265_, lean_object* v___x_1266_, lean_object* v_transparency_1267_, lean_object* v_as_1268_, lean_object* v_i_1269_, lean_object* v_stop_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v_transparency_boxed_1277_; size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_transparency_boxed_1277_ = lean_unbox(v_transparency_1267_);
v_i_boxed_1278_ = lean_unbox_usize(v_i_1269_);
lean_dec(v_i_1269_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1270_);
lean_dec(v_stop_1270_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1265_, v___x_1266_, v_transparency_boxed_1277_, v_as_1268_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_as_1268_);
lean_dec(v___x_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1281_, lean_object* v_a_1282_, lean_object* v___x_1283_, lean_object* v_as_1284_, size_t v_i_1285_, size_t v_stop_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_a_1294_; uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_eq(v_i_1285_, v_stop_1286_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v_a_1301_; lean_object* v___x_1303_; 
v___x_1299_ = lean_array_uget_borrowed(v_as_1284_, v_i_1285_);
lean_inc(v___x_1299_);
v___x_1303_ = l_Lean_FVarId_getType___redArg(v___x_1299_, v___y_1288_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1304_, v___y_1289_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_nat_dec_eq(v___x_1283_, v___x_1307_);
v___x_1309_ = lean_array_get_size(v_a_1282_);
v___x_1310_ = lean_nat_dec_lt(v___x_1307_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v_a_1306_);
v_a_1301_ = v___x_1308_;
goto v___jp_1300_;
}
else
{
if (v___x_1310_ == 0)
{
lean_dec(v_a_1306_);
v_a_1301_ = v___x_1308_;
goto v___jp_1300_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1309_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1281_, v_a_1306_, v_a_1282_, v___x_1311_, v___x_1312_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; uint8_t v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
v_a_1301_ = v___x_1315_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_b_1287_);
v_a_1316_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1313_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1313_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_b_1287_);
v_a_1324_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1305_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1305_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_b_1287_);
v_a_1332_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1303_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1303_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
v___jp_1300_:
{
if (v_a_1301_ == 0)
{
v_a_1294_ = v_b_1287_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1302_; 
lean_inc(v___x_1299_);
v___x_1302_ = lean_array_push(v_b_1287_, v___x_1299_);
v_a_1294_ = v___x_1302_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1287_);
return v___x_1340_;
}
v___jp_1293_:
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1285_, v___x_1295_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1282_, v___x_1283_, v_transparency_1281_, v_as_1284_, v___x_1296_, v_stop_1286_, v_a_1294_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1341_, lean_object* v_a_1342_, lean_object* v___x_1343_, lean_object* v_as_1344_, lean_object* v_i_1345_, lean_object* v_stop_1346_, lean_object* v_b_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_transparency_boxed_1353_; size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_transparency_boxed_1353_ = lean_unbox(v_transparency_1341_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1346_);
lean_dec(v_stop_1346_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1353_, v_a_1342_, v___x_1343_, v_as_1344_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v_as_1344_);
lean_dec(v___x_1343_);
lean_dec_ref(v_a_1342_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1359_, lean_object* v_args_1360_, lean_object* v_hyps_1361_, lean_object* v_fvarSubst_1362_, uint8_t v_transparency_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_array_get_size(v_hyps_1361_);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_nat_dec_eq(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
size_t v_sz_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v_sz_1372_ = lean_array_size(v_args_1360_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1372_, v___x_1373_, v_args_1360_, v_a_1365_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; uint8_t v___x_1376_; lean_object* v_a_1378_; lean_object* v___y_1452_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = 1;
v___x_1462_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1463_ = lean_nat_dec_lt(v___x_1370_, v___x_1369_);
if (v___x_1463_ == 0)
{
v_a_1378_ = v___x_1462_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_le(v___x_1369_, v___x_1369_);
if (v___x_1464_ == 0)
{
if (v___x_1463_ == 0)
{
v_a_1378_ = v___x_1462_;
goto v___jp_1377_;
}
else
{
size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_usize_of_nat(v___x_1369_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1363_, v_a_1375_, v___x_1369_, v_hyps_1361_, v___x_1373_, v___x_1465_, v___x_1462_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1452_ = v___x_1466_;
goto v___jp_1451_;
}
}
else
{
size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_usize_of_nat(v___x_1369_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1363_, v_a_1375_, v___x_1369_, v_hyps_1361_, v___x_1373_, v___x_1467_, v___x_1462_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1452_ = v___x_1468_;
goto v___jp_1451_;
}
}
v___jp_1377_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_MVarId_revert(v_mvarId_1359_, v_a_1378_, v___x_1376_, v___x_1371_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___x_1383_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v_fst_1381_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_fst_1381_);
v_snd_1382_ = lean_ctor_get(v_a_1380_, 1);
lean_inc(v_snd_1382_);
lean_dec(v_a_1380_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1382_, v_a_1375_, v_transparency_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1434_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v_fst_1385_ = lean_ctor_get(v_a_1384_, 0);
v_snd_1386_ = lean_ctor_get(v_a_1384_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_a_1384_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1388_ = v_a_1384_;
v_isShared_1389_ = v_isSharedCheck_1434_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snd_1386_);
lean_inc(v_fst_1385_);
lean_dec(v_a_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1434_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_array_get_size(v_fst_1381_);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Lean_Meta_introNCore(v_snd_1386_, v___x_1390_, v___x_1391_, v___x_1371_, v___x_1376_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1425_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1425_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1425_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1424_; 
v_fst_1397_ = lean_ctor_get(v_a_1393_, 0);
v_snd_1398_ = lean_ctor_get(v_a_1393_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_a_1393_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1400_ = v_a_1393_;
v_isShared_1401_ = v_isSharedCheck_1424_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_inc(v_fst_1397_);
lean_dec(v_a_1393_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1424_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1402_ = lean_array_get_size(v_fst_1397_);
v___x_1403_ = l_Array_toSubarray___redArg(v_fst_1397_, v___x_1370_, v___x_1402_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1403_);
lean_ctor_set(v___x_1400_, 0, v_fvarSubst_1362_);
v___x_1405_ = v___x_1400_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fvarSubst_1362_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
size_t v_sz_1406_; lean_object* v___x_1407_; lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_sz_1406_ = lean_array_size(v_fst_1381_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1381_, v_sz_1406_, v___x_1373_, v___x_1405_);
lean_dec(v_fst_1381_);
v_fst_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1407_, 1);
lean_dec(v_unused_1422_);
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_fst_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_snd_1398_);
lean_ctor_set(v___x_1410_, 0, v_fst_1385_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_fst_1385_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_snd_1398_);
v___x_1413_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1413_);
lean_ctor_set(v___x_1388_, 0, v_fst_1408_);
v___x_1415_ = v___x_1388_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_fst_1408_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1415_);
v___x_1417_ = v___x_1395_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
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
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_del_object(v___x_1388_);
lean_dec(v_fst_1385_);
lean_dec(v_fst_1381_);
lean_dec(v_fvarSubst_1362_);
v_a_1426_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1392_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1392_);
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
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_fst_1381_);
lean_dec(v_fvarSubst_1362_);
v_a_1435_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1383_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1383_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1375_);
lean_dec(v_fvarSubst_1362_);
v_a_1443_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1379_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1379_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
v___jp_1451_:
{
if (lean_obj_tag(v___y_1452_) == 0)
{
lean_object* v_a_1453_; 
v_a_1453_ = lean_ctor_get(v___y_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___y_1452_, 1);
v_a_1378_ = v_a_1453_;
goto v___jp_1377_;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1375_);
lean_dec(v_fvarSubst_1362_);
lean_dec(v_mvarId_1359_);
v_a_1454_ = lean_ctor_get(v___y_1452_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___y_1452_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___y_1452_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___y_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_fvarSubst_1362_);
lean_dec(v_mvarId_1359_);
v_a_1469_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1374_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1374_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1359_, v_args_1360_, v_transparency_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_fvarSubst_1362_);
lean_ctor_set(v___x_1482_, 1, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_fvarSubst_1362_);
v_a_1487_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1477_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1477_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1495_, lean_object* v_args_1496_, lean_object* v_hyps_1497_, lean_object* v_fvarSubst_1498_, lean_object* v_transparency_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
uint8_t v_transparency_boxed_1505_; lean_object* v_res_1506_; 
v_transparency_boxed_1505_ = lean_unbox(v_transparency_1499_);
v_res_1506_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1495_, v_args_1496_, v_hyps_1497_, v_fvarSubst_1498_, v_transparency_boxed_1505_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec_ref(v_hyps_1497_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1507_, size_t v_i_1508_, lean_object* v_bs_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1507_, v_i_1508_, v_bs_1509_, v___y_1511_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1516_, lean_object* v_i_1517_, lean_object* v_bs_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1524_, v_i_boxed_1525_, v_bs_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1526_;
}
}
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedGeneralizeArg_default = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default);
l_Lean_Meta_instInhabitedGeneralizeArg = _init_l_Lean_Meta_instInhabitedGeneralizeArg();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Generalize(builtin);
}
#ifdef __cplusplus
}
#endif
