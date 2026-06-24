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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_15_; 
v___x_15_ = l_Lean_Expr_hasMVar(v_e_12_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v_e_12_);
return v___x_16_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_37_, v___y_38_);
lean_dec(v___y_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_41_, v___y_43_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object* v_e_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(v_e_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object* v_args_58_, uint8_t v_transparency_59_, lean_object* v_target_60_, lean_object* v_i_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_get_size(v_args_58_);
v___x_68_ = lean_nat_dec_lt(v_i_61_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v_target_60_);
return v___x_69_;
}
else
{
lean_object* v_arg_70_; lean_object* v_expr_71_; lean_object* v_xName_x3f_72_; lean_object* v___x_73_; 
v_arg_70_ = lean_array_fget_borrowed(v_args_58_, v_i_61_);
v_expr_71_ = lean_ctor_get(v_arg_70_, 0);
v_xName_x3f_72_ = lean_ctor_get(v_arg_70_, 1);
lean_inc_ref(v_expr_71_);
v___x_73_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_71_, v_a_63_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_75_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_n(v_a_74_, 2);
lean_dec_ref_known(v___x_73_, 1);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
v___x_75_ = lean_infer_type(v_a_74_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_75_, 1);
v___x_77_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_76_, v_a_63_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_i_61_, v___x_79_);
v___x_81_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_58_, v_transparency_59_, v_target_60_, v___x_80_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v_xName_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
if (lean_obj_tag(v_xName_x3f_72_) == 1)
{
lean_object* v_val_145_; 
v_val_145_ = lean_ctor_get(v_xName_x3f_72_, 0);
lean_inc(v_val_145_);
v_xName_84_ = v_val_145_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
v___x_147_ = l_Lean_Core_mkFreshUserName(v___x_146_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v_xName_84_ = v_a_148_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec(v_a_82_);
lean_dec(v_a_78_);
lean_dec(v_a_74_);
v_a_149_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_147_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
v___jp_83_:
{
lean_object* v___x_89_; uint8_t v_foApprox_90_; uint8_t v_ctxApprox_91_; uint8_t v_quasiPatternApprox_92_; uint8_t v_constApprox_93_; uint8_t v_isDefEqStuckEx_94_; uint8_t v_unificationHints_95_; uint8_t v_proofIrrelevance_96_; uint8_t v_assignSyntheticOpaque_97_; uint8_t v_offsetCnstrs_98_; uint8_t v_etaStruct_99_; uint8_t v_univApprox_100_; uint8_t v_iota_101_; uint8_t v_beta_102_; uint8_t v_proj_103_; uint8_t v_zeta_104_; uint8_t v_zetaDelta_105_; uint8_t v_zetaUnused_106_; uint8_t v_zetaHave_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_144_; 
v___x_89_ = l_Lean_Meta_Context_config(v___y_85_);
v_foApprox_90_ = lean_ctor_get_uint8(v___x_89_, 0);
v_ctxApprox_91_ = lean_ctor_get_uint8(v___x_89_, 1);
v_quasiPatternApprox_92_ = lean_ctor_get_uint8(v___x_89_, 2);
v_constApprox_93_ = lean_ctor_get_uint8(v___x_89_, 3);
v_isDefEqStuckEx_94_ = lean_ctor_get_uint8(v___x_89_, 4);
v_unificationHints_95_ = lean_ctor_get_uint8(v___x_89_, 5);
v_proofIrrelevance_96_ = lean_ctor_get_uint8(v___x_89_, 6);
v_assignSyntheticOpaque_97_ = lean_ctor_get_uint8(v___x_89_, 7);
v_offsetCnstrs_98_ = lean_ctor_get_uint8(v___x_89_, 8);
v_etaStruct_99_ = lean_ctor_get_uint8(v___x_89_, 10);
v_univApprox_100_ = lean_ctor_get_uint8(v___x_89_, 11);
v_iota_101_ = lean_ctor_get_uint8(v___x_89_, 12);
v_beta_102_ = lean_ctor_get_uint8(v___x_89_, 13);
v_proj_103_ = lean_ctor_get_uint8(v___x_89_, 14);
v_zeta_104_ = lean_ctor_get_uint8(v___x_89_, 15);
v_zetaDelta_105_ = lean_ctor_get_uint8(v___x_89_, 16);
v_zetaUnused_106_ = lean_ctor_get_uint8(v___x_89_, 17);
v_zetaHave_107_ = lean_ctor_get_uint8(v___x_89_, 18);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_144_ == 0)
{
v___x_109_ = v___x_89_;
v_isShared_110_ = v_isSharedCheck_144_;
goto v_resetjp_108_;
}
else
{
lean_dec(v___x_89_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_144_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v_trackZetaDelta_111_; lean_object* v_zetaDeltaSet_112_; lean_object* v_lctx_113_; lean_object* v_localInstances_114_; lean_object* v_defEqCtx_x3f_115_; lean_object* v_synthPendingDepth_116_; lean_object* v_canUnfold_x3f_117_; uint8_t v_univApprox_118_; uint8_t v_inTypeClassResolution_119_; uint8_t v_cacheInferType_120_; lean_object* v_config_122_; 
v_trackZetaDelta_111_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7);
v_zetaDeltaSet_112_ = lean_ctor_get(v___y_85_, 1);
v_lctx_113_ = lean_ctor_get(v___y_85_, 2);
v_localInstances_114_ = lean_ctor_get(v___y_85_, 3);
v_defEqCtx_x3f_115_ = lean_ctor_get(v___y_85_, 4);
v_synthPendingDepth_116_ = lean_ctor_get(v___y_85_, 5);
v_canUnfold_x3f_117_ = lean_ctor_get(v___y_85_, 6);
v_univApprox_118_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_119_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 2);
v_cacheInferType_120_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 3);
if (v_isShared_110_ == 0)
{
v_config_122_ = v___x_109_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 0, v_foApprox_90_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 1, v_ctxApprox_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 2, v_quasiPatternApprox_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 3, v_constApprox_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 4, v_isDefEqStuckEx_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 5, v_unificationHints_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 6, v_proofIrrelevance_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 7, v_assignSyntheticOpaque_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 8, v_offsetCnstrs_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 10, v_etaStruct_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 11, v_univApprox_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 12, v_iota_101_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 13, v_beta_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 14, v_proj_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 15, v_zeta_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 16, v_zetaDelta_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 17, v_zetaUnused_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, 18, v_zetaHave_107_);
v_config_122_ = v_reuseFailAlloc_143_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; lean_object* v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_key_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_ctor_set_uint8(v_config_122_, 9, v_transparency_59_);
v___x_123_ = l_Lean_Meta_Context_configKey(v___y_85_);
v___x_124_ = 3ULL;
v___x_125_ = lean_uint64_shift_right(v___x_123_, v___x_124_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_uint64_shift_left(v___x_125_, v___x_124_);
v___x_128_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_59_);
v_key_129_ = lean_uint64_lor(v___x_127_, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_130_, 0, v_config_122_);
lean_ctor_set_uint64(v___x_130_, sizeof(void*)*1, v_key_129_);
lean_inc(v_canUnfold_x3f_117_);
lean_inc(v_synthPendingDepth_116_);
lean_inc(v_defEqCtx_x3f_115_);
lean_inc_ref(v_localInstances_114_);
lean_inc_ref(v_lctx_113_);
lean_inc(v_zetaDeltaSet_112_);
v___x_131_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_zetaDeltaSet_112_);
lean_ctor_set(v___x_131_, 2, v_lctx_113_);
lean_ctor_set(v___x_131_, 3, v_localInstances_114_);
lean_ctor_set(v___x_131_, 4, v_defEqCtx_x3f_115_);
lean_ctor_set(v___x_131_, 5, v_synthPendingDepth_116_);
lean_ctor_set(v___x_131_, 6, v_canUnfold_x3f_117_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*7, v_trackZetaDelta_111_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*7 + 1, v_univApprox_118_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*7 + 2, v_inTypeClassResolution_119_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*7 + 3, v_cacheInferType_120_);
v___x_132_ = l_Lean_Meta_kabstract(v_a_82_, v_a_74_, v___x_126_, v___x_131_, v___y_86_, v___y_87_, v___y_88_);
lean_dec_ref_known(v___x_131_, 7);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_142_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = 0;
v___x_138_ = l_Lean_mkForall(v_xName_84_, v___x_137_, v_a_78_, v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_dec(v_xName_84_);
lean_dec(v_a_78_);
return v___x_132_;
}
}
}
}
}
else
{
lean_dec(v_a_78_);
lean_dec(v_a_74_);
return v___x_81_;
}
}
else
{
lean_dec(v_a_74_);
lean_dec_ref(v_target_60_);
return v___x_77_;
}
}
else
{
lean_dec(v_a_74_);
lean_dec_ref(v_target_60_);
return v___x_75_;
}
}
else
{
lean_dec_ref(v_target_60_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_157_, lean_object* v_transparency_158_, lean_object* v_target_159_, lean_object* v_i_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_transparency_boxed_166_; lean_object* v_res_167_; 
v_transparency_boxed_166_ = lean_unbox(v_transparency_158_);
v_res_167_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_157_, v_transparency_boxed_166_, v_target_159_, v_i_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_i_160_);
lean_dec_ref(v_args_157_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_168_, lean_object* v_xs_169_, lean_object* v_type_170_, lean_object* v_i_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_array_get_size(v_xs_169_);
v___x_178_ = lean_nat_dec_lt(v_i_171_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_i_171_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_type_170_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v_arg_183_; lean_object* v_hName_x3f_184_; 
v___x_182_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_183_ = lean_array_get_borrowed(v___x_182_, v_args_168_, v_i_171_);
v_hName_x3f_184_ = lean_ctor_get(v_arg_183_, 2);
if (lean_obj_tag(v_hName_x3f_184_) == 1)
{
lean_object* v_expr_185_; lean_object* v_val_186_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_expr_185_ = lean_ctor_get(v_arg_183_, 0);
v_val_186_ = lean_ctor_get(v_hName_x3f_184_, 0);
v___x_217_ = lean_array_fget_borrowed(v_xs_169_, v_i_171_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
lean_inc(v___x_217_);
v___x_218_ = lean_infer_type(v___x_217_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
lean_inc_ref(v_expr_185_);
v___x_220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_185_, v_a_173_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_n(v_a_221_, 2);
lean_dec_ref_known(v___x_220_, 1);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
v___x_222_ = lean_infer_type(v_a_221_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_223_, v_a_173_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l_Lean_Meta_isExprDefEq(v_a_219_, v_a_225_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; uint8_t v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = lean_unbox(v_a_227_);
lean_dec(v_a_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_inc(v___x_217_);
lean_inc(v_a_221_);
v___x_229_ = l_Lean_Meta_mkHEq(v_a_221_, v___x_217_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = l_Lean_Meta_mkHEqRefl(v_a_221_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v_fst_188_ = v_a_230_;
v_snd_189_ = v_a_232_;
v___y_190_ = v_a_172_;
v___y_191_ = v_a_173_;
v___y_192_ = v_a_174_;
v___y_193_ = v_a_175_;
goto v___jp_187_;
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_230_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_221_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_241_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_229_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_229_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
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
else
{
lean_object* v___x_249_; 
lean_inc(v___x_217_);
lean_inc(v_a_221_);
v___x_249_ = l_Lean_Meta_mkEq(v_a_221_, v___x_217_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = l_Lean_Meta_mkEqRefl(v_a_221_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_251_, 1);
v_fst_188_ = v_a_250_;
v_snd_189_ = v_a_252_;
v___y_190_ = v_a_172_;
v___y_191_ = v_a_173_;
v___y_192_ = v_a_174_;
v___y_193_ = v_a_175_;
goto v___jp_187_;
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_250_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_253_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_251_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_251_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_a_221_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_261_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_249_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_249_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_221_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_269_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_226_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_226_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_277_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_224_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_224_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_285_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_222_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_222_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_a_219_);
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_293_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_220_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_220_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_i_171_);
lean_dec_ref(v_type_170_);
v_a_301_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_218_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_218_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
v___jp_187_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_i_171_, v___x_194_);
lean_dec(v_i_171_);
v___x_196_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_168_, v_xs_169_, v_type_170_, v___x_195_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_216_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_216_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_216_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_216_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_215_; 
v_fst_201_ = lean_ctor_get(v_a_197_, 0);
v_snd_202_ = lean_ctor_get(v_a_197_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_a_197_);
if (v_isSharedCheck_215_ == 0)
{
v___x_204_ = v_a_197_;
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_snd_202_);
lean_inc(v_fst_201_);
lean_dec(v_a_197_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v_snd_189_);
lean_ctor_set(v___x_206_, 1, v_fst_201_);
v___x_207_ = 0;
lean_inc(v_val_186_);
v___x_208_ = l_Lean_mkForall(v_val_186_, v___x_207_, v_fst_188_, v_snd_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_208_);
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_210_ = v___x_204_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_210_);
v___x_212_ = v___x_199_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_189_);
lean_dec_ref(v_fst_188_);
return v___x_196_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_i_171_, v___x_309_);
lean_dec(v_i_171_);
v_i_171_ = v___x_310_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_312_, lean_object* v_xs_313_, lean_object* v_type_314_, lean_object* v_i_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_312_, v_xs_313_, v_type_314_, v_i_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_xs_313_);
lean_dec_ref(v_args_312_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* v_k_322_, lean_object* v_b_323_, lean_object* v_c_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
v___x_330_ = lean_apply_7(v_k_322_, v_b_323_, v_c_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* v_k_331_, lean_object* v_b_332_, lean_object* v_c_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_331_, v_b_332_, v_c_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* v_type_340_, lean_object* v_maxFVars_x3f_341_, lean_object* v_k_342_, uint8_t v_cleanupAnnotations_343_, uint8_t v_whnfType_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; 
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_350_, 0, v_k_342_);
v___x_351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_340_, v_maxFVars_x3f_341_, v___f_350_, v_cleanupAnnotations_343_, v_whnfType_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
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
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* v_type_368_, lean_object* v_maxFVars_x3f_369_, lean_object* v_k_370_, lean_object* v_cleanupAnnotations_371_, lean_object* v_whnfType_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_378_; uint8_t v_whnfType_boxed_379_; lean_object* v_res_380_; 
v_cleanupAnnotations_boxed_378_ = lean_unbox(v_cleanupAnnotations_371_);
v_whnfType_boxed_379_ = lean_unbox(v_whnfType_372_);
v_res_380_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_368_, v_maxFVars_x3f_369_, v_k_370_, v_cleanupAnnotations_boxed_378_, v_whnfType_boxed_379_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_00_u03b1_381_, lean_object* v_type_382_, lean_object* v_maxFVars_x3f_383_, lean_object* v_k_384_, uint8_t v_cleanupAnnotations_385_, uint8_t v_whnfType_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_382_, v_maxFVars_x3f_383_, v_k_384_, v_cleanupAnnotations_385_, v_whnfType_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_00_u03b1_393_, lean_object* v_type_394_, lean_object* v_maxFVars_x3f_395_, lean_object* v_k_396_, lean_object* v_cleanupAnnotations_397_, lean_object* v_whnfType_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_404_; uint8_t v_whnfType_boxed_405_; lean_object* v_res_406_; 
v_cleanupAnnotations_boxed_404_ = lean_unbox(v_cleanupAnnotations_397_);
v_whnfType_boxed_405_ = lean_unbox(v_whnfType_398_);
v_res_406_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_393_, v_type_394_, v_maxFVars_x3f_395_, v_k_396_, v_cleanupAnnotations_boxed_404_, v_whnfType_boxed_405_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_407_, lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_407_, v_x_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_414_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_414_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_431_, lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_431_, v_x_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_439_, lean_object* v_mvarId_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_440_, v_x_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_448_, lean_object* v_mvarId_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_448_, v_mvarId_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_457_, lean_object* v___x_458_, uint8_t v___x_459_, uint8_t v___x_460_, lean_object* v_xs_461_, lean_object* v_type_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_457_, v_xs_461_, v_type_462_, v___x_458_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_496_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v_fst_470_ = lean_ctor_get(v_a_469_, 0);
v_snd_471_ = lean_ctor_get(v_a_469_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_496_ == 0)
{
v___x_473_ = v_a_469_;
v_isShared_474_ = v_isSharedCheck_496_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v_a_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_496_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint8_t v___x_475_; lean_object* v___x_476_; 
v___x_475_ = 1;
v___x_476_ = l_Lean_Meta_mkForallFVars(v_xs_461_, v_snd_471_, v___x_459_, v___x_460_, v___x_460_, v___x_475_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_a_477_);
v___x_482_ = v___x_473_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_fst_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_477_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_473_);
lean_dec(v_fst_470_);
v_a_488_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_476_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_476_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_497_, lean_object* v___x_498_, lean_object* v___x_499_, lean_object* v___x_500_, lean_object* v_xs_501_, lean_object* v_type_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_4821__boxed_508_; uint8_t v___x_4822__boxed_509_; lean_object* v_res_510_; 
v___x_4821__boxed_508_ = lean_unbox(v___x_499_);
v___x_4822__boxed_509_ = lean_unbox(v___x_500_);
v_res_510_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_497_, v___x_498_, v___x_4821__boxed_508_, v___x_4822__boxed_509_, v_xs_501_, v_type_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_xs_501_);
lean_dec_ref(v_args_497_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_as_511_, size_t v_i_512_, size_t v_stop_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_512_, v_stop_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v_hName_x3f_516_; uint8_t v___x_517_; 
v___x_515_ = lean_array_uget_borrowed(v_as_511_, v_i_512_);
v_hName_x3f_516_ = lean_ctor_get(v___x_515_, 2);
v___x_517_ = 1;
if (lean_obj_tag(v_hName_x3f_516_) == 0)
{
if (v___x_514_ == 0)
{
size_t v___x_518_; size_t v___x_519_; 
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_512_, v___x_518_);
v_i_512_ = v___x_519_;
goto _start;
}
else
{
return v___x_517_;
}
}
else
{
return v___x_517_;
}
}
else
{
uint8_t v___x_521_; 
v___x_521_ = 0;
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_as_522_, lean_object* v_i_523_, lean_object* v_stop_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; uint8_t v_res_527_; lean_object* v_r_528_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_522_, v_i_boxed_525_, v_stop_boxed_526_);
lean_dec_ref(v_as_522_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_529_, size_t v_i_530_, lean_object* v_bs_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_lt(v_i_530_, v_sz_529_);
if (v___x_532_ == 0)
{
return v_bs_531_;
}
else
{
lean_object* v_v_533_; lean_object* v_expr_534_; lean_object* v___x_535_; lean_object* v_bs_x27_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v_v_533_ = lean_array_uget_borrowed(v_bs_531_, v_i_530_);
v_expr_534_ = lean_ctor_get(v_v_533_, 0);
lean_inc_ref(v_expr_534_);
v___x_535_ = lean_unsigned_to_nat(0u);
v_bs_x27_536_ = lean_array_uset(v_bs_531_, v_i_530_, v___x_535_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_530_, v___x_537_);
v___x_539_ = lean_array_uset(v_bs_x27_536_, v_i_530_, v_expr_534_);
v_i_530_ = v___x_538_;
v_bs_531_ = v___x_539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_bs_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_544_, v_i_boxed_545_, v_bs_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_ks_551_; lean_object* v_vs_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_576_; 
v_ks_551_ = lean_ctor_get(v_x_547_, 0);
v_vs_552_ = lean_ctor_get(v_x_547_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_576_ == 0)
{
v___x_554_ = v_x_547_;
v_isShared_555_ = v_isSharedCheck_576_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_vs_552_);
lean_inc(v_ks_551_);
lean_dec(v_x_547_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_576_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_get_size(v_ks_551_);
v___x_557_ = lean_nat_dec_lt(v_x_548_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec(v_x_548_);
v___x_558_ = lean_array_push(v_ks_551_, v_x_549_);
v___x_559_ = lean_array_push(v_vs_552_, v_x_550_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_559_);
lean_ctor_set(v___x_554_, 0, v___x_558_);
v___x_561_ = v___x_554_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v_k_x27_563_; uint8_t v___x_564_; 
v_k_x27_563_ = lean_array_fget_borrowed(v_ks_551_, v_x_548_);
v___x_564_ = l_Lean_instBEqMVarId_beq(v_x_549_, v_k_x27_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_566_; 
if (v_isShared_555_ == 0)
{
v___x_566_ = v___x_554_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_ks_551_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_vs_552_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_x_548_, v___x_567_);
lean_dec(v_x_548_);
v_x_547_ = v___x_566_;
v_x_548_ = v___x_568_;
goto _start;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_array_fset(v_ks_551_, v_x_548_, v_x_549_);
v___x_572_ = lean_array_fset(v_vs_552_, v_x_548_, v_x_550_);
lean_dec(v_x_548_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_572_);
lean_ctor_set(v___x_554_, 0, v___x_571_);
v___x_574_ = v___x_554_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* v_n_577_, lean_object* v_k_578_, lean_object* v_v_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_577_, v___x_580_, v_k_578_, v_v_579_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_583_, size_t v_x_584_, size_t v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
lean_object* v_es_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v_j_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_es_588_ = lean_ctor_get(v_x_583_, 0);
v___x_589_ = ((size_t)31ULL);
v___x_590_ = lean_usize_land(v_x_584_, v___x_589_);
v_j_591_ = lean_usize_to_nat(v___x_590_);
v___x_592_ = lean_array_get_size(v_es_588_);
v___x_593_ = lean_nat_dec_lt(v_j_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_j_591_);
lean_dec(v_x_587_);
lean_dec(v_x_586_);
return v_x_583_;
}
else
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_632_; 
lean_inc_ref(v_es_588_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_x_583_, 0);
lean_dec(v_unused_633_);
v___x_595_ = v_x_583_;
v_isShared_596_ = v_isSharedCheck_632_;
goto v_resetjp_594_;
}
else
{
lean_dec(v_x_583_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_632_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_v_597_; lean_object* v___x_598_; lean_object* v_xs_x27_599_; lean_object* v___y_601_; 
v_v_597_ = lean_array_fget(v_es_588_, v_j_591_);
v___x_598_ = lean_box(0);
v_xs_x27_599_ = lean_array_fset(v_es_588_, v_j_591_, v___x_598_);
switch(lean_obj_tag(v_v_597_))
{
case 0:
{
lean_object* v_key_606_; lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
v_key_606_ = lean_ctor_get(v_v_597_, 0);
v_val_607_ = lean_ctor_get(v_v_597_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_v_597_);
if (v_isSharedCheck_617_ == 0)
{
v___x_609_ = v_v_597_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_inc(v_key_606_);
lean_dec(v_v_597_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint8_t v___x_611_; 
v___x_611_ = l_Lean_instBEqMVarId_beq(v_x_586_, v_key_606_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_609_);
v___x_612_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_606_, v_val_607_, v_x_586_, v_x_587_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___y_601_ = v___x_613_;
goto v___jp_600_;
}
else
{
lean_object* v___x_615_; 
lean_dec(v_val_607_);
lean_dec(v_key_606_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_x_587_);
lean_ctor_set(v___x_609_, 0, v_x_586_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_x_586_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_x_587_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v___y_601_ = v___x_615_;
goto v___jp_600_;
}
}
}
}
case 1:
{
lean_object* v_node_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_630_; 
v_node_618_ = lean_ctor_get(v_v_597_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_v_597_);
if (v_isSharedCheck_630_ == 0)
{
v___x_620_ = v_v_597_;
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_node_618_);
lean_dec(v_v_597_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_622_ = ((size_t)5ULL);
v___x_623_ = lean_usize_shift_right(v_x_584_, v___x_622_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_x_585_, v___x_624_);
v___x_626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_618_, v___x_623_, v___x_625_, v_x_586_, v_x_587_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_626_);
v___x_628_ = v___x_620_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v___y_601_ = v___x_628_;
goto v___jp_600_;
}
}
}
default: 
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_x_586_);
lean_ctor_set(v___x_631_, 1, v_x_587_);
v___y_601_ = v___x_631_;
goto v___jp_600_;
}
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_array_fset(v_xs_x27_599_, v_j_591_, v___y_601_);
lean_dec(v_j_591_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_602_);
v___x_604_ = v___x_595_;
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
}
}
else
{
lean_object* v_ks_634_; lean_object* v_vs_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_655_; 
v_ks_634_ = lean_ctor_get(v_x_583_, 0);
v_vs_635_ = lean_ctor_get(v_x_583_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_655_ == 0)
{
v___x_637_ = v_x_583_;
v_isShared_638_ = v_isSharedCheck_655_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_vs_635_);
lean_inc(v_ks_634_);
lean_dec(v_x_583_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_655_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_ks_634_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_vs_635_);
v___x_640_ = v_reuseFailAlloc_654_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v_newNode_641_; uint8_t v___y_643_; size_t v___x_649_; uint8_t v___x_650_; 
v_newNode_641_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_640_, v_x_586_, v_x_587_);
v___x_649_ = ((size_t)7ULL);
v___x_650_ = lean_usize_dec_le(v___x_649_, v_x_585_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_641_);
v___x_652_ = lean_unsigned_to_nat(4u);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
lean_dec(v___x_651_);
v___y_643_ = v___x_653_;
goto v___jp_642_;
}
else
{
v___y_643_ = v___x_650_;
goto v___jp_642_;
}
v___jp_642_:
{
if (v___y_643_ == 0)
{
lean_object* v_ks_644_; lean_object* v_vs_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_ks_644_ = lean_ctor_get(v_newNode_641_, 0);
lean_inc_ref(v_ks_644_);
v_vs_645_ = lean_ctor_get(v_newNode_641_, 1);
lean_inc_ref(v_vs_645_);
lean_dec_ref(v_newNode_641_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_648_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_585_, v_ks_644_, v_vs_645_, v___x_646_, v___x_647_);
lean_dec_ref(v_vs_645_);
lean_dec_ref(v_ks_644_);
return v___x_648_;
}
else
{
return v_newNode_641_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_656_, lean_object* v_keys_657_, lean_object* v_vals_658_, lean_object* v_i_659_, lean_object* v_entries_660_){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_keys_657_);
v___x_662_ = lean_nat_dec_lt(v_i_659_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec(v_i_659_);
return v_entries_660_;
}
else
{
lean_object* v_k_663_; lean_object* v_v_664_; uint64_t v___x_665_; size_t v_h_666_; size_t v___x_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v_h_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_k_663_ = lean_array_fget_borrowed(v_keys_657_, v_i_659_);
v_v_664_ = lean_array_fget_borrowed(v_vals_658_, v_i_659_);
v___x_665_ = l_Lean_instHashableMVarId_hash(v_k_663_);
v_h_666_ = lean_uint64_to_usize(v___x_665_);
v___x_667_ = ((size_t)5ULL);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_sub(v_depth_656_, v___x_669_);
v___x_671_ = lean_usize_mul(v___x_667_, v___x_670_);
v_h_672_ = lean_usize_shift_right(v_h_666_, v___x_671_);
v___x_673_ = lean_nat_add(v_i_659_, v___x_668_);
lean_dec(v_i_659_);
lean_inc(v_v_664_);
lean_inc(v_k_663_);
v___x_674_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_660_, v_h_672_, v_depth_656_, v_k_663_, v_v_664_);
v_i_659_ = v___x_673_;
v_entries_660_ = v___x_674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_i_679_, lean_object* v_entries_680_){
_start:
{
size_t v_depth_boxed_681_; lean_object* v_res_682_; 
v_depth_boxed_681_ = lean_unbox_usize(v_depth_676_);
lean_dec(v_depth_676_);
v_res_682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_681_, v_keys_677_, v_vals_678_, v_i_679_, v_entries_680_);
lean_dec_ref(v_vals_678_);
lean_dec_ref(v_keys_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
size_t v_x_5007__boxed_688_; size_t v_x_5008__boxed_689_; lean_object* v_res_690_; 
v_x_5007__boxed_688_ = lean_unbox_usize(v_x_684_);
lean_dec(v_x_684_);
v_x_5008__boxed_689_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_res_690_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_683_, v_x_5007__boxed_688_, v_x_5008__boxed_689_, v_x_686_, v_x_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
uint64_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_694_ = l_Lean_instHashableMVarId_hash(v_x_692_);
v___x_695_ = lean_uint64_to_usize(v___x_694_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_691_, v___x_695_, v___x_696_, v_x_692_, v_x_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_698_, lean_object* v_val_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_mctx_703_; lean_object* v_cache_704_; lean_object* v_zetaDeltaFVarIds_705_; lean_object* v_postponed_706_; lean_object* v_diag_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_735_; 
v___x_702_ = lean_st_ref_take(v___y_700_);
v_mctx_703_ = lean_ctor_get(v___x_702_, 0);
v_cache_704_ = lean_ctor_get(v___x_702_, 1);
v_zetaDeltaFVarIds_705_ = lean_ctor_get(v___x_702_, 2);
v_postponed_706_ = lean_ctor_get(v___x_702_, 3);
v_diag_707_ = lean_ctor_get(v___x_702_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_735_ == 0)
{
v___x_709_ = v___x_702_;
v_isShared_710_ = v_isSharedCheck_735_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_diag_707_);
lean_inc(v_postponed_706_);
lean_inc(v_zetaDeltaFVarIds_705_);
lean_inc(v_cache_704_);
lean_inc(v_mctx_703_);
lean_dec(v___x_702_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_735_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_depth_711_; lean_object* v_levelAssignDepth_712_; lean_object* v_lmvarCounter_713_; lean_object* v_mvarCounter_714_; lean_object* v_lDecls_715_; lean_object* v_decls_716_; lean_object* v_userNames_717_; lean_object* v_lAssignment_718_; lean_object* v_eAssignment_719_; lean_object* v_dAssignment_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_734_; 
v_depth_711_ = lean_ctor_get(v_mctx_703_, 0);
v_levelAssignDepth_712_ = lean_ctor_get(v_mctx_703_, 1);
v_lmvarCounter_713_ = lean_ctor_get(v_mctx_703_, 2);
v_mvarCounter_714_ = lean_ctor_get(v_mctx_703_, 3);
v_lDecls_715_ = lean_ctor_get(v_mctx_703_, 4);
v_decls_716_ = lean_ctor_get(v_mctx_703_, 5);
v_userNames_717_ = lean_ctor_get(v_mctx_703_, 6);
v_lAssignment_718_ = lean_ctor_get(v_mctx_703_, 7);
v_eAssignment_719_ = lean_ctor_get(v_mctx_703_, 8);
v_dAssignment_720_ = lean_ctor_get(v_mctx_703_, 9);
v_isSharedCheck_734_ = !lean_is_exclusive(v_mctx_703_);
if (v_isSharedCheck_734_ == 0)
{
v___x_722_ = v_mctx_703_;
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_dAssignment_720_);
lean_inc(v_eAssignment_719_);
lean_inc(v_lAssignment_718_);
lean_inc(v_userNames_717_);
lean_inc(v_decls_716_);
lean_inc(v_lDecls_715_);
lean_inc(v_mvarCounter_714_);
lean_inc(v_lmvarCounter_713_);
lean_inc(v_levelAssignDepth_712_);
lean_inc(v_depth_711_);
lean_dec(v_mctx_703_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_719_, v_mvarId_698_, v_val_699_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 8, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_depth_711_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_levelAssignDepth_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_lmvarCounter_713_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_mvarCounter_714_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_lDecls_715_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v_decls_716_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_userNames_717_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_lAssignment_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v_dAssignment_720_);
v___x_726_ = v_reuseFailAlloc_733_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_726_);
v___x_728_ = v___x_709_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_cache_704_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_zetaDeltaFVarIds_705_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_postponed_706_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_diag_707_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_st_ref_set(v___y_700_, v___x_728_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_736_, lean_object* v_val_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_736_, v_val_737_, v___y_738_);
lean_dec(v___y_738_);
return v_res_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_744_, lean_object* v___x_745_, lean_object* v_args_746_, uint8_t v_transparency_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
lean_inc(v___x_745_);
lean_inc(v_mvarId_744_);
v___x_753_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_744_, v___x_745_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; 
lean_dec_ref_known(v___x_753_, 1);
lean_inc(v_mvarId_744_);
v___x_754_ = l_Lean_MVarId_getTag(v_mvarId_744_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
lean_inc(v_mvarId_744_);
v___x_756_ = l_Lean_MVarId_getType(v_mvarId_744_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_872_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_757_, v___y_749_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_872_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_872_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_872_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_746_, v_transparency_747_, v_a_759_, v___x_763_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; uint8_t v___y_773_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___x_840_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_n(v_a_765_, 2);
lean_dec_ref_known(v___x_764_, 1);
v___x_840_ = l_Lean_Meta_isTypeCorrect(v_a_765_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_765_);
v___x_844_ = l_Lean_indentExpr(v_a_765_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_inc(v_mvarId_744_);
v___x_847_ = l_Lean_Meta_throwTacticEx___redArg(v___x_745_, v_mvarId_744_, v___x_846_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_dec_ref_known(v___x_847_, 1);
v___y_791_ = v___y_748_;
v___y_792_ = v___y_749_;
v___y_793_ = v___y_750_;
v___y_794_ = v___y_751_;
goto v___jp_790_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_765_);
lean_del_object(v___x_761_);
lean_dec(v_a_755_);
lean_dec_ref(v_args_746_);
lean_dec(v_mvarId_744_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_dec(v___x_745_);
v___y_791_ = v___y_748_;
v___y_792_ = v___y_749_;
v___y_793_ = v___y_750_;
v___y_794_ = v___y_751_;
goto v___jp_790_;
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_765_);
lean_del_object(v___x_761_);
lean_dec(v_a_755_);
lean_dec_ref(v_args_746_);
lean_dec(v___x_745_);
lean_dec(v_mvarId_744_);
v_a_856_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_840_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_840_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
v___jp_766_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_765_, v_a_755_, v___y_770_, v___y_771_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_n(v_a_775_, 2);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = l_Lean_mkAppN(v_a_775_, v___y_767_);
lean_dec_ref(v___y_767_);
v___x_777_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_744_, v___x_776_, v___y_771_);
lean_dec_ref(v___x_777_);
v___x_778_ = 1;
v___x_779_ = l_Lean_Expr_mvarId_x21(v_a_775_);
lean_dec(v_a_775_);
v___x_780_ = lean_box(0);
v___x_781_ = l_Lean_Meta_introNCore(v___x_779_, v___y_772_, v___x_780_, v___y_773_, v___x_778_, v___y_770_, v___y_771_, v___y_768_, v___y_769_);
return v___x_781_;
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v___y_772_);
lean_dec_ref(v___y_767_);
lean_dec(v_mvarId_744_);
v_a_782_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_774_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_774_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
v___jp_790_:
{
size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_sz_795_ = lean_array_size(v_args_746_);
v___x_796_ = ((size_t)0ULL);
lean_inc_ref(v_args_746_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_795_, v___x_796_, v_args_746_);
v___x_798_ = lean_array_get_size(v_args_746_);
v___x_799_ = lean_nat_dec_lt(v___x_763_, v___x_798_);
if (v___x_799_ == 0)
{
lean_del_object(v___x_761_);
lean_dec_ref(v_args_746_);
v___y_767_ = v___x_797_;
v___y_768_ = v___y_793_;
v___y_769_ = v___y_794_;
v___y_770_ = v___y_791_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_798_;
v___y_773_ = v___x_799_;
goto v___jp_766_;
}
else
{
if (v___x_799_ == 0)
{
lean_del_object(v___x_761_);
lean_dec_ref(v_args_746_);
v___y_767_ = v___x_797_;
v___y_768_ = v___y_793_;
v___y_769_ = v___y_794_;
v___y_770_ = v___y_791_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_798_;
v___y_773_ = v___x_799_;
goto v___jp_766_;
}
else
{
size_t v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_usize_of_nat(v___x_798_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_746_, v___x_796_, v___x_800_);
if (v___x_801_ == 0)
{
lean_del_object(v___x_761_);
lean_dec_ref(v_args_746_);
v___y_767_ = v___x_797_;
v___y_768_ = v___y_793_;
v___y_769_ = v___y_794_;
v___y_770_ = v___y_791_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_798_;
v___y_773_ = v___x_801_;
goto v___jp_766_;
}
else
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_807_; 
v___x_802_ = 0;
v___x_803_ = lean_box(v___x_802_);
v___x_804_ = lean_box(v___x_801_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_805_, 0, v_args_746_);
lean_closure_set(v___f_805_, 1, v___x_763_);
lean_closure_set(v___f_805_, 2, v___x_803_);
lean_closure_set(v___f_805_, 3, v___x_804_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 1);
lean_ctor_set(v___x_761_, 0, v___x_798_);
v___x_807_ = v___x_761_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_798_);
v___x_807_ = v_reuseFailAlloc_839_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_765_, v___x_807_, v___f_805_, v___x_802_, v___x_802_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v___x_812_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_fst_810_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_fst_810_);
v_snd_811_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_811_);
lean_dec(v_a_809_);
v___x_812_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_811_, v_a_755_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_n(v_a_813_, 2);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = l_Lean_mkAppN(v_a_813_, v___x_797_);
lean_dec_ref(v___x_797_);
lean_inc(v_fst_810_);
v___x_815_ = lean_array_mk(v_fst_810_);
v___x_816_ = l_Lean_mkAppN(v___x_814_, v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_744_, v___x_816_, v___y_792_);
lean_dec_ref(v___x_817_);
v___x_818_ = l_Lean_Expr_mvarId_x21(v_a_813_);
lean_dec(v_a_813_);
v___x_819_ = l_List_lengthTR___redArg(v_fst_810_);
lean_dec(v_fst_810_);
v___x_820_ = lean_nat_add(v___x_798_, v___x_819_);
lean_dec(v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = l_Lean_Meta_introNCore(v___x_818_, v___x_820_, v___x_821_, v___x_802_, v___x_801_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_fst_810_);
lean_dec_ref(v___x_797_);
lean_dec(v_mvarId_744_);
v_a_823_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_812_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_812_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v___x_797_);
lean_dec(v_a_755_);
lean_dec(v_mvarId_744_);
v_a_831_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_808_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_808_);
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
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_761_);
lean_dec(v_a_755_);
lean_dec_ref(v_args_746_);
lean_dec(v___x_745_);
lean_dec(v_mvarId_744_);
v_a_864_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_764_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_764_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_755_);
lean_dec_ref(v_args_746_);
lean_dec(v___x_745_);
lean_dec(v_mvarId_744_);
v_a_873_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_756_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_756_);
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
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_args_746_);
lean_dec(v___x_745_);
lean_dec(v_mvarId_744_);
v_a_881_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_754_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_754_);
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
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v_args_746_);
lean_dec(v___x_745_);
lean_dec(v_mvarId_744_);
v_a_889_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_753_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_753_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_897_, lean_object* v___x_898_, lean_object* v_args_899_, lean_object* v_transparency_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v_transparency_boxed_906_; lean_object* v_res_907_; 
v_transparency_boxed_906_ = lean_unbox(v_transparency_900_);
v_res_907_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_897_, v___x_898_, v_args_899_, v_transparency_boxed_906_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_911_, lean_object* v_args_912_, uint8_t v_transparency_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_920_ = lean_box(v_transparency_913_);
lean_inc(v_mvarId_911_);
v___f_921_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_921_, 0, v_mvarId_911_);
lean_closure_set(v___f_921_, 1, v___x_919_);
lean_closure_set(v___f_921_, 2, v_args_912_);
lean_closure_set(v___f_921_, 3, v___x_920_);
v___x_922_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_911_, v___f_921_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_923_, lean_object* v_args_924_, lean_object* v_transparency_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_transparency_boxed_931_; lean_object* v_res_932_; 
v_transparency_boxed_931_ = lean_unbox(v_transparency_925_);
v_res_932_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_923_, v_args_924_, v_transparency_boxed_931_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_933_, lean_object* v_val_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_933_, v_val_934_, v___y_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_941_, lean_object* v_val_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_941_, v_val_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, size_t v_x_956_, size_t v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_955_, v_x_956_, v_x_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
size_t v_x_5586__boxed_967_; size_t v_x_5587__boxed_968_; lean_object* v_res_969_; 
v_x_5586__boxed_967_ = lean_unbox_usize(v_x_963_);
lean_dec(v_x_963_);
v_x_5587__boxed_968_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_961_, v_x_962_, v_x_5586__boxed_967_, v_x_5587__boxed_968_, v_x_965_, v_x_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_970_, lean_object* v_n_971_, lean_object* v_k_972_, lean_object* v_v_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_971_, v_k_972_, v_v_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_975_, size_t v_depth_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_heq_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_976_, v_keys_977_, v_vals_978_, v_i_980_, v_entries_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_983_, lean_object* v_depth_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
size_t v_depth_boxed_990_; lean_object* v_res_991_; 
v_depth_boxed_990_ = lean_unbox_usize(v_depth_984_);
lean_dec(v_depth_984_);
v_res_991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_983_, v_depth_boxed_990_, v_keys_985_, v_vals_986_, v_heq_987_, v_i_988_, v_entries_989_);
lean_dec_ref(v_vals_986_);
lean_dec_ref(v_keys_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_993_, v_x_994_, v_x_995_, v_x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_998_, lean_object* v_args_999_, uint8_t v_transparency_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_998_, v_args_999_, v_transparency_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_1007_, lean_object* v_args_1008_, lean_object* v_transparency_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
uint8_t v_transparency_boxed_1015_; lean_object* v_res_1016_; 
v_transparency_boxed_1015_ = lean_unbox(v_transparency_1009_);
v_res_1016_ = l_Lean_MVarId_generalize(v_mvarId_1007_, v_args_1008_, v_transparency_boxed_1015_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1017_, size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_b_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1021_ == 0)
{
return v_b_1020_;
}
else
{
lean_object* v_snd_1022_; lean_object* v_fst_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1056_; 
v_snd_1022_ = lean_ctor_get(v_b_1020_, 1);
v_fst_1023_ = lean_ctor_get(v_b_1020_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_b_1020_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1025_ = v_b_1020_;
v_isShared_1026_ = v_isSharedCheck_1056_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1023_);
lean_dec(v_b_1020_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1056_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_array_1027_; lean_object* v_start_1028_; lean_object* v_stop_1029_; uint8_t v___x_1030_; 
v_array_1027_ = lean_ctor_get(v_snd_1022_, 0);
v_start_1028_ = lean_ctor_get(v_snd_1022_, 1);
v_stop_1029_ = lean_ctor_get(v_snd_1022_, 2);
v___x_1030_ = lean_nat_dec_lt(v_start_1028_, v_stop_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1032_; 
if (v_isShared_1026_ == 0)
{
v___x_1032_ = v___x_1025_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_fst_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_snd_1022_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1052_; 
lean_inc(v_stop_1029_);
lean_inc(v_start_1028_);
lean_inc_ref(v_array_1027_);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_snd_1022_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1053_ = lean_ctor_get(v_snd_1022_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_snd_1022_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_snd_1022_, 0);
lean_dec(v_unused_1055_);
v___x_1035_ = v_snd_1022_;
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v_snd_1022_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v_a_1037_ = lean_array_uget_borrowed(v_as_1017_, v_i_1019_);
v___x_1038_ = lean_array_fget(v_array_1027_, v_start_1028_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_start_1028_, v___x_1039_);
lean_dec(v_start_1028_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1040_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_array_1027_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_stop_1029_);
v___x_1042_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = l_Lean_mkFVar(v___x_1038_);
lean_inc(v_a_1037_);
v___x_1044_ = l_Lean_Meta_FVarSubst_insert(v_fst_1023_, v_a_1037_, v___x_1043_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___x_1042_);
lean_ctor_set(v___x_1025_, 0, v___x_1044_);
v___x_1046_ = v___x_1025_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1042_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
size_t v___x_1047_; size_t v___x_1048_; 
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1019_, v___x_1047_);
v_i_1019_ = v___x_1048_;
v_b_1020_ = v___x_1046_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1057_, lean_object* v_sz_1058_, lean_object* v_i_1059_, lean_object* v_b_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1058_);
lean_dec(v_sz_1058_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1057_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1060_);
lean_dec_ref(v_as_1057_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_bs_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_bs_1066_);
return v___x_1070_;
}
else
{
lean_object* v_v_1071_; lean_object* v_expr_1072_; lean_object* v_xName_x3f_1073_; lean_object* v_hName_x3f_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1097_; 
v_v_1071_ = lean_array_uget(v_bs_1066_, v_i_1065_);
v_expr_1072_ = lean_ctor_get(v_v_1071_, 0);
v_xName_x3f_1073_ = lean_ctor_get(v_v_1071_, 1);
v_hName_x3f_1074_ = lean_ctor_get(v_v_1071_, 2);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_v_1071_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1076_ = v_v_1071_;
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_hName_x3f_1074_);
lean_inc(v_xName_x3f_1073_);
lean_inc(v_expr_1072_);
lean_dec(v_v_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1072_, v___y_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; lean_object* v_bs_x27_1081_; lean_object* v___x_1083_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = lean_unsigned_to_nat(0u);
v_bs_x27_1081_ = lean_array_uset(v_bs_1066_, v_i_1065_, v___x_1080_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_a_1079_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_xName_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_hName_x3f_1074_);
v___x_1083_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1065_, v___x_1084_);
v___x_1086_ = lean_array_uset(v_bs_x27_1081_, v_i_1065_, v___x_1083_);
v_i_1065_ = v___x_1085_;
v_bs_1066_ = v___x_1086_;
goto _start;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1076_);
lean_dec(v_hName_x3f_1074_);
lean_dec(v_xName_x3f_1073_);
lean_dec_ref(v_bs_1066_);
v_a_1089_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1078_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1078_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1098_, lean_object* v_i_1099_, lean_object* v_bs_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1098_);
lean_dec(v_sz_1098_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1103_, v_i_boxed_1104_, v_bs_1100_, v___y_1101_);
lean_dec(v___y_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1106_, lean_object* v_a_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v_expr_1118_; lean_object* v___x_1119_; uint8_t v_foApprox_1120_; uint8_t v_ctxApprox_1121_; uint8_t v_quasiPatternApprox_1122_; uint8_t v_constApprox_1123_; uint8_t v_isDefEqStuckEx_1124_; uint8_t v_unificationHints_1125_; uint8_t v_proofIrrelevance_1126_; uint8_t v_assignSyntheticOpaque_1127_; uint8_t v_offsetCnstrs_1128_; uint8_t v_etaStruct_1129_; uint8_t v_univApprox_1130_; uint8_t v_iota_1131_; uint8_t v_beta_1132_; uint8_t v_proj_1133_; uint8_t v_zeta_1134_; uint8_t v_zetaDelta_1135_; uint8_t v_zetaUnused_1136_; uint8_t v_zetaHave_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1185_; 
v___x_1117_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v_expr_1118_ = lean_ctor_get(v___x_1117_, 0);
v___x_1119_ = l_Lean_Meta_Context_config(v___y_1111_);
v_foApprox_1120_ = lean_ctor_get_uint8(v___x_1119_, 0);
v_ctxApprox_1121_ = lean_ctor_get_uint8(v___x_1119_, 1);
v_quasiPatternApprox_1122_ = lean_ctor_get_uint8(v___x_1119_, 2);
v_constApprox_1123_ = lean_ctor_get_uint8(v___x_1119_, 3);
v_isDefEqStuckEx_1124_ = lean_ctor_get_uint8(v___x_1119_, 4);
v_unificationHints_1125_ = lean_ctor_get_uint8(v___x_1119_, 5);
v_proofIrrelevance_1126_ = lean_ctor_get_uint8(v___x_1119_, 6);
v_assignSyntheticOpaque_1127_ = lean_ctor_get_uint8(v___x_1119_, 7);
v_offsetCnstrs_1128_ = lean_ctor_get_uint8(v___x_1119_, 8);
v_etaStruct_1129_ = lean_ctor_get_uint8(v___x_1119_, 10);
v_univApprox_1130_ = lean_ctor_get_uint8(v___x_1119_, 11);
v_iota_1131_ = lean_ctor_get_uint8(v___x_1119_, 12);
v_beta_1132_ = lean_ctor_get_uint8(v___x_1119_, 13);
v_proj_1133_ = lean_ctor_get_uint8(v___x_1119_, 14);
v_zeta_1134_ = lean_ctor_get_uint8(v___x_1119_, 15);
v_zetaDelta_1135_ = lean_ctor_get_uint8(v___x_1119_, 16);
v_zetaUnused_1136_ = lean_ctor_get_uint8(v___x_1119_, 17);
v_zetaHave_1137_ = lean_ctor_get_uint8(v___x_1119_, 18);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1139_ = v___x_1119_;
v_isShared_1140_ = v_isSharedCheck_1185_;
goto v_resetjp_1138_;
}
else
{
lean_dec(v___x_1119_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1185_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v_trackZetaDelta_1141_; lean_object* v_zetaDeltaSet_1142_; lean_object* v_lctx_1143_; lean_object* v_localInstances_1144_; lean_object* v_defEqCtx_x3f_1145_; lean_object* v_synthPendingDepth_1146_; lean_object* v_canUnfold_x3f_1147_; uint8_t v_univApprox_1148_; uint8_t v_inTypeClassResolution_1149_; uint8_t v_cacheInferType_1150_; lean_object* v_config_1152_; 
v_trackZetaDelta_1141_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*7);
v_zetaDeltaSet_1142_ = lean_ctor_get(v___y_1111_, 1);
v_lctx_1143_ = lean_ctor_get(v___y_1111_, 2);
v_localInstances_1144_ = lean_ctor_get(v___y_1111_, 3);
v_defEqCtx_x3f_1145_ = lean_ctor_get(v___y_1111_, 4);
v_synthPendingDepth_1146_ = lean_ctor_get(v___y_1111_, 5);
v_canUnfold_x3f_1147_ = lean_ctor_get(v___y_1111_, 6);
v_univApprox_1148_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1149_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*7 + 2);
v_cacheInferType_1150_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*7 + 3);
if (v_isShared_1140_ == 0)
{
v_config_1152_ = v___x_1139_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 0, v_foApprox_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 1, v_ctxApprox_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 2, v_quasiPatternApprox_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 3, v_constApprox_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 4, v_isDefEqStuckEx_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 5, v_unificationHints_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 6, v_proofIrrelevance_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 7, v_assignSyntheticOpaque_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 8, v_offsetCnstrs_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 10, v_etaStruct_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 11, v_univApprox_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 12, v_iota_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 13, v_beta_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 14, v_proj_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 15, v_zeta_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 16, v_zetaDelta_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 17, v_zetaUnused_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1184_, 18, v_zetaHave_1137_);
v_config_1152_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; lean_object* v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v_key_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_ctor_set_uint8(v_config_1152_, 9, v_transparency_1106_);
v___x_1153_ = l_Lean_Meta_Context_configKey(v___y_1111_);
v___x_1154_ = 3ULL;
v___x_1155_ = lean_uint64_shift_right(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_uint64_shift_left(v___x_1155_, v___x_1154_);
v___x_1158_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1106_);
v_key_1159_ = lean_uint64_lor(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1160_, 0, v_config_1152_);
lean_ctor_set_uint64(v___x_1160_, sizeof(void*)*1, v_key_1159_);
lean_inc(v_canUnfold_x3f_1147_);
lean_inc(v_synthPendingDepth_1146_);
lean_inc(v_defEqCtx_x3f_1145_);
lean_inc_ref(v_localInstances_1144_);
lean_inc_ref(v_lctx_1143_);
lean_inc(v_zetaDeltaSet_1142_);
v___x_1161_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_zetaDeltaSet_1142_);
lean_ctor_set(v___x_1161_, 2, v_lctx_1143_);
lean_ctor_set(v___x_1161_, 3, v_localInstances_1144_);
lean_ctor_set(v___x_1161_, 4, v_defEqCtx_x3f_1145_);
lean_ctor_set(v___x_1161_, 5, v_synthPendingDepth_1146_);
lean_ctor_set(v___x_1161_, 6, v_canUnfold_x3f_1147_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*7, v_trackZetaDelta_1141_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*7 + 1, v_univApprox_1148_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1149_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*7 + 3, v_cacheInferType_1150_);
lean_inc_ref(v_expr_1118_);
lean_inc_ref(v_a_1107_);
v___x_1162_ = l_Lean_Meta_kabstract(v_a_1107_, v_expr_1118_, v___x_1156_, v___x_1161_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec_ref_known(v___x_1161_, 7);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1175_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
uint8_t v___x_1167_; 
v___x_1167_ = l_Lean_Expr_hasLooseBVars(v_a_1163_);
lean_dec(v_a_1163_);
if (v___x_1167_ == 0)
{
size_t v___x_1168_; size_t v___x_1169_; 
lean_del_object(v___x_1165_);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1109_, v___x_1168_);
v_i_1109_ = v___x_1169_;
goto _start;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec_ref(v_a_1107_);
v___x_1171_ = lean_box(v___x_1167_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1171_);
v___x_1173_ = v___x_1165_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_a_1107_);
v_a_1176_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1162_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1162_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
else
{
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_a_1107_);
v___x_1186_ = 0;
v___x_1187_ = lean_box(v___x_1186_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1189_, lean_object* v_a_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v_transparency_boxed_1199_; size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_transparency_boxed_1199_ = lean_unbox(v_transparency_1189_);
v_i_boxed_1200_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1199_, v_a_1190_, v_as_1191_, v_i_boxed_1200_, v_stop_boxed_1201_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_as_1191_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1203_, lean_object* v___x_1204_, uint8_t v_transparency_1205_, lean_object* v_as_1206_, size_t v_i_1207_, size_t v_stop_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_a_1216_; uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_eq(v_i_1207_, v_stop_1208_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; uint8_t v_a_1223_; lean_object* v___x_1225_; 
v___x_1221_ = lean_array_uget_borrowed(v_as_1206_, v_i_1207_);
lean_inc(v___x_1221_);
v___x_1225_ = l_Lean_FVarId_getType___redArg(v___x_1221_, v___y_1210_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1226_, v___y_1211_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_nat_dec_eq(v___x_1204_, v___x_1229_);
v___x_1231_ = lean_array_get_size(v_a_1203_);
v___x_1232_ = lean_nat_dec_lt(v___x_1229_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_a_1228_);
v_a_1223_ = v___x_1230_;
goto v___jp_1222_;
}
else
{
if (v___x_1232_ == 0)
{
lean_dec(v_a_1228_);
v_a_1223_ = v___x_1230_;
goto v___jp_1222_;
}
else
{
size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = lean_usize_of_nat(v___x_1231_);
v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1205_, v_a_1228_, v_a_1203_, v___x_1233_, v___x_1234_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
v_a_1223_ = v___x_1237_;
goto v___jp_1222_;
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v_b_1209_);
v_a_1238_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1235_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1235_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_b_1209_);
v_a_1246_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1227_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1227_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_b_1209_);
v_a_1254_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1225_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1225_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
v___jp_1222_:
{
if (v_a_1223_ == 0)
{
v_a_1216_ = v_b_1209_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1224_; 
lean_inc(v___x_1221_);
v___x_1224_ = lean_array_push(v_b_1209_, v___x_1221_);
v_a_1216_ = v___x_1224_;
goto v___jp_1215_;
}
}
}
else
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_b_1209_);
return v___x_1262_;
}
v___jp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1207_, v___x_1217_);
v_i_1207_ = v___x_1218_;
v_b_1209_ = v_a_1216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1263_, lean_object* v___x_1264_, lean_object* v_transparency_1265_, lean_object* v_as_1266_, lean_object* v_i_1267_, lean_object* v_stop_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_transparency_boxed_1275_; size_t v_i_boxed_1276_; size_t v_stop_boxed_1277_; lean_object* v_res_1278_; 
v_transparency_boxed_1275_ = lean_unbox(v_transparency_1265_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_stop_boxed_1277_ = lean_unbox_usize(v_stop_1268_);
lean_dec(v_stop_1268_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1263_, v___x_1264_, v_transparency_boxed_1275_, v_as_1266_, v_i_boxed_1276_, v_stop_boxed_1277_, v_b_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_as_1266_);
lean_dec(v___x_1264_);
lean_dec_ref(v_a_1263_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1279_, lean_object* v_a_1280_, lean_object* v___x_1281_, lean_object* v_as_1282_, size_t v_i_1283_, size_t v_stop_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_a_1292_; uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_eq(v_i_1283_, v_stop_1284_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v_a_1299_; lean_object* v___x_1301_; 
v___x_1297_ = lean_array_uget_borrowed(v_as_1282_, v_i_1283_);
lean_inc(v___x_1297_);
v___x_1301_ = l_Lean_FVarId_getType___redArg(v___x_1297_, v___y_1286_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1303_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1302_, v___y_1287_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_nat_dec_eq(v___x_1281_, v___x_1305_);
v___x_1307_ = lean_array_get_size(v_a_1280_);
v___x_1308_ = lean_nat_dec_lt(v___x_1305_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec(v_a_1304_);
v_a_1299_ = v___x_1306_;
goto v___jp_1298_;
}
else
{
if (v___x_1308_ == 0)
{
lean_dec(v_a_1304_);
v_a_1299_ = v___x_1306_;
goto v___jp_1298_;
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1307_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1279_, v_a_1304_, v_a_1280_, v___x_1309_, v___x_1310_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; uint8_t v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
v_a_1299_ = v___x_1313_;
goto v___jp_1298_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_b_1285_);
v_a_1314_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1311_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1311_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_b_1285_);
v_a_1322_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1303_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1303_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_b_1285_);
v_a_1330_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1301_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1301_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
v___jp_1298_:
{
if (v_a_1299_ == 0)
{
v_a_1292_ = v_b_1285_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1300_; 
lean_inc(v___x_1297_);
v___x_1300_ = lean_array_push(v_b_1285_, v___x_1297_);
v_a_1292_ = v___x_1300_;
goto v___jp_1291_;
}
}
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1285_);
return v___x_1338_;
}
v___jp_1291_:
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1283_, v___x_1293_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1280_, v___x_1281_, v_transparency_1279_, v_as_1282_, v___x_1294_, v_stop_1284_, v_a_1292_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1339_, lean_object* v_a_1340_, lean_object* v___x_1341_, lean_object* v_as_1342_, lean_object* v_i_1343_, lean_object* v_stop_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_transparency_boxed_1351_; size_t v_i_boxed_1352_; size_t v_stop_boxed_1353_; lean_object* v_res_1354_; 
v_transparency_boxed_1351_ = lean_unbox(v_transparency_1339_);
v_i_boxed_1352_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_stop_boxed_1353_ = lean_unbox_usize(v_stop_1344_);
lean_dec(v_stop_1344_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1351_, v_a_1340_, v___x_1341_, v_as_1342_, v_i_boxed_1352_, v_stop_boxed_1353_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v_as_1342_);
lean_dec(v___x_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1357_, lean_object* v_args_1358_, lean_object* v_hyps_1359_, lean_object* v_fvarSubst_1360_, uint8_t v_transparency_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_array_get_size(v_hyps_1359_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_nat_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
size_t v_sz_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v_sz_1370_ = lean_array_size(v_args_1358_);
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1370_, v___x_1371_, v_args_1358_, v_a_1363_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; lean_object* v_a_1376_; lean_object* v___y_1450_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = 1;
v___x_1460_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1461_ = lean_nat_dec_lt(v___x_1368_, v___x_1367_);
if (v___x_1461_ == 0)
{
v_a_1376_ = v___x_1460_;
goto v___jp_1375_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1462_ == 0)
{
if (v___x_1461_ == 0)
{
v_a_1376_ = v___x_1460_;
goto v___jp_1375_;
}
else
{
size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_usize_of_nat(v___x_1367_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1361_, v_a_1373_, v___x_1367_, v_hyps_1359_, v___x_1371_, v___x_1463_, v___x_1460_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
v___y_1450_ = v___x_1464_;
goto v___jp_1449_;
}
}
else
{
size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_usize_of_nat(v___x_1367_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1361_, v_a_1373_, v___x_1367_, v_hyps_1359_, v___x_1371_, v___x_1465_, v___x_1460_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
v___y_1450_ = v___x_1466_;
goto v___jp_1449_;
}
}
v___jp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_MVarId_revert(v_mvarId_1357_, v_a_1376_, v___x_1374_, v___x_1369_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1381_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_fst_1379_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_fst_1379_);
v_snd_1380_ = lean_ctor_get(v_a_1378_, 1);
lean_inc(v_snd_1380_);
lean_dec(v_a_1378_);
v___x_1381_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1380_, v_a_1373_, v_transparency_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1432_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_fst_1383_ = lean_ctor_get(v_a_1382_, 0);
v_snd_1384_ = lean_ctor_get(v_a_1382_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1382_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1386_ = v_a_1382_;
v_isShared_1387_ = v_isSharedCheck_1432_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v_a_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1432_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_array_get_size(v_fst_1379_);
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Lean_Meta_introNCore(v_snd_1384_, v___x_1388_, v___x_1389_, v___x_1369_, v___x_1374_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1423_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1423_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1423_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1422_; 
v_fst_1395_ = lean_ctor_get(v_a_1391_, 0);
v_snd_1396_ = lean_ctor_get(v_a_1391_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_a_1391_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1398_ = v_a_1391_;
v_isShared_1399_ = v_isSharedCheck_1422_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snd_1396_);
lean_inc(v_fst_1395_);
lean_dec(v_a_1391_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1422_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1400_ = lean_array_get_size(v_fst_1395_);
v___x_1401_ = l_Array_toSubarray___redArg(v_fst_1395_, v___x_1368_, v___x_1400_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1401_);
lean_ctor_set(v___x_1398_, 0, v_fvarSubst_1360_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fvarSubst_1360_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
size_t v_sz_1404_; lean_object* v___x_1405_; lean_object* v_fst_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v_sz_1404_ = lean_array_size(v_fst_1379_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1379_, v_sz_1404_, v___x_1371_, v___x_1403_);
lean_dec(v_fst_1379_);
v_fst_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1405_, 1);
lean_dec(v_unused_1420_);
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_fst_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_snd_1396_);
lean_ctor_set(v___x_1408_, 0, v_fst_1383_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1383_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_snd_1396_);
v___x_1411_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1411_);
lean_ctor_set(v___x_1386_, 0, v_fst_1406_);
v___x_1413_ = v___x_1386_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1413_);
v___x_1415_ = v___x_1393_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
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
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_del_object(v___x_1386_);
lean_dec(v_fst_1383_);
lean_dec(v_fst_1379_);
lean_dec(v_fvarSubst_1360_);
v_a_1424_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1390_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1390_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_fst_1379_);
lean_dec(v_fvarSubst_1360_);
v_a_1433_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1381_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1381_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1373_);
lean_dec(v_fvarSubst_1360_);
v_a_1441_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1377_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1377_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
v___jp_1449_:
{
if (lean_obj_tag(v___y_1450_) == 0)
{
lean_object* v_a_1451_; 
v_a_1451_ = lean_ctor_get(v___y_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___y_1450_, 1);
v_a_1376_ = v_a_1451_;
goto v___jp_1375_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_a_1373_);
lean_dec(v_fvarSubst_1360_);
lean_dec(v_mvarId_1357_);
v_a_1452_ = lean_ctor_get(v___y_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___y_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___y_1450_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___y_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_fvarSubst_1360_);
lean_dec(v_mvarId_1357_);
v_a_1467_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1372_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1372_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1357_, v_args_1358_, v_transparency_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1484_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_fvarSubst_1360_);
lean_ctor_set(v___x_1480_, 1, v_a_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_fvarSubst_1360_);
v_a_1485_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1475_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1475_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1493_, lean_object* v_args_1494_, lean_object* v_hyps_1495_, lean_object* v_fvarSubst_1496_, lean_object* v_transparency_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
uint8_t v_transparency_boxed_1503_; lean_object* v_res_1504_; 
v_transparency_boxed_1503_ = lean_unbox(v_transparency_1497_);
v_res_1504_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1493_, v_args_1494_, v_hyps_1495_, v_fvarSubst_1496_, v_transparency_boxed_1503_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec_ref(v_hyps_1495_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1505_, size_t v_i_1506_, lean_object* v_bs_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1505_, v_i_1506_, v_bs_1507_, v___y_1509_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_bs_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1522_, v_i_boxed_1523_, v_bs_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1524_;
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
