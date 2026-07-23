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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* v_val_114_; 
v_val_114_ = lean_ctor_get(v_xName_x3f_72_, 0);
lean_inc(v_val_114_);
v_xName_84_ = v_val_114_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
v___x_116_ = l_Lean_Core_mkFreshUserName(v___x_115_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v_xName_84_ = v_a_117_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v_a_82_);
lean_dec(v_a_78_);
lean_dec(v_a_74_);
v_a_118_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_116_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
v___jp_83_:
{
lean_object* v_keyedConfig_89_; uint8_t v_trackZetaDelta_90_; lean_object* v_zetaDeltaSet_91_; lean_object* v_lctx_92_; lean_object* v_localInstances_93_; lean_object* v_defEqCtx_x3f_94_; lean_object* v_synthPendingDepth_95_; lean_object* v_customCanUnfoldPredicate_x3f_96_; uint8_t v_univApprox_97_; uint8_t v_inTypeClassResolution_98_; uint8_t v_cacheInferType_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_keyedConfig_89_ = lean_ctor_get(v___y_85_, 0);
v_trackZetaDelta_90_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7);
v_zetaDeltaSet_91_ = lean_ctor_get(v___y_85_, 1);
v_lctx_92_ = lean_ctor_get(v___y_85_, 2);
v_localInstances_93_ = lean_ctor_get(v___y_85_, 3);
v_defEqCtx_x3f_94_ = lean_ctor_get(v___y_85_, 4);
v_synthPendingDepth_95_ = lean_ctor_get(v___y_85_, 5);
v_customCanUnfoldPredicate_x3f_96_ = lean_ctor_get(v___y_85_, 6);
v_univApprox_97_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_98_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 2);
v_cacheInferType_99_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7 + 3);
v___x_100_ = lean_box(0);
lean_inc_ref(v_keyedConfig_89_);
v___x_101_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_59_, v_keyedConfig_89_);
lean_inc(v_customCanUnfoldPredicate_x3f_96_);
lean_inc(v_synthPendingDepth_95_);
lean_inc(v_defEqCtx_x3f_94_);
lean_inc_ref(v_localInstances_93_);
lean_inc_ref(v_lctx_92_);
lean_inc(v_zetaDeltaSet_91_);
v___x_102_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_zetaDeltaSet_91_);
lean_ctor_set(v___x_102_, 2, v_lctx_92_);
lean_ctor_set(v___x_102_, 3, v_localInstances_93_);
lean_ctor_set(v___x_102_, 4, v_defEqCtx_x3f_94_);
lean_ctor_set(v___x_102_, 5, v_synthPendingDepth_95_);
lean_ctor_set(v___x_102_, 6, v_customCanUnfoldPredicate_x3f_96_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*7, v_trackZetaDelta_90_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*7 + 1, v_univApprox_97_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*7 + 2, v_inTypeClassResolution_98_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*7 + 3, v_cacheInferType_99_);
v___x_103_ = l_Lean_Meta_kabstract(v_a_82_, v_a_74_, v___x_100_, v___x_102_, v___y_86_, v___y_87_, v___y_88_);
lean_dec_ref_known(v___x_102_, 7);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_113_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_113_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_108_ = 0;
v___x_109_ = l_Lean_mkForall(v_xName_84_, v___x_108_, v_a_78_, v_a_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_dec(v_xName_84_);
lean_dec(v_a_78_);
return v___x_103_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_126_, lean_object* v_transparency_127_, lean_object* v_target_128_, lean_object* v_i_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_transparency_boxed_135_; lean_object* v_res_136_; 
v_transparency_boxed_135_ = lean_unbox(v_transparency_127_);
v_res_136_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_126_, v_transparency_boxed_135_, v_target_128_, v_i_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_i_129_);
lean_dec_ref(v_args_126_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_137_, lean_object* v_xs_138_, lean_object* v_type_139_, lean_object* v_i_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_array_get_size(v_xs_138_);
v___x_147_ = lean_nat_dec_lt(v_i_140_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_i_140_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_type_139_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v_arg_152_; lean_object* v_hName_x3f_153_; 
v___x_151_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_152_ = lean_array_get_borrowed(v___x_151_, v_args_137_, v_i_140_);
v_hName_x3f_153_ = lean_ctor_get(v_arg_152_, 2);
if (lean_obj_tag(v_hName_x3f_153_) == 1)
{
lean_object* v_expr_154_; lean_object* v_val_155_; lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_expr_154_ = lean_ctor_get(v_arg_152_, 0);
v_val_155_ = lean_ctor_get(v_hName_x3f_153_, 0);
v___x_186_ = lean_array_fget_borrowed(v_xs_138_, v_i_140_);
lean_inc(v_a_144_);
lean_inc_ref(v_a_143_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
lean_inc(v___x_186_);
v___x_187_ = lean_infer_type(v___x_186_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
lean_inc_ref(v_expr_154_);
v___x_189_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_154_, v_a_142_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc_n(v_a_190_, 2);
lean_dec_ref_known(v___x_189_, 1);
lean_inc(v_a_144_);
lean_inc_ref(v_a_143_);
lean_inc(v_a_142_);
lean_inc_ref(v_a_141_);
v___x_191_ = lean_infer_type(v_a_190_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_192_, v_a_142_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v___x_195_ = l_Lean_Meta_isExprDefEq(v_a_188_, v_a_194_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; uint8_t v___x_197_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = lean_unbox(v_a_196_);
lean_dec(v_a_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_inc(v___x_186_);
lean_inc(v_a_190_);
v___x_198_ = l_Lean_Meta_mkHEq(v_a_190_, v___x_186_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = l_Lean_Meta_mkHEqRefl(v_a_190_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v_fst_157_ = v_a_199_;
v_snd_158_ = v_a_201_;
v___y_159_ = v_a_141_;
v___y_160_ = v_a_142_;
v___y_161_ = v_a_143_;
v___y_162_ = v_a_144_;
goto v___jp_156_;
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_199_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_202_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_200_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_190_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_210_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_198_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_198_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v___x_218_; 
lean_inc(v___x_186_);
lean_inc(v_a_190_);
v___x_218_ = l_Lean_Meta_mkEq(v_a_190_, v___x_186_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = l_Lean_Meta_mkEqRefl(v_a_190_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v_fst_157_ = v_a_219_;
v_snd_158_ = v_a_221_;
v___y_159_ = v_a_141_;
v___y_160_ = v_a_142_;
v___y_161_ = v_a_143_;
v___y_162_ = v_a_144_;
goto v___jp_156_;
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_a_219_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_a_190_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_230_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_218_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_218_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_a_190_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_238_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_195_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_195_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_190_);
lean_dec(v_a_188_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_246_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_193_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_193_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_a_190_);
lean_dec(v_a_188_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_254_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_191_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_191_);
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
lean_dec(v_a_188_);
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_262_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_189_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_189_);
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
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_i_140_);
lean_dec_ref(v_type_139_);
v_a_270_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_187_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_187_);
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
v___jp_156_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_i_140_, v___x_163_);
lean_dec(v_i_140_);
v___x_165_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_137_, v_xs_138_, v_type_139_, v___x_164_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_185_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_185_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_185_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_185_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_184_; 
v_fst_170_ = lean_ctor_get(v_a_166_, 0);
v_snd_171_ = lean_ctor_get(v_a_166_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_166_);
if (v_isSharedCheck_184_ == 0)
{
v___x_173_ = v_a_166_;
v_isShared_174_ = v_isSharedCheck_184_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_snd_171_);
lean_inc(v_fst_170_);
lean_dec(v_a_166_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_184_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v_snd_158_);
lean_ctor_set(v___x_175_, 1, v_fst_170_);
v___x_176_ = 0;
lean_inc(v_val_155_);
v___x_177_ = l_Lean_mkForall(v_val_155_, v___x_176_, v_fst_157_, v_snd_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_177_);
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_179_ = v___x_173_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_181_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_179_);
v___x_181_ = v___x_168_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_158_);
lean_dec_ref(v_fst_157_);
return v___x_165_;
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_140_, v___x_278_);
lean_dec(v_i_140_);
v_i_140_ = v___x_279_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_281_, lean_object* v_xs_282_, lean_object* v_type_283_, lean_object* v_i_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_281_, v_xs_282_, v_type_283_, v_i_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec_ref(v_xs_282_);
lean_dec_ref(v_args_281_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* v_k_291_, lean_object* v_b_292_, lean_object* v_c_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
v___x_299_ = lean_apply_7(v_k_291_, v_b_292_, v_c_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, lean_box(0));
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* v_k_300_, lean_object* v_b_301_, lean_object* v_c_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_300_, v_b_301_, v_c_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* v_type_309_, lean_object* v_maxFVars_x3f_310_, lean_object* v_k_311_, uint8_t v_cleanupAnnotations_312_, uint8_t v_whnfType_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; 
v___f_319_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_319_, 0, v_k_311_);
v___x_320_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_309_, v_maxFVars_x3f_310_, v___f_319_, v_cleanupAnnotations_312_, v_whnfType_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_320_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_320_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* v_type_337_, lean_object* v_maxFVars_x3f_338_, lean_object* v_k_339_, lean_object* v_cleanupAnnotations_340_, lean_object* v_whnfType_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_347_; uint8_t v_whnfType_boxed_348_; lean_object* v_res_349_; 
v_cleanupAnnotations_boxed_347_ = lean_unbox(v_cleanupAnnotations_340_);
v_whnfType_boxed_348_ = lean_unbox(v_whnfType_341_);
v_res_349_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_337_, v_maxFVars_x3f_338_, v_k_339_, v_cleanupAnnotations_boxed_347_, v_whnfType_boxed_348_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_00_u03b1_350_, lean_object* v_type_351_, lean_object* v_maxFVars_x3f_352_, lean_object* v_k_353_, uint8_t v_cleanupAnnotations_354_, uint8_t v_whnfType_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_351_, v_maxFVars_x3f_352_, v_k_353_, v_cleanupAnnotations_354_, v_whnfType_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_00_u03b1_362_, lean_object* v_type_363_, lean_object* v_maxFVars_x3f_364_, lean_object* v_k_365_, lean_object* v_cleanupAnnotations_366_, lean_object* v_whnfType_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_373_; uint8_t v_whnfType_boxed_374_; lean_object* v_res_375_; 
v_cleanupAnnotations_boxed_373_ = lean_unbox(v_cleanupAnnotations_366_);
v_whnfType_boxed_374_ = lean_unbox(v_whnfType_367_);
v_res_375_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_362_, v_type_363_, v_maxFVars_x3f_364_, v_k_365_, v_cleanupAnnotations_boxed_373_, v_whnfType_boxed_374_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_376_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_383_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_383_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_400_, v_x_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_408_, lean_object* v_mvarId_409_, lean_object* v_x_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_409_, v_x_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_417_, lean_object* v_mvarId_418_, lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_417_, v_mvarId_418_, v_x_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_426_, lean_object* v___x_427_, uint8_t v___x_428_, uint8_t v___x_429_, lean_object* v_xs_430_, lean_object* v_type_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_426_, v_xs_430_, v_type_431_, v___x_427_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_465_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v_fst_439_ = lean_ctor_get(v_a_438_, 0);
v_snd_440_ = lean_ctor_get(v_a_438_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_465_ == 0)
{
v___x_442_ = v_a_438_;
v_isShared_443_ = v_isSharedCheck_465_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_inc(v_fst_439_);
lean_dec(v_a_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_465_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint8_t v___x_444_; lean_object* v___x_445_; 
v___x_444_ = 1;
v___x_445_ = l_Lean_Meta_mkForallFVars(v_xs_430_, v_snd_440_, v___x_428_, v___x_429_, v___x_429_, v___x_444_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_456_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_a_446_);
v___x_451_ = v___x_442_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_fst_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_446_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_del_object(v___x_442_);
lean_dec(v_fst_439_);
v_a_457_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_445_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_445_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_466_, lean_object* v___x_467_, lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v_xs_470_, lean_object* v_type_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_4821__boxed_477_; uint8_t v___x_4822__boxed_478_; lean_object* v_res_479_; 
v___x_4821__boxed_477_ = lean_unbox(v___x_468_);
v___x_4822__boxed_478_ = lean_unbox(v___x_469_);
v_res_479_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_466_, v___x_467_, v___x_4821__boxed_477_, v___x_4822__boxed_478_, v_xs_470_, v_type_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_xs_470_);
lean_dec_ref(v_args_466_);
return v_res_479_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_as_480_, size_t v_i_481_, size_t v_stop_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_eq(v_i_481_, v_stop_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v_hName_x3f_485_; uint8_t v___x_486_; 
v___x_484_ = lean_array_uget_borrowed(v_as_480_, v_i_481_);
v_hName_x3f_485_ = lean_ctor_get(v___x_484_, 2);
v___x_486_ = 1;
if (lean_obj_tag(v_hName_x3f_485_) == 0)
{
if (v___x_483_ == 0)
{
size_t v___x_487_; size_t v___x_488_; 
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_481_, v___x_487_);
v_i_481_ = v___x_488_;
goto _start;
}
else
{
return v___x_486_;
}
}
else
{
return v___x_486_;
}
}
else
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; uint8_t v_res_496_; lean_object* v_r_497_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_491_, v_i_boxed_494_, v_stop_boxed_495_);
lean_dec_ref(v_as_491_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_498_, size_t v_i_499_, lean_object* v_bs_500_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_lt(v_i_499_, v_sz_498_);
if (v___x_501_ == 0)
{
return v_bs_500_;
}
else
{
lean_object* v_v_502_; lean_object* v_expr_503_; lean_object* v___x_504_; lean_object* v_bs_x27_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_v_502_ = lean_array_uget_borrowed(v_bs_500_, v_i_499_);
v_expr_503_ = lean_ctor_get(v_v_502_, 0);
lean_inc_ref(v_expr_503_);
v___x_504_ = lean_unsigned_to_nat(0u);
v_bs_x27_505_ = lean_array_uset(v_bs_500_, v_i_499_, v___x_504_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_add(v_i_499_, v___x_506_);
v___x_508_ = lean_array_uset(v_bs_x27_505_, v_i_499_, v_expr_503_);
v_i_499_ = v___x_507_;
v_bs_500_ = v___x_508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_bs_512_){
_start:
{
size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_sz_boxed_513_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_514_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_513_, v_i_boxed_514_, v_bs_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
lean_object* v_ks_520_; lean_object* v_vs_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_545_; 
v_ks_520_ = lean_ctor_get(v_x_516_, 0);
v_vs_521_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_545_ == 0)
{
v___x_523_ = v_x_516_;
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_vs_521_);
lean_inc(v_ks_520_);
lean_dec(v_x_516_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_ks_520_);
v___x_526_ = lean_nat_dec_lt(v_x_517_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v_x_517_);
v___x_527_ = lean_array_push(v_ks_520_, v_x_518_);
v___x_528_ = lean_array_push(v_vs_521_, v_x_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_528_);
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v_k_x27_532_; uint8_t v___x_533_; 
v_k_x27_532_ = lean_array_fget_borrowed(v_ks_520_, v_x_517_);
v___x_533_ = l_Lean_instBEqMVarId_beq(v_x_518_, v_k_x27_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_535_; 
if (v_isShared_524_ == 0)
{
v___x_535_ = v___x_523_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_ks_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_vs_521_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_x_517_, v___x_536_);
lean_dec(v_x_517_);
v_x_516_ = v___x_535_;
v_x_517_ = v___x_537_;
goto _start;
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_array_fset(v_ks_520_, v_x_517_, v_x_518_);
v___x_541_ = lean_array_fset(v_vs_521_, v_x_517_, v_x_519_);
lean_dec(v_x_517_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_541_);
lean_ctor_set(v___x_523_, 0, v___x_540_);
v___x_543_ = v___x_523_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* v_n_546_, lean_object* v_k_547_, lean_object* v_v_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_546_, v___x_549_, v_k_547_, v_v_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_552_, size_t v_x_553_, size_t v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_es_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_j_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_es_557_ = lean_ctor_get(v_x_552_, 0);
v___x_558_ = ((size_t)31ULL);
v___x_559_ = lean_usize_land(v_x_553_, v___x_558_);
v_j_560_ = lean_usize_to_nat(v___x_559_);
v___x_561_ = lean_array_get_size(v_es_557_);
v___x_562_ = lean_nat_dec_lt(v_j_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v_j_560_);
lean_dec(v_x_556_);
lean_dec(v_x_555_);
return v_x_552_;
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_601_; 
lean_inc_ref(v_es_557_);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_x_552_, 0);
lean_dec(v_unused_602_);
v___x_564_ = v_x_552_;
v_isShared_565_ = v_isSharedCheck_601_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_x_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_601_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_v_566_; lean_object* v___x_567_; lean_object* v_xs_x27_568_; lean_object* v___y_570_; 
v_v_566_ = lean_array_fget(v_es_557_, v_j_560_);
v___x_567_ = lean_box(0);
v_xs_x27_568_ = lean_array_fset(v_es_557_, v_j_560_, v___x_567_);
switch(lean_obj_tag(v_v_566_))
{
case 0:
{
lean_object* v_key_575_; lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_key_575_ = lean_ctor_get(v_v_566_, 0);
v_val_576_ = lean_ctor_get(v_v_566_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_v_566_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_v_566_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_inc(v_key_575_);
lean_dec(v_v_566_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v___x_580_; 
v___x_580_ = l_Lean_instBEqMVarId_beq(v_x_555_, v_key_575_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_del_object(v___x_578_);
v___x_581_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_575_, v_val_576_, v_x_555_, v_x_556_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___y_570_ = v___x_582_;
goto v___jp_569_;
}
else
{
lean_object* v___x_584_; 
lean_dec(v_val_576_);
lean_dec(v_key_575_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_x_556_);
lean_ctor_set(v___x_578_, 0, v_x_555_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_x_555_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_x_556_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_570_ = v___x_584_;
goto v___jp_569_;
}
}
}
}
case 1:
{
lean_object* v_node_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_599_; 
v_node_587_ = lean_ctor_get(v_v_566_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_v_566_);
if (v_isSharedCheck_599_ == 0)
{
v___x_589_ = v_v_566_;
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_node_587_);
lean_dec(v_v_566_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_591_ = ((size_t)5ULL);
v___x_592_ = lean_usize_shift_right(v_x_553_, v___x_591_);
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_x_554_, v___x_593_);
v___x_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_587_, v___x_592_, v___x_594_, v_x_555_, v_x_556_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_595_);
v___x_597_ = v___x_589_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v___y_570_ = v___x_597_;
goto v___jp_569_;
}
}
}
default: 
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_x_555_);
lean_ctor_set(v___x_600_, 1, v_x_556_);
v___y_570_ = v___x_600_;
goto v___jp_569_;
}
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_array_fset(v_xs_x27_568_, v_j_560_, v___y_570_);
lean_dec(v_j_560_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_571_);
v___x_573_ = v___x_564_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
else
{
lean_object* v_ks_603_; lean_object* v_vs_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_624_; 
v_ks_603_ = lean_ctor_get(v_x_552_, 0);
v_vs_604_ = lean_ctor_get(v_x_552_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_624_ == 0)
{
v___x_606_ = v_x_552_;
v_isShared_607_ = v_isSharedCheck_624_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_vs_604_);
lean_inc(v_ks_603_);
lean_dec(v_x_552_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_624_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_ks_603_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_vs_604_);
v___x_609_ = v_reuseFailAlloc_623_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v_newNode_610_; uint8_t v___y_612_; size_t v___x_618_; uint8_t v___x_619_; 
v_newNode_610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_609_, v_x_555_, v_x_556_);
v___x_618_ = ((size_t)7ULL);
v___x_619_ = lean_usize_dec_le(v___x_618_, v_x_554_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_610_);
v___x_621_ = lean_unsigned_to_nat(4u);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
lean_dec(v___x_620_);
v___y_612_ = v___x_622_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_619_;
goto v___jp_611_;
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
lean_object* v_ks_613_; lean_object* v_vs_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_ks_613_ = lean_ctor_get(v_newNode_610_, 0);
lean_inc_ref(v_ks_613_);
v_vs_614_ = lean_ctor_get(v_newNode_610_, 1);
lean_inc_ref(v_vs_614_);
lean_dec_ref(v_newNode_610_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_554_, v_ks_613_, v_vs_614_, v___x_615_, v___x_616_);
lean_dec_ref(v_vs_614_);
lean_dec_ref(v_ks_613_);
return v___x_617_;
}
else
{
return v_newNode_610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_array_get_size(v_keys_626_);
v___x_631_ = lean_nat_dec_lt(v_i_628_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_i_628_);
return v_entries_629_;
}
else
{
lean_object* v_k_632_; lean_object* v_v_633_; uint64_t v___x_634_; size_t v_h_635_; size_t v___x_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v_h_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_k_632_ = lean_array_fget_borrowed(v_keys_626_, v_i_628_);
v_v_633_ = lean_array_fget_borrowed(v_vals_627_, v_i_628_);
v___x_634_ = l_Lean_instHashableMVarId_hash(v_k_632_);
v_h_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = ((size_t)5ULL);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_sub(v_depth_625_, v___x_638_);
v___x_640_ = lean_usize_mul(v___x_636_, v___x_639_);
v_h_641_ = lean_usize_shift_right(v_h_635_, v___x_640_);
v___x_642_ = lean_nat_add(v_i_628_, v___x_637_);
lean_dec(v_i_628_);
lean_inc(v_v_633_);
lean_inc(v_k_632_);
v___x_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_629_, v_h_641_, v_depth_625_, v_k_632_, v_v_633_);
v_i_628_ = v___x_642_;
v_entries_629_ = v___x_643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_645_, lean_object* v_keys_646_, lean_object* v_vals_647_, lean_object* v_i_648_, lean_object* v_entries_649_){
_start:
{
size_t v_depth_boxed_650_; lean_object* v_res_651_; 
v_depth_boxed_650_ = lean_unbox_usize(v_depth_645_);
lean_dec(v_depth_645_);
v_res_651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_650_, v_keys_646_, v_vals_647_, v_i_648_, v_entries_649_);
lean_dec_ref(v_vals_647_);
lean_dec_ref(v_keys_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_5007__boxed_657_; size_t v_x_5008__boxed_658_; lean_object* v_res_659_; 
v_x_5007__boxed_657_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_x_5008__boxed_658_ = lean_unbox_usize(v_x_654_);
lean_dec(v_x_654_);
v_res_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_652_, v_x_5007__boxed_657_, v_x_5008__boxed_658_, v_x_655_, v_x_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint64_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v___x_663_ = l_Lean_instHashableMVarId_hash(v_x_661_);
v___x_664_ = lean_uint64_to_usize(v___x_663_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_660_, v___x_664_, v___x_665_, v_x_661_, v_x_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_667_, lean_object* v_val_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v_mctx_672_; lean_object* v_cache_673_; lean_object* v_zetaDeltaFVarIds_674_; lean_object* v_postponed_675_; lean_object* v_diag_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_704_; 
v___x_671_ = lean_st_ref_take(v___y_669_);
v_mctx_672_ = lean_ctor_get(v___x_671_, 0);
v_cache_673_ = lean_ctor_get(v___x_671_, 1);
v_zetaDeltaFVarIds_674_ = lean_ctor_get(v___x_671_, 2);
v_postponed_675_ = lean_ctor_get(v___x_671_, 3);
v_diag_676_ = lean_ctor_get(v___x_671_, 4);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_704_ == 0)
{
v___x_678_ = v___x_671_;
v_isShared_679_ = v_isSharedCheck_704_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_diag_676_);
lean_inc(v_postponed_675_);
lean_inc(v_zetaDeltaFVarIds_674_);
lean_inc(v_cache_673_);
lean_inc(v_mctx_672_);
lean_dec(v___x_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_704_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_depth_680_; lean_object* v_levelAssignDepth_681_; lean_object* v_lmvarCounter_682_; lean_object* v_mvarCounter_683_; lean_object* v_lDecls_684_; lean_object* v_decls_685_; lean_object* v_userNames_686_; lean_object* v_lAssignment_687_; lean_object* v_eAssignment_688_; lean_object* v_dAssignment_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_703_; 
v_depth_680_ = lean_ctor_get(v_mctx_672_, 0);
v_levelAssignDepth_681_ = lean_ctor_get(v_mctx_672_, 1);
v_lmvarCounter_682_ = lean_ctor_get(v_mctx_672_, 2);
v_mvarCounter_683_ = lean_ctor_get(v_mctx_672_, 3);
v_lDecls_684_ = lean_ctor_get(v_mctx_672_, 4);
v_decls_685_ = lean_ctor_get(v_mctx_672_, 5);
v_userNames_686_ = lean_ctor_get(v_mctx_672_, 6);
v_lAssignment_687_ = lean_ctor_get(v_mctx_672_, 7);
v_eAssignment_688_ = lean_ctor_get(v_mctx_672_, 8);
v_dAssignment_689_ = lean_ctor_get(v_mctx_672_, 9);
v_isSharedCheck_703_ = !lean_is_exclusive(v_mctx_672_);
if (v_isSharedCheck_703_ == 0)
{
v___x_691_ = v_mctx_672_;
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_dAssignment_689_);
lean_inc(v_eAssignment_688_);
lean_inc(v_lAssignment_687_);
lean_inc(v_userNames_686_);
lean_inc(v_decls_685_);
lean_inc(v_lDecls_684_);
lean_inc(v_mvarCounter_683_);
lean_inc(v_lmvarCounter_682_);
lean_inc(v_levelAssignDepth_681_);
lean_inc(v_depth_680_);
lean_dec(v_mctx_672_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_688_, v_mvarId_667_, v_val_668_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 8, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_depth_680_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_levelAssignDepth_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_lmvarCounter_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_mvarCounter_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_lDecls_684_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_decls_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_userNames_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v_lAssignment_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_702_, 9, v_dAssignment_689_);
v___x_695_ = v_reuseFailAlloc_702_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_695_);
v___x_697_ = v___x_678_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_zetaDeltaFVarIds_674_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_postponed_675_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_diag_676_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_st_ref_set(v___y_669_, v___x_697_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_705_, lean_object* v_val_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_705_, v_val_706_, v___y_707_);
lean_dec(v___y_707_);
return v_res_709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_713_, lean_object* v___x_714_, lean_object* v_args_715_, uint8_t v_transparency_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
lean_inc(v___x_714_);
lean_inc(v_mvarId_713_);
v___x_722_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_713_, v___x_714_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; 
lean_dec_ref_known(v___x_722_, 1);
lean_inc(v_mvarId_713_);
v___x_723_ = l_Lean_MVarId_getTag(v_mvarId_713_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
lean_inc(v_mvarId_713_);
v___x_725_ = l_Lean_MVarId_getType(v_mvarId_713_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_841_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_726_, v___y_718_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_841_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_841_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_841_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_715_, v_transparency_716_, v_a_728_, v___x_732_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___y_742_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___x_809_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
v___x_809_ = l_Lean_Meta_isTypeCorrect(v_a_734_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_734_);
v___x_813_ = l_Lean_indentExpr(v_a_734_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_inc(v_mvarId_713_);
v___x_816_ = l_Lean_Meta_throwTacticEx___redArg(v___x_714_, v_mvarId_713_, v___x_815_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_dec_ref_known(v___x_816_, 1);
v___y_760_ = v___y_717_;
v___y_761_ = v___y_718_;
v___y_762_ = v___y_719_;
v___y_763_ = v___y_720_;
goto v___jp_759_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_a_734_);
lean_del_object(v___x_730_);
lean_dec(v_a_724_);
lean_dec_ref(v_args_715_);
lean_dec(v_mvarId_713_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
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
lean_dec(v___x_714_);
v___y_760_ = v___y_717_;
v___y_761_ = v___y_718_;
v___y_762_ = v___y_719_;
v___y_763_ = v___y_720_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_734_);
lean_del_object(v___x_730_);
lean_dec(v_a_724_);
lean_dec_ref(v_args_715_);
lean_dec(v___x_714_);
lean_dec(v_mvarId_713_);
v_a_825_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_809_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_809_);
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
v___jp_735_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_734_, v_a_724_, v___y_740_, v___y_737_, v___y_736_, v___y_739_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_n(v_a_744_, 2);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_mkAppN(v_a_744_, v___y_738_);
lean_dec_ref(v___y_738_);
v___x_746_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_713_, v___x_745_, v___y_737_);
lean_dec_ref(v___x_746_);
v___x_747_ = 1;
v___x_748_ = l_Lean_Expr_mvarId_x21(v_a_744_);
lean_dec(v_a_744_);
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_Meta_introNCore(v___x_748_, v___y_741_, v___x_749_, v___y_742_, v___x_747_, v___y_740_, v___y_737_, v___y_736_, v___y_739_);
return v___x_750_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___y_741_);
lean_dec_ref(v___y_738_);
lean_dec(v_mvarId_713_);
v_a_751_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_743_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_743_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
v___jp_759_:
{
size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_sz_764_ = lean_array_size(v_args_715_);
v___x_765_ = ((size_t)0ULL);
lean_inc_ref(v_args_715_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_764_, v___x_765_, v_args_715_);
v___x_767_ = lean_array_get_size(v_args_715_);
v___x_768_ = lean_nat_dec_lt(v___x_732_, v___x_767_);
if (v___x_768_ == 0)
{
lean_del_object(v___x_730_);
lean_dec_ref(v_args_715_);
v___y_736_ = v___y_762_;
v___y_737_ = v___y_761_;
v___y_738_ = v___x_766_;
v___y_739_ = v___y_763_;
v___y_740_ = v___y_760_;
v___y_741_ = v___x_767_;
v___y_742_ = v___x_768_;
goto v___jp_735_;
}
else
{
if (v___x_768_ == 0)
{
lean_del_object(v___x_730_);
lean_dec_ref(v_args_715_);
v___y_736_ = v___y_762_;
v___y_737_ = v___y_761_;
v___y_738_ = v___x_766_;
v___y_739_ = v___y_763_;
v___y_740_ = v___y_760_;
v___y_741_ = v___x_767_;
v___y_742_ = v___x_768_;
goto v___jp_735_;
}
else
{
size_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_usize_of_nat(v___x_767_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_715_, v___x_765_, v___x_769_);
if (v___x_770_ == 0)
{
lean_del_object(v___x_730_);
lean_dec_ref(v_args_715_);
v___y_736_ = v___y_762_;
v___y_737_ = v___y_761_;
v___y_738_ = v___x_766_;
v___y_739_ = v___y_763_;
v___y_740_ = v___y_760_;
v___y_741_ = v___x_767_;
v___y_742_ = v___x_770_;
goto v___jp_735_;
}
else
{
uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_776_; 
v___x_771_ = 0;
v___x_772_ = lean_box(v___x_771_);
v___x_773_ = lean_box(v___x_770_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_774_, 0, v_args_715_);
lean_closure_set(v___f_774_, 1, v___x_732_);
lean_closure_set(v___f_774_, 2, v___x_772_);
lean_closure_set(v___f_774_, 3, v___x_773_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 1);
lean_ctor_set(v___x_730_, 0, v___x_767_);
v___x_776_ = v___x_730_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_767_);
v___x_776_ = v_reuseFailAlloc_808_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_734_, v___x_776_, v___f_774_, v___x_771_, v___x_771_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_781_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v_fst_779_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_fst_779_);
v_snd_780_ = lean_ctor_get(v_a_778_, 1);
lean_inc(v_snd_780_);
lean_dec(v_a_778_);
v___x_781_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_780_, v_a_724_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_n(v_a_782_, 2);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_mkAppN(v_a_782_, v___x_766_);
lean_dec_ref(v___x_766_);
lean_inc(v_fst_779_);
v___x_784_ = lean_array_mk(v_fst_779_);
v___x_785_ = l_Lean_mkAppN(v___x_783_, v___x_784_);
lean_dec_ref(v___x_784_);
v___x_786_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_713_, v___x_785_, v___y_761_);
lean_dec_ref(v___x_786_);
v___x_787_ = l_Lean_Expr_mvarId_x21(v_a_782_);
lean_dec(v_a_782_);
v___x_788_ = l_List_lengthTR___redArg(v_fst_779_);
lean_dec(v_fst_779_);
v___x_789_ = lean_nat_add(v___x_767_, v___x_788_);
lean_dec(v___x_788_);
v___x_790_ = lean_box(0);
v___x_791_ = l_Lean_Meta_introNCore(v___x_787_, v___x_789_, v___x_790_, v___x_771_, v___x_770_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_791_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_fst_779_);
lean_dec_ref(v___x_766_);
lean_dec(v_mvarId_713_);
v_a_792_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_781_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_781_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___x_766_);
lean_dec(v_a_724_);
lean_dec(v_mvarId_713_);
v_a_800_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_777_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_777_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
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
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_del_object(v___x_730_);
lean_dec(v_a_724_);
lean_dec_ref(v_args_715_);
lean_dec(v___x_714_);
lean_dec(v_mvarId_713_);
v_a_833_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_733_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_733_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_724_);
lean_dec_ref(v_args_715_);
lean_dec(v___x_714_);
lean_dec(v_mvarId_713_);
v_a_842_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_725_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_725_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_args_715_);
lean_dec(v___x_714_);
lean_dec(v_mvarId_713_);
v_a_850_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_723_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_723_);
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
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_args_715_);
lean_dec(v___x_714_);
lean_dec(v_mvarId_713_);
v_a_858_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_722_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_722_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_866_, lean_object* v___x_867_, lean_object* v_args_868_, lean_object* v_transparency_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_transparency_boxed_875_; lean_object* v_res_876_; 
v_transparency_boxed_875_ = lean_unbox(v_transparency_869_);
v_res_876_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_866_, v___x_867_, v_args_868_, v_transparency_boxed_875_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_880_, lean_object* v_args_881_, uint8_t v_transparency_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_889_ = lean_box(v_transparency_882_);
lean_inc(v_mvarId_880_);
v___f_890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_890_, 0, v_mvarId_880_);
lean_closure_set(v___f_890_, 1, v___x_888_);
lean_closure_set(v___f_890_, 2, v_args_881_);
lean_closure_set(v___f_890_, 3, v___x_889_);
v___x_891_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_880_, v___f_890_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_892_, lean_object* v_args_893_, lean_object* v_transparency_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
uint8_t v_transparency_boxed_900_; lean_object* v_res_901_; 
v_transparency_boxed_900_ = lean_unbox(v_transparency_894_);
v_res_901_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_892_, v_args_893_, v_transparency_boxed_900_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_902_, lean_object* v_val_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_902_, v_val_903_, v___y_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_910_, lean_object* v_val_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_910_, v_val_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_919_, v_x_920_, v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_923_, lean_object* v_x_924_, size_t v_x_925_, size_t v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_924_, v_x_925_, v_x_926_, v_x_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
size_t v_x_5586__boxed_936_; size_t v_x_5587__boxed_937_; lean_object* v_res_938_; 
v_x_5586__boxed_936_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_x_5587__boxed_937_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_res_938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_930_, v_x_931_, v_x_5586__boxed_936_, v_x_5587__boxed_937_, v_x_934_, v_x_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_939_, lean_object* v_n_940_, lean_object* v_k_941_, lean_object* v_v_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_940_, v_k_941_, v_v_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_944_, size_t v_depth_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_entries_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_945_, v_keys_946_, v_vals_947_, v_i_949_, v_entries_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_952_, lean_object* v_depth_953_, lean_object* v_keys_954_, lean_object* v_vals_955_, lean_object* v_heq_956_, lean_object* v_i_957_, lean_object* v_entries_958_){
_start:
{
size_t v_depth_boxed_959_; lean_object* v_res_960_; 
v_depth_boxed_959_ = lean_unbox_usize(v_depth_953_);
lean_dec(v_depth_953_);
v_res_960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_952_, v_depth_boxed_959_, v_keys_954_, v_vals_955_, v_heq_956_, v_i_957_, v_entries_958_);
lean_dec_ref(v_vals_955_);
lean_dec_ref(v_keys_954_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_962_, v_x_963_, v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_967_, lean_object* v_args_968_, uint8_t v_transparency_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_967_, v_args_968_, v_transparency_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_976_, lean_object* v_args_977_, lean_object* v_transparency_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
uint8_t v_transparency_boxed_984_; lean_object* v_res_985_; 
v_transparency_boxed_984_ = lean_unbox(v_transparency_978_);
v_res_985_ = l_Lean_MVarId_generalize(v_mvarId_976_, v_args_977_, v_transparency_boxed_984_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_986_, size_t v_sz_987_, size_t v_i_988_, lean_object* v_b_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_990_ == 0)
{
return v_b_989_;
}
else
{
lean_object* v_snd_991_; lean_object* v_fst_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1025_; 
v_snd_991_ = lean_ctor_get(v_b_989_, 1);
v_fst_992_ = lean_ctor_get(v_b_989_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_b_989_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_994_ = v_b_989_;
v_isShared_995_ = v_isSharedCheck_1025_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_991_);
lean_inc(v_fst_992_);
lean_dec(v_b_989_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1025_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_array_996_; lean_object* v_start_997_; lean_object* v_stop_998_; uint8_t v___x_999_; 
v_array_996_ = lean_ctor_get(v_snd_991_, 0);
v_start_997_ = lean_ctor_get(v_snd_991_, 1);
v_stop_998_ = lean_ctor_get(v_snd_991_, 2);
v___x_999_ = lean_nat_dec_lt(v_start_997_, v_stop_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1001_; 
if (v_isShared_995_ == 0)
{
v___x_1001_ = v___x_994_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_snd_991_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1021_; 
lean_inc(v_stop_998_);
lean_inc(v_start_997_);
lean_inc_ref(v_array_996_);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_snd_991_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; 
v_unused_1022_ = lean_ctor_get(v_snd_991_, 2);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_snd_991_, 1);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_snd_991_, 0);
lean_dec(v_unused_1024_);
v___x_1004_ = v_snd_991_;
v_isShared_1005_ = v_isSharedCheck_1021_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v_snd_991_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1021_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v_a_1006_ = lean_array_uget_borrowed(v_as_986_, v_i_988_);
v___x_1007_ = lean_array_fget(v_array_996_, v_start_997_);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_start_997_, v___x_1008_);
lean_dec(v_start_997_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1009_);
v___x_1011_ = v___x_1004_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_array_996_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_stop_998_);
v___x_1011_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = l_Lean_mkFVar(v___x_1007_);
lean_inc(v_a_1006_);
v___x_1013_ = l_Lean_Meta_FVarSubst_insert(v_fst_992_, v_a_1006_, v___x_1012_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_1011_);
lean_ctor_set(v___x_994_, 0, v___x_1013_);
v___x_1015_ = v___x_994_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1011_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
size_t v___x_1016_; size_t v___x_1017_; 
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_add(v_i_988_, v___x_1016_);
v_i_988_ = v___x_1017_;
v_b_989_ = v___x_1015_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1026_, lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_b_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1026_, v_sz_boxed_1030_, v_i_boxed_1031_, v_b_1029_);
lean_dec_ref(v_as_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1033_, size_t v_i_1034_, lean_object* v_bs_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_usize_dec_lt(v_i_1034_, v_sz_1033_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_bs_1035_);
return v___x_1039_;
}
else
{
lean_object* v_v_1040_; lean_object* v_expr_1041_; lean_object* v_xName_x3f_1042_; lean_object* v_hName_x3f_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1066_; 
v_v_1040_ = lean_array_uget(v_bs_1035_, v_i_1034_);
v_expr_1041_ = lean_ctor_get(v_v_1040_, 0);
v_xName_x3f_1042_ = lean_ctor_get(v_v_1040_, 1);
v_hName_x3f_1043_ = lean_ctor_get(v_v_1040_, 2);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_v_1040_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1045_ = v_v_1040_;
v_isShared_1046_ = v_isSharedCheck_1066_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_hName_x3f_1043_);
lean_inc(v_xName_x3f_1042_);
lean_inc(v_expr_1041_);
lean_dec(v_v_1040_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1066_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1041_, v___y_1036_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v_bs_x27_1050_; lean_object* v___x_1052_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = lean_unsigned_to_nat(0u);
v_bs_x27_1050_ = lean_array_uset(v_bs_1035_, v_i_1034_, v___x_1049_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_a_1048_);
v___x_1052_ = v___x_1045_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_xName_x3f_1042_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_hName_x3f_1043_);
v___x_1052_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1034_, v___x_1053_);
v___x_1055_ = lean_array_uset(v_bs_x27_1050_, v_i_1034_, v___x_1052_);
v_i_1034_ = v___x_1054_;
v_bs_1035_ = v___x_1055_;
goto _start;
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_del_object(v___x_1045_);
lean_dec(v_hName_x3f_1043_);
lean_dec(v_xName_x3f_1042_);
lean_dec_ref(v_bs_1035_);
v_a_1058_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1047_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1047_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1067_, lean_object* v_i_1068_, lean_object* v_bs_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1067_);
lean_dec(v_sz_1067_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1072_, v_i_boxed_1073_, v_bs_1069_, v___y_1070_);
lean_dec(v___y_1070_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1075_, lean_object* v_a_1076_, lean_object* v_as_1077_, size_t v_i_1078_, size_t v_stop_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_eq(v_i_1078_, v_stop_1079_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v_expr_1087_; lean_object* v_keyedConfig_1088_; uint8_t v_trackZetaDelta_1089_; lean_object* v_zetaDeltaSet_1090_; lean_object* v_lctx_1091_; lean_object* v_localInstances_1092_; lean_object* v_defEqCtx_x3f_1093_; lean_object* v_synthPendingDepth_1094_; lean_object* v_customCanUnfoldPredicate_x3f_1095_; uint8_t v_univApprox_1096_; uint8_t v_inTypeClassResolution_1097_; uint8_t v_cacheInferType_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1086_ = lean_array_uget_borrowed(v_as_1077_, v_i_1078_);
v_expr_1087_ = lean_ctor_get(v___x_1086_, 0);
v_keyedConfig_1088_ = lean_ctor_get(v___y_1080_, 0);
v_trackZetaDelta_1089_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7);
v_zetaDeltaSet_1090_ = lean_ctor_get(v___y_1080_, 1);
v_lctx_1091_ = lean_ctor_get(v___y_1080_, 2);
v_localInstances_1092_ = lean_ctor_get(v___y_1080_, 3);
v_defEqCtx_x3f_1093_ = lean_ctor_get(v___y_1080_, 4);
v_synthPendingDepth_1094_ = lean_ctor_get(v___y_1080_, 5);
v_customCanUnfoldPredicate_x3f_1095_ = lean_ctor_get(v___y_1080_, 6);
v_univApprox_1096_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1097_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 2);
v_cacheInferType_1098_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 3);
v___x_1099_ = lean_box(0);
lean_inc_ref(v_keyedConfig_1088_);
v___x_1100_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_1075_, v_keyedConfig_1088_);
lean_inc(v_customCanUnfoldPredicate_x3f_1095_);
lean_inc(v_synthPendingDepth_1094_);
lean_inc(v_defEqCtx_x3f_1093_);
lean_inc_ref(v_localInstances_1092_);
lean_inc_ref(v_lctx_1091_);
lean_inc(v_zetaDeltaSet_1090_);
v___x_1101_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_zetaDeltaSet_1090_);
lean_ctor_set(v___x_1101_, 2, v_lctx_1091_);
lean_ctor_set(v___x_1101_, 3, v_localInstances_1092_);
lean_ctor_set(v___x_1101_, 4, v_defEqCtx_x3f_1093_);
lean_ctor_set(v___x_1101_, 5, v_synthPendingDepth_1094_);
lean_ctor_set(v___x_1101_, 6, v_customCanUnfoldPredicate_x3f_1095_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*7, v_trackZetaDelta_1089_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*7 + 1, v_univApprox_1096_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1097_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*7 + 3, v_cacheInferType_1098_);
lean_inc_ref(v_expr_1087_);
lean_inc_ref(v_a_1076_);
v___x_1102_ = l_Lean_Meta_kabstract(v_a_1076_, v_expr_1087_, v___x_1099_, v___x_1101_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref_known(v___x_1101_, 7);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1115_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_Expr_hasLooseBVars(v_a_1103_);
lean_dec(v_a_1103_);
if (v___x_1107_ == 0)
{
size_t v___x_1108_; size_t v___x_1109_; 
lean_del_object(v___x_1105_);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1078_, v___x_1108_);
v_i_1078_ = v___x_1109_;
goto _start;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec_ref(v_a_1076_);
v___x_1111_ = lean_box(v___x_1107_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1111_);
v___x_1113_ = v___x_1105_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_a_1076_);
v_a_1116_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1102_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1102_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref(v_a_1076_);
v___x_1124_ = 0;
v___x_1125_ = lean_box(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1127_, lean_object* v_a_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_transparency_boxed_1137_; size_t v_i_boxed_1138_; size_t v_stop_boxed_1139_; lean_object* v_res_1140_; 
v_transparency_boxed_1137_ = lean_unbox(v_transparency_1127_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1139_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1137_, v_a_1128_, v_as_1129_, v_i_boxed_1138_, v_stop_boxed_1139_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1141_, lean_object* v___x_1142_, uint8_t v_transparency_1143_, lean_object* v_as_1144_, size_t v_i_1145_, size_t v_stop_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_a_1154_; uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_eq(v_i_1145_, v_stop_1146_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; uint8_t v_a_1161_; lean_object* v___x_1163_; 
v___x_1159_ = lean_array_uget_borrowed(v_as_1144_, v_i_1145_);
lean_inc(v___x_1159_);
v___x_1163_ = l_Lean_FVarId_getType___redArg(v___x_1159_, v___y_1148_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1164_, v___y_1149_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_eq(v___x_1142_, v___x_1167_);
v___x_1169_ = lean_array_get_size(v_a_1141_);
v___x_1170_ = lean_nat_dec_lt(v___x_1167_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_dec(v_a_1166_);
v_a_1161_ = v___x_1168_;
goto v___jp_1160_;
}
else
{
if (v___x_1170_ == 0)
{
lean_dec(v_a_1166_);
v_a_1161_ = v___x_1168_;
goto v___jp_1160_;
}
else
{
size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = lean_usize_of_nat(v___x_1169_);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1143_, v_a_1166_, v_a_1141_, v___x_1171_, v___x_1172_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; uint8_t v___x_1175_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = lean_unbox(v_a_1174_);
lean_dec(v_a_1174_);
v_a_1161_ = v___x_1175_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_b_1147_);
v_a_1176_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1173_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1173_);
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
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_b_1147_);
v_a_1184_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1165_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1165_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_b_1147_);
v_a_1192_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1163_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1163_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
v___jp_1160_:
{
if (v_a_1161_ == 0)
{
v_a_1154_ = v_b_1147_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1162_; 
lean_inc(v___x_1159_);
v___x_1162_ = lean_array_push(v_b_1147_, v___x_1159_);
v_a_1154_ = v___x_1162_;
goto v___jp_1153_;
}
}
}
else
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_b_1147_);
return v___x_1200_;
}
v___jp_1153_:
{
size_t v___x_1155_; size_t v___x_1156_; 
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1145_, v___x_1155_);
v_i_1145_ = v___x_1156_;
v_b_1147_ = v_a_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1201_, lean_object* v___x_1202_, lean_object* v_transparency_1203_, lean_object* v_as_1204_, lean_object* v_i_1205_, lean_object* v_stop_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_transparency_boxed_1213_; size_t v_i_boxed_1214_; size_t v_stop_boxed_1215_; lean_object* v_res_1216_; 
v_transparency_boxed_1213_ = lean_unbox(v_transparency_1203_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1205_);
lean_dec(v_i_1205_);
v_stop_boxed_1215_ = lean_unbox_usize(v_stop_1206_);
lean_dec(v_stop_1206_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1201_, v___x_1202_, v_transparency_boxed_1213_, v_as_1204_, v_i_boxed_1214_, v_stop_boxed_1215_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_as_1204_);
lean_dec(v___x_1202_);
lean_dec_ref(v_a_1201_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1217_, lean_object* v_a_1218_, lean_object* v___x_1219_, lean_object* v_as_1220_, size_t v_i_1221_, size_t v_stop_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_a_1230_; uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_eq(v_i_1221_, v_stop_1222_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v_a_1237_; lean_object* v___x_1239_; 
v___x_1235_ = lean_array_uget_borrowed(v_as_1220_, v_i_1221_);
lean_inc(v___x_1235_);
v___x_1239_ = l_Lean_FVarId_getType___redArg(v___x_1235_, v___y_1224_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1240_, v___y_1225_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_nat_dec_eq(v___x_1219_, v___x_1243_);
v___x_1245_ = lean_array_get_size(v_a_1218_);
v___x_1246_ = lean_nat_dec_lt(v___x_1243_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v_a_1242_);
v_a_1237_ = v___x_1244_;
goto v___jp_1236_;
}
else
{
if (v___x_1246_ == 0)
{
lean_dec(v_a_1242_);
v_a_1237_ = v___x_1244_;
goto v___jp_1236_;
}
else
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = lean_usize_of_nat(v___x_1245_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1217_, v_a_1242_, v_a_1218_, v___x_1247_, v___x_1248_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
v_a_1237_ = v___x_1251_;
goto v___jp_1236_;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_b_1223_);
v_a_1252_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1249_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1249_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_b_1223_);
v_a_1260_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1241_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1241_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_b_1223_);
v_a_1268_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1239_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1239_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
v___jp_1236_:
{
if (v_a_1237_ == 0)
{
v_a_1230_ = v_b_1223_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1238_; 
lean_inc(v___x_1235_);
v___x_1238_ = lean_array_push(v_b_1223_, v___x_1235_);
v_a_1230_ = v___x_1238_;
goto v___jp_1229_;
}
}
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_b_1223_);
return v___x_1276_;
}
v___jp_1229_:
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_i_1221_, v___x_1231_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1218_, v___x_1219_, v_transparency_1217_, v_as_1220_, v___x_1232_, v_stop_1222_, v_a_1230_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1277_, lean_object* v_a_1278_, lean_object* v___x_1279_, lean_object* v_as_1280_, lean_object* v_i_1281_, lean_object* v_stop_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_transparency_boxed_1289_; size_t v_i_boxed_1290_; size_t v_stop_boxed_1291_; lean_object* v_res_1292_; 
v_transparency_boxed_1289_ = lean_unbox(v_transparency_1277_);
v_i_boxed_1290_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_stop_boxed_1291_ = lean_unbox_usize(v_stop_1282_);
lean_dec(v_stop_1282_);
v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1289_, v_a_1278_, v___x_1279_, v_as_1280_, v_i_boxed_1290_, v_stop_boxed_1291_, v_b_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_as_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1295_, lean_object* v_args_1296_, lean_object* v_hyps_1297_, lean_object* v_fvarSubst_1298_, uint8_t v_transparency_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_array_get_size(v_hyps_1297_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
size_t v_sz_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v_sz_1308_ = lean_array_size(v_args_1296_);
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1308_, v___x_1309_, v_args_1296_, v_a_1301_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; uint8_t v___x_1312_; lean_object* v_a_1314_; lean_object* v___y_1388_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = 1;
v___x_1398_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1399_ = lean_nat_dec_lt(v___x_1306_, v___x_1305_);
if (v___x_1399_ == 0)
{
v_a_1314_ = v___x_1398_;
goto v___jp_1313_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_le(v___x_1305_, v___x_1305_);
if (v___x_1400_ == 0)
{
if (v___x_1399_ == 0)
{
v_a_1314_ = v___x_1398_;
goto v___jp_1313_;
}
else
{
size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_usize_of_nat(v___x_1305_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1299_, v_a_1311_, v___x_1305_, v_hyps_1297_, v___x_1309_, v___x_1401_, v___x_1398_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
v___y_1388_ = v___x_1402_;
goto v___jp_1387_;
}
}
else
{
size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_usize_of_nat(v___x_1305_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1299_, v_a_1311_, v___x_1305_, v_hyps_1297_, v___x_1309_, v___x_1403_, v___x_1398_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
v___y_1388_ = v___x_1404_;
goto v___jp_1387_;
}
}
v___jp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_MVarId_revert(v_mvarId_1295_, v_a_1314_, v___x_1312_, v___x_1307_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_fst_1317_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_a_1316_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_a_1316_);
v___x_1319_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1318_, v_a_1311_, v_transparency_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1370_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v_fst_1321_ = lean_ctor_get(v_a_1320_, 0);
v_snd_1322_ = lean_ctor_get(v_a_1320_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1324_ = v_a_1320_;
v_isShared_1325_ = v_isSharedCheck_1370_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snd_1322_);
lean_inc(v_fst_1321_);
lean_dec(v_a_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1370_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_array_get_size(v_fst_1317_);
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Lean_Meta_introNCore(v_snd_1322_, v___x_1326_, v___x_1327_, v___x_1307_, v___x_1312_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1361_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1361_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1361_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1360_; 
v_fst_1333_ = lean_ctor_get(v_a_1329_, 0);
v_snd_1334_ = lean_ctor_get(v_a_1329_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_a_1329_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1336_ = v_a_1329_;
v_isShared_1337_ = v_isSharedCheck_1360_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1334_);
lean_inc(v_fst_1333_);
lean_dec(v_a_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1360_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = lean_array_get_size(v_fst_1333_);
v___x_1339_ = l_Array_toSubarray___redArg(v_fst_1333_, v___x_1306_, v___x_1338_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1339_);
lean_ctor_set(v___x_1336_, 0, v_fvarSubst_1298_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fvarSubst_1298_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
size_t v_sz_1342_; lean_object* v___x_1343_; lean_object* v_fst_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1357_; 
v_sz_1342_ = lean_array_size(v_fst_1317_);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1317_, v_sz_1342_, v___x_1309_, v___x_1341_);
lean_dec(v_fst_1317_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1343_, 1);
lean_dec(v_unused_1358_);
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_fst_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_snd_1334_);
lean_ctor_set(v___x_1346_, 0, v_fst_1321_);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_fst_1321_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1334_);
v___x_1349_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1349_);
lean_ctor_set(v___x_1324_, 0, v_fst_1344_);
v___x_1351_ = v___x_1324_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1351_);
v___x_1353_ = v___x_1331_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
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
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1324_);
lean_dec(v_fst_1321_);
lean_dec(v_fst_1317_);
lean_dec(v_fvarSubst_1298_);
v_a_1362_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1328_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1328_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_fst_1317_);
lean_dec(v_fvarSubst_1298_);
v_a_1371_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1319_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1319_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1311_);
lean_dec(v_fvarSubst_1298_);
v_a_1379_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1315_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1315_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
v___jp_1387_:
{
if (lean_obj_tag(v___y_1388_) == 0)
{
lean_object* v_a_1389_; 
v_a_1389_ = lean_ctor_get(v___y_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___y_1388_, 1);
v_a_1314_ = v_a_1389_;
goto v___jp_1313_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1311_);
lean_dec(v_fvarSubst_1298_);
lean_dec(v_mvarId_1295_);
v_a_1390_ = lean_ctor_get(v___y_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___y_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___y_1388_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___y_1388_);
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
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_fvarSubst_1298_);
lean_dec(v_mvarId_1295_);
v_a_1405_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1310_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1310_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1295_, v_args_1296_, v_transparency_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_fvarSubst_1298_);
lean_ctor_set(v___x_1418_, 1, v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_fvarSubst_1298_);
v_a_1423_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1413_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1413_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1431_, lean_object* v_args_1432_, lean_object* v_hyps_1433_, lean_object* v_fvarSubst_1434_, lean_object* v_transparency_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
uint8_t v_transparency_boxed_1441_; lean_object* v_res_1442_; 
v_transparency_boxed_1441_ = lean_unbox(v_transparency_1435_);
v_res_1442_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1431_, v_args_1432_, v_hyps_1433_, v_fvarSubst_1434_, v_transparency_boxed_1441_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_hyps_1433_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1443_, size_t v_i_1444_, lean_object* v_bs_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1443_, v_i_1444_, v_bs_1445_, v___y_1447_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1452_, lean_object* v_i_1453_, lean_object* v_bs_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
size_t v_sz_boxed_1460_; size_t v_i_boxed_1461_; lean_object* v_res_1462_; 
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1452_);
lean_dec(v_sz_1452_);
v_i_boxed_1461_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1460_, v_i_boxed_1461_, v_bs_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1462_;
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
