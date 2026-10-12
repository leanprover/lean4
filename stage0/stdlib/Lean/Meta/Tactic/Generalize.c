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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(lean_object* v_e_12_, lean_object* v___y_13_){
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
v___x_32_ = lean_st_ref_put(v___y_13_, v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v_fst_20_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_12_ = stack[0].m_obj;
lean_object* v___y_13_ = stack[1].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_12_, v___y_13_);
stack->m_obj
 = v_res_37_;
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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_e_42_, v___y_44_);
return v___x_48_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v___y_44_ = stack[2].m_obj;
lean_object* v___y_45_ = stack[3].m_obj;
lean_object* v___y_46_ = stack[4].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(v_e_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object* v_e_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(v_e_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object* v_args_60_, uint8_t v_transparency_61_, lean_object* v_target_62_, lean_object* v_i_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_array_get_size(v_args_60_);
v___x_70_ = lean_nat_dec_lt(v_i_63_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v_target_62_);
return v___x_71_;
}
else
{
lean_object* v_arg_72_; lean_object* v_expr_73_; lean_object* v_xName_x3f_74_; lean_object* v___x_75_; 
v_arg_72_ = lean_array_fget_borrowed(v_args_60_, v_i_63_);
v_expr_73_ = lean_ctor_get(v_arg_72_, 0);
v_xName_x3f_74_ = lean_ctor_get(v_arg_72_, 1);
lean_inc_ref(v_expr_73_);
v___x_75_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_73_, v_a_65_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_n(v_a_76_, 2);
lean_dec_ref_known(v___x_75_, 1);
lean_inc(v_a_67_);
lean_inc_ref(v_a_66_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
v___x_77_ = lean_infer_type(v_a_76_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_78_, v_a_65_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_i_63_, v___x_102_);
v___x_104_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_60_, v_transparency_61_, v_target_62_, v___x_103_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v___x_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_xName_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
if (lean_obj_tag(v_xName_x3f_74_) == 1)
{
lean_object* v_val_131_; 
v_val_131_ = lean_ctor_get(v_xName_x3f_74_, 0);
lean_inc(v_val_131_);
v_xName_107_ = v_val_131_;
v___y_108_ = v_a_64_;
v___y_109_ = v_a_65_;
v___y_110_ = v_a_66_;
v___y_111_ = v_a_67_;
goto v___jp_106_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
v___x_133_ = l_Lean_Core_mkFreshUserName(v___x_132_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v_xName_107_ = v_a_134_;
v___y_108_ = v_a_64_;
v___y_109_ = v_a_65_;
v___y_110_ = v_a_66_;
v___y_111_ = v_a_67_;
goto v___jp_106_;
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_a_105_);
lean_dec(v_a_80_);
lean_dec(v_a_76_);
v_a_135_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_133_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
v___jp_106_:
{
lean_object* v___x_112_; uint8_t v_transparency_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_112_ = l_Lean_Meta_Context_config(v___y_108_);
v_transparency_113_ = lean_ctor_get_uint8(v___x_112_, 9);
lean_dec_ref(v___x_112_);
v___x_114_ = lean_box(0);
v___x_115_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_113_, v_transparency_61_);
if (v___x_115_ == 0)
{
lean_object* v_keyedConfig_116_; uint8_t v_trackZetaDelta_117_; lean_object* v_zetaDeltaSet_118_; lean_object* v_lctx_119_; lean_object* v_localInstances_120_; lean_object* v_defEqCtx_x3f_121_; lean_object* v_synthPendingDepth_122_; lean_object* v_customCanUnfoldPredicate_x3f_123_; uint8_t v_univApprox_124_; uint8_t v_inTypeClassResolution_125_; uint8_t v_cacheInferType_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_keyedConfig_116_ = lean_ctor_get(v___y_108_, 0);
v_trackZetaDelta_117_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*7);
v_zetaDeltaSet_118_ = lean_ctor_get(v___y_108_, 1);
v_lctx_119_ = lean_ctor_get(v___y_108_, 2);
v_localInstances_120_ = lean_ctor_get(v___y_108_, 3);
v_defEqCtx_x3f_121_ = lean_ctor_get(v___y_108_, 4);
v_synthPendingDepth_122_ = lean_ctor_get(v___y_108_, 5);
v_customCanUnfoldPredicate_x3f_123_ = lean_ctor_get(v___y_108_, 6);
v_univApprox_124_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_125_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*7 + 2);
v_cacheInferType_126_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_116_);
v___x_127_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_61_, v_keyedConfig_116_);
lean_inc(v_customCanUnfoldPredicate_x3f_123_);
lean_inc(v_synthPendingDepth_122_);
lean_inc(v_defEqCtx_x3f_121_);
lean_inc_ref(v_localInstances_120_);
lean_inc_ref(v_lctx_119_);
lean_inc(v_zetaDeltaSet_118_);
v___x_128_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_zetaDeltaSet_118_);
lean_ctor_set(v___x_128_, 2, v_lctx_119_);
lean_ctor_set(v___x_128_, 3, v_localInstances_120_);
lean_ctor_set(v___x_128_, 4, v_defEqCtx_x3f_121_);
lean_ctor_set(v___x_128_, 5, v_synthPendingDepth_122_);
lean_ctor_set(v___x_128_, 6, v_customCanUnfoldPredicate_x3f_123_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*7, v_trackZetaDelta_117_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*7 + 1, v_univApprox_124_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*7 + 2, v_inTypeClassResolution_125_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*7 + 3, v_cacheInferType_126_);
v___x_129_ = l_Lean_Meta_kabstract(v_a_105_, v_a_76_, v___x_114_, v___x_128_, v___y_109_, v___y_110_, v___y_111_);
lean_dec_ref_known(v___x_128_, 7);
v___y_82_ = v_xName_107_;
v___y_83_ = v___x_129_;
goto v___jp_81_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_kabstract(v_a_105_, v_a_76_, v___x_114_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
v___y_82_ = v_xName_107_;
v___y_83_ = v___x_130_;
goto v___jp_81_;
}
}
}
else
{
lean_dec(v_a_80_);
lean_dec(v_a_76_);
return v___x_104_;
}
v___jp_81_:
{
if (lean_obj_tag(v___y_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_93_; 
v_a_84_ = lean_ctor_get(v___y_83_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___y_83_);
if (v_isSharedCheck_93_ == 0)
{
v___x_86_ = v___y_83_;
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___y_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_88_ = 0;
v___x_89_ = l_Lean_mkForall(v___y_82_, v___x_88_, v_a_80_, v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_89_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v___y_82_);
lean_dec(v_a_80_);
v_a_94_ = lean_ctor_get(v___y_83_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___y_83_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___y_83_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___y_83_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
else
{
lean_dec(v_a_76_);
lean_dec_ref(v_target_62_);
return v___x_79_;
}
}
else
{
lean_dec(v_a_76_);
lean_dec_ref(v_target_62_);
return v___x_77_;
}
}
else
{
lean_dec_ref(v_target_62_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_60_ = stack[0].m_obj;
uint8_t v_transparency_61_ = stack[1].m_num;
lean_object* v_target_62_ = stack[2].m_obj;
lean_object* v_i_63_ = stack[3].m_obj;
lean_object* v_a_64_ = stack[4].m_obj;
lean_object* v_a_65_ = stack[5].m_obj;
lean_object* v_a_66_ = stack[6].m_obj;
lean_object* v_a_67_ = stack[7].m_obj;
lean_object* v_res_143_;
v_res_143_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_60_, v_transparency_61_, v_target_62_, v_i_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_144_, lean_object* v_transparency_145_, lean_object* v_target_146_, lean_object* v_i_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
uint8_t v_transparency_boxed_153_; lean_object* v_res_154_; 
v_transparency_boxed_153_ = lean_unbox(v_transparency_145_);
v_res_154_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_144_, v_transparency_boxed_153_, v_target_146_, v_i_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_i_147_);
lean_dec_ref(v_args_144_);
return v_res_154_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_155_, lean_object* v_xs_156_, lean_object* v_type_157_, lean_object* v_i_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v_xs_156_);
v___x_165_ = lean_nat_dec_lt(v_i_158_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_i_158_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_type_157_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v_arg_170_; lean_object* v_hName_x3f_171_; 
v___x_169_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_170_ = lean_array_get_borrowed(v___x_169_, v_args_155_, v_i_158_);
v_hName_x3f_171_ = lean_ctor_get(v_arg_170_, 2);
if (lean_obj_tag(v_hName_x3f_171_) == 1)
{
lean_object* v_expr_172_; lean_object* v_val_173_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_expr_172_ = lean_ctor_get(v_arg_170_, 0);
v_val_173_ = lean_ctor_get(v_hName_x3f_171_, 0);
v___x_204_ = lean_array_fget_borrowed(v_xs_156_, v_i_158_);
lean_inc(v_a_162_);
lean_inc_ref(v_a_161_);
lean_inc(v_a_160_);
lean_inc_ref(v_a_159_);
lean_inc(v___x_204_);
v___x_205_ = lean_infer_type(v___x_204_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
lean_inc_ref(v_expr_172_);
v___x_207_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_172_, v_a_160_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_n(v_a_208_, 2);
lean_dec_ref_known(v___x_207_, 1);
lean_inc(v_a_162_);
lean_inc_ref(v_a_161_);
lean_inc(v_a_160_);
lean_inc_ref(v_a_159_);
v___x_209_ = lean_infer_type(v_a_208_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_210_, v_a_160_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_Lean_Meta_isExprDefEq(v_a_206_, v_a_212_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = lean_unbox(v_a_214_);
lean_dec(v_a_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_inc(v___x_204_);
lean_inc(v_a_208_);
v___x_216_ = l_Lean_Meta_mkHEq(v_a_208_, v___x_204_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = l_Lean_Meta_mkHEqRefl(v_a_208_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v_fst_175_ = v_a_217_;
v_snd_176_ = v_a_219_;
v___y_177_ = v_a_159_;
v___y_178_ = v_a_160_;
v___y_179_ = v_a_161_;
v___y_180_ = v_a_162_;
goto v___jp_174_;
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_217_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_220_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_218_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_208_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_228_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_216_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_216_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v___x_236_; 
lean_inc(v___x_204_);
lean_inc(v_a_208_);
v___x_236_ = l_Lean_Meta_mkEq(v_a_208_, v___x_204_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = l_Lean_Meta_mkEqRefl(v_a_208_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v_fst_175_ = v_a_237_;
v_snd_176_ = v_a_239_;
v___y_177_ = v_a_159_;
v___y_178_ = v_a_160_;
v___y_179_ = v_a_161_;
v___y_180_ = v_a_162_;
goto v___jp_174_;
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_237_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_240_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_238_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_208_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_248_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_236_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_236_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_208_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_256_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_213_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_213_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_208_);
lean_dec(v_a_206_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_264_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_211_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_211_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v_a_208_);
lean_dec(v_a_206_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_272_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_209_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_209_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v_a_206_);
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_280_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_207_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_207_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_i_158_);
lean_dec_ref(v_type_157_);
v_a_288_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_205_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_205_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
v___jp_174_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_158_, v___x_181_);
lean_dec(v_i_158_);
v___x_183_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_155_, v_xs_156_, v_type_157_, v___x_182_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_203_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_203_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_203_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_203_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_202_; 
v_fst_188_ = lean_ctor_get(v_a_184_, 0);
v_snd_189_ = lean_ctor_get(v_a_184_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_184_);
if (v_isSharedCheck_202_ == 0)
{
v___x_191_ = v_a_184_;
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snd_189_);
lean_inc(v_fst_188_);
lean_dec(v_a_184_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_snd_176_);
lean_ctor_set(v___x_193_, 1, v_fst_188_);
v___x_194_ = 0;
lean_inc(v_val_173_);
v___x_195_ = l_Lean_mkForall(v_val_173_, v___x_194_, v_fst_175_, v_snd_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_195_);
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_197_ = v___x_191_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_197_);
v___x_199_ = v___x_186_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_176_);
lean_dec_ref(v_fst_175_);
return v___x_183_;
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_158_, v___x_296_);
lean_dec(v_i_158_);
v_i_158_ = v___x_297_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_155_ = stack[0].m_obj;
lean_object* v_xs_156_ = stack[1].m_obj;
lean_object* v_type_157_ = stack[2].m_obj;
lean_object* v_i_158_ = stack[3].m_obj;
lean_object* v_a_159_ = stack[4].m_obj;
lean_object* v_a_160_ = stack[5].m_obj;
lean_object* v_a_161_ = stack[6].m_obj;
lean_object* v_a_162_ = stack[7].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_155_, v_xs_156_, v_type_157_, v_i_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_300_, lean_object* v_xs_301_, lean_object* v_type_302_, lean_object* v_i_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_300_, v_xs_301_, v_type_302_, v_i_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec_ref(v_xs_301_);
lean_dec_ref(v_args_300_);
return v_res_309_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* v_k_310_, lean_object* v_b_311_, lean_object* v_c_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
v___x_318_ = lean_apply_7(v_k_310_, v_b_311_, v_c_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, lean_box(0));
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_310_ = stack[0].m_obj;
lean_object* v_b_311_ = stack[1].m_obj;
lean_object* v_c_312_ = stack[2].m_obj;
lean_object* v___y_313_ = stack[3].m_obj;
lean_object* v___y_314_ = stack[4].m_obj;
lean_object* v___y_315_ = stack[5].m_obj;
lean_object* v___y_316_ = stack[6].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_310_, v_b_311_, v_c_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* v_k_320_, lean_object* v_b_321_, lean_object* v_c_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_320_, v_b_321_, v_c_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_328_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* v_type_329_, lean_object* v_maxFVars_x3f_330_, lean_object* v_k_331_, uint8_t v_cleanupAnnotations_332_, uint8_t v_whnfType_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_339_, 0, v_k_331_);
v___x_340_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_329_, v_maxFVars_x3f_330_, v___f_339_, v_cleanupAnnotations_332_, v_whnfType_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_340_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_340_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_329_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_330_ = stack[1].m_obj;
lean_object* v_k_331_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_332_ = stack[3].m_num;
uint8_t v_whnfType_333_ = stack[4].m_num;
lean_object* v___y_334_ = stack[5].m_obj;
lean_object* v___y_335_ = stack[6].m_obj;
lean_object* v___y_336_ = stack[7].m_obj;
lean_object* v___y_337_ = stack[8].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_329_, v_maxFVars_x3f_330_, v_k_331_, v_cleanupAnnotations_332_, v_whnfType_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* v_type_358_, lean_object* v_maxFVars_x3f_359_, lean_object* v_k_360_, lean_object* v_cleanupAnnotations_361_, lean_object* v_whnfType_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_368_; uint8_t v_whnfType_boxed_369_; lean_object* v_res_370_; 
v_cleanupAnnotations_boxed_368_ = lean_unbox(v_cleanupAnnotations_361_);
v_whnfType_boxed_369_ = lean_unbox(v_whnfType_362_);
v_res_370_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_358_, v_maxFVars_x3f_359_, v_k_360_, v_cleanupAnnotations_boxed_368_, v_whnfType_boxed_369_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_370_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_00_u03b1_371_, lean_object* v_type_372_, lean_object* v_maxFVars_x3f_373_, lean_object* v_k_374_, uint8_t v_cleanupAnnotations_375_, uint8_t v_whnfType_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_372_, v_maxFVars_x3f_373_, v_k_374_, v_cleanupAnnotations_375_, v_whnfType_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_372_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_373_ = stack[2].m_obj;
lean_object* v_k_374_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_375_ = stack[4].m_num;
uint8_t v_whnfType_376_ = stack[5].m_num;
lean_object* v___y_377_ = stack[6].m_obj;
lean_object* v___y_378_ = stack[7].m_obj;
lean_object* v___y_379_ = stack[8].m_obj;
lean_object* v___y_380_ = stack[9].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_box(0), v_type_372_, v_maxFVars_x3f_373_, v_k_374_, v_cleanupAnnotations_375_, v_whnfType_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_00_u03b1_384_, lean_object* v_type_385_, lean_object* v_maxFVars_x3f_386_, lean_object* v_k_387_, lean_object* v_cleanupAnnotations_388_, lean_object* v_whnfType_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_395_; uint8_t v_whnfType_boxed_396_; lean_object* v_res_397_; 
v_cleanupAnnotations_boxed_395_ = lean_unbox(v_cleanupAnnotations_388_);
v_whnfType_boxed_396_ = lean_unbox(v_whnfType_389_);
v_res_397_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_384_, v_type_385_, v_maxFVars_x3f_386_, v_k_387_, v_cleanupAnnotations_boxed_395_, v_whnfType_boxed_396_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_397_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_414_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_405_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_398_ = stack[0].m_obj;
lean_object* v_x_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v___y_402_ = stack[4].m_obj;
lean_object* v___y_403_ = stack[5].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_423_, lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_423_, v_x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_431_, lean_object* v_mvarId_432_, lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_432_, v_x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_432_ = stack[1].m_obj;
lean_object* v_x_433_ = stack[2].m_obj;
lean_object* v___y_434_ = stack[3].m_obj;
lean_object* v___y_435_ = stack[4].m_obj;
lean_object* v___y_436_ = stack[5].m_obj;
lean_object* v___y_437_ = stack[6].m_obj;
lean_object* v_res_440_;
v_res_440_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_box(0), v_mvarId_432_, v_x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_441_, lean_object* v_mvarId_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_441_, v_mvarId_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_449_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_450_, lean_object* v___x_451_, uint8_t v___x_452_, uint8_t v___x_453_, lean_object* v_xs_454_, lean_object* v_type_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_450_, v_xs_454_, v_type_455_, v___x_451_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_489_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v_fst_463_ = lean_ctor_get(v_a_462_, 0);
v_snd_464_ = lean_ctor_get(v_a_462_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_489_ == 0)
{
v___x_466_ = v_a_462_;
v_isShared_467_ = v_isSharedCheck_489_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_a_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_489_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; lean_object* v___x_469_; 
v___x_468_ = 1;
v___x_469_ = l_Lean_Meta_mkForallFVars(v_xs_454_, v_snd_464_, v___x_452_, v___x_453_, v___x_453_, v___x_468_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_480_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v_a_470_);
v___x_475_ = v___x_466_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_463_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_a_470_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_466_);
lean_dec(v_fst_463_);
v_a_481_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_469_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_469_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
return v___x_461_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_450_ = stack[0].m_obj;
lean_object* v___x_451_ = stack[1].m_obj;
uint8_t v___x_452_ = stack[2].m_num;
uint8_t v___x_453_ = stack[3].m_num;
lean_object* v_xs_454_ = stack[4].m_obj;
lean_object* v_type_455_ = stack[5].m_obj;
lean_object* v___y_456_ = stack[6].m_obj;
lean_object* v___y_457_ = stack[7].m_obj;
lean_object* v___y_458_ = stack[8].m_obj;
lean_object* v___y_459_ = stack[9].m_obj;
lean_object* v_res_490_;
v_res_490_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_450_, v___x_451_, v___x_452_, v___x_453_, v_xs_454_, v_type_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v_xs_495_, lean_object* v_type_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___x_4497__boxed_502_; uint8_t v___x_4498__boxed_503_; lean_object* v_res_504_; 
v___x_4497__boxed_502_ = lean_unbox(v___x_493_);
v___x_4498__boxed_503_ = lean_unbox(v___x_494_);
v_res_504_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_491_, v___x_492_, v___x_4497__boxed_502_, v___x_4498__boxed_503_, v_xs_495_, v_type_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec_ref(v_xs_495_);
lean_dec_ref(v_args_491_);
return v_res_504_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v_hName_x3f_510_; 
v___x_509_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
v_hName_x3f_510_ = lean_ctor_get(v___x_509_, 2);
if (lean_obj_tag(v_hName_x3f_510_) == 0)
{
size_t v___x_511_; size_t v___x_512_; 
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_506_, v___x_511_);
v_i_506_ = v___x_512_;
goto _start;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = 1;
return v___x_514_;
}
}
else
{
uint8_t v___x_515_; 
v___x_515_ = 0;
return v___x_515_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_505_ = stack[0].m_obj;
size_t v_i_506_ = stack[1].m_num;
size_t v_stop_507_ = stack[2].m_num;
uint8_t v_res_516_;
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_505_, v_i_506_, v_stop_507_);
stack->m_num = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_stop_519_){
_start:
{
size_t v_i_boxed_520_; size_t v_stop_boxed_521_; uint8_t v_res_522_; lean_object* v_r_523_; 
v_i_boxed_520_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_stop_boxed_521_ = lean_unbox_usize(v_stop_519_);
lean_dec(v_stop_519_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_517_, v_i_boxed_520_, v_stop_boxed_521_);
lean_dec_ref(v_as_517_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_524_, size_t v_i_525_, lean_object* v_bs_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_525_, v_sz_524_);
if (v___x_527_ == 0)
{
return v_bs_526_;
}
else
{
lean_object* v_v_528_; lean_object* v_expr_529_; lean_object* v___x_530_; lean_object* v_bs_x27_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v_v_528_ = lean_array_uget_borrowed(v_bs_526_, v_i_525_);
v_expr_529_ = lean_ctor_get(v_v_528_, 0);
lean_inc_ref(v_expr_529_);
v___x_530_ = lean_unsigned_to_nat(0u);
v_bs_x27_531_ = lean_array_uset(v_bs_526_, v_i_525_, v___x_530_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_525_, v___x_532_);
v___x_534_ = lean_array_uset(v_bs_x27_531_, v_i_525_, v_expr_529_);
v_i_525_ = v___x_533_;
v_bs_526_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_524_ = stack[0].m_num;
size_t v_i_525_ = stack[1].m_num;
lean_object* v_bs_526_ = stack[2].m_obj;
lean_object* v_res_536_;
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_524_, v_i_525_, v_bs_526_);
stack->m_obj
 = v_res_536_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_ks_547_; lean_object* v_vs_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_572_; 
v_ks_547_ = lean_ctor_get(v_x_543_, 0);
v_vs_548_ = lean_ctor_get(v_x_543_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_572_ == 0)
{
v___x_550_ = v_x_543_;
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_vs_548_);
lean_inc(v_ks_547_);
lean_dec(v_x_543_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v_ks_547_);
v___x_553_ = lean_nat_dec_lt(v_x_544_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
lean_dec(v_x_544_);
v___x_554_ = lean_array_push(v_ks_547_, v_x_545_);
v___x_555_ = lean_array_push(v_vs_548_, v_x_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_555_);
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_557_ = v___x_550_;
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
else
{
lean_object* v_k_x27_559_; uint8_t v___x_560_; 
v_k_x27_559_ = lean_array_fget_borrowed(v_ks_547_, v_x_544_);
v___x_560_ = l_Lean_instBEqMVarId_beq(v_x_545_, v_k_x27_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; 
if (v_isShared_551_ == 0)
{
v___x_562_ = v___x_550_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_ks_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_vs_548_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_x_544_, v___x_563_);
lean_dec(v_x_544_);
v_x_543_ = v___x_562_;
v_x_544_ = v___x_564_;
goto _start;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_array_fset(v_ks_547_, v_x_544_, v_x_545_);
v___x_568_ = lean_array_fset(v_vs_548_, v_x_544_, v_x_546_);
lean_dec(v_x_544_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_568_);
lean_ctor_set(v___x_550_, 0, v___x_567_);
v___x_570_ = v___x_550_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* v_n_573_, lean_object* v_k_574_, lean_object* v_v_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_573_, v___x_576_, v_k_574_, v_v_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_578_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_579_, size_t v_x_580_, size_t v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_es_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v_j_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_es_584_ = lean_ctor_get(v_x_579_, 0);
v___x_585_ = ((size_t)31ULL);
v___x_586_ = lean_usize_land(v_x_580_, v___x_585_);
v_j_587_ = lean_usize_to_nat(v___x_586_);
v___x_588_ = lean_array_get_size(v_es_584_);
v___x_589_ = lean_nat_dec_lt(v_j_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v_j_587_);
lean_dec(v_x_583_);
lean_dec(v_x_582_);
return v_x_579_;
}
else
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_628_; 
lean_inc_ref(v_es_584_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_x_579_, 0);
lean_dec(v_unused_629_);
v___x_591_ = v_x_579_;
v_isShared_592_ = v_isSharedCheck_628_;
goto v_resetjp_590_;
}
else
{
lean_dec(v_x_579_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_628_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_v_593_; lean_object* v___x_594_; lean_object* v_xs_x27_595_; lean_object* v___y_597_; 
v_v_593_ = lean_array_fget(v_es_584_, v_j_587_);
v___x_594_ = lean_box(0);
v_xs_x27_595_ = lean_array_fset(v_es_584_, v_j_587_, v___x_594_);
switch(lean_obj_tag(v_v_593_))
{
case 0:
{
lean_object* v_key_602_; lean_object* v_val_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_613_; 
v_key_602_ = lean_ctor_get(v_v_593_, 0);
v_val_603_ = lean_ctor_get(v_v_593_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_v_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_605_ = v_v_593_;
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_val_603_);
lean_inc(v_key_602_);
lean_dec(v_v_593_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_613_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_instBEqMVarId_beq(v_x_582_, v_key_602_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_del_object(v___x_605_);
v___x_608_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_602_, v_val_603_, v_x_582_, v_x_583_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___y_597_ = v___x_609_;
goto v___jp_596_;
}
else
{
lean_object* v___x_611_; 
lean_dec(v_val_603_);
lean_dec(v_key_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v_x_583_);
lean_ctor_set(v___x_605_, 0, v_x_582_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_x_582_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_x_583_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v___y_597_ = v___x_611_;
goto v___jp_596_;
}
}
}
}
case 1:
{
lean_object* v_node_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_626_; 
v_node_614_ = lean_ctor_get(v_v_593_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_v_593_);
if (v_isSharedCheck_626_ == 0)
{
v___x_616_ = v_v_593_;
v_isShared_617_ = v_isSharedCheck_626_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_node_614_);
lean_dec(v_v_593_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_626_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_618_ = ((size_t)5ULL);
v___x_619_ = lean_usize_shift_right(v_x_580_, v___x_618_);
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_x_581_, v___x_620_);
v___x_622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_614_, v___x_619_, v___x_621_, v_x_582_, v_x_583_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_622_);
v___x_624_ = v___x_616_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v___y_597_ = v___x_624_;
goto v___jp_596_;
}
}
}
default: 
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_x_582_);
lean_ctor_set(v___x_627_, 1, v_x_583_);
v___y_597_ = v___x_627_;
goto v___jp_596_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_array_fset(v_xs_x27_595_, v_j_587_, v___y_597_);
lean_dec(v_j_587_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_600_ = v___x_591_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v_ks_630_; lean_object* v_vs_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_649_; 
v_ks_630_ = lean_ctor_get(v_x_579_, 0);
v_vs_631_ = lean_ctor_get(v_x_579_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_649_ == 0)
{
v___x_633_ = v_x_579_;
v_isShared_634_ = v_isSharedCheck_649_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_vs_631_);
lean_inc(v_ks_630_);
lean_dec(v_x_579_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_649_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_ks_630_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_vs_631_);
v___x_636_ = v_reuseFailAlloc_648_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v_newNode_637_; size_t v___x_638_; uint8_t v___x_639_; 
v_newNode_637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_636_, v_x_582_, v_x_583_);
v___x_638_ = ((size_t)7ULL);
v___x_639_ = lean_usize_dec_le(v___x_638_, v_x_581_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_637_);
v___x_641_ = lean_unsigned_to_nat(4u);
v___x_642_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
lean_dec(v___x_640_);
if (v___x_642_ == 0)
{
lean_object* v_ks_643_; lean_object* v_vs_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_ks_643_ = lean_ctor_get(v_newNode_637_, 0);
lean_inc_ref(v_ks_643_);
v_vs_644_ = lean_ctor_get(v_newNode_637_, 1);
lean_inc_ref(v_vs_644_);
lean_dec_ref(v_newNode_637_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_581_, v_ks_643_, v_vs_644_, v___x_645_, v___x_646_);
lean_dec_ref(v_vs_644_);
lean_dec_ref(v_ks_643_);
return v___x_647_;
}
else
{
return v_newNode_637_;
}
}
else
{
return v_newNode_637_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_579_ = stack[0].m_obj;
size_t v_x_580_ = stack[1].m_num;
size_t v_x_581_ = stack[2].m_num;
lean_object* v_x_582_ = stack[3].m_obj;
lean_object* v_x_583_ = stack[4].m_obj;
lean_object* v_res_650_;
v_res_650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_579_, v_x_580_, v_x_581_, v_x_582_, v_x_583_);
stack->m_obj
 = v_res_650_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_651_, lean_object* v_keys_652_, lean_object* v_vals_653_, lean_object* v_i_654_, lean_object* v_entries_655_){
_start:
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_array_get_size(v_keys_652_);
v___x_657_ = lean_nat_dec_lt(v_i_654_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v_i_654_);
return v_entries_655_;
}
else
{
lean_object* v_k_658_; lean_object* v_v_659_; uint64_t v___x_660_; size_t v_h_661_; size_t v___x_662_; lean_object* v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v_h_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_k_658_ = lean_array_fget_borrowed(v_keys_652_, v_i_654_);
v_v_659_ = lean_array_fget_borrowed(v_vals_653_, v_i_654_);
v___x_660_ = l_Lean_instHashableMVarId_hash(v_k_658_);
v_h_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = ((size_t)5ULL);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_sub(v_depth_651_, v___x_664_);
v___x_666_ = lean_usize_mul(v___x_662_, v___x_665_);
v_h_667_ = lean_usize_shift_right(v_h_661_, v___x_666_);
v___x_668_ = lean_nat_add(v_i_654_, v___x_663_);
lean_dec(v_i_654_);
lean_inc(v_v_659_);
lean_inc(v_k_658_);
v___x_669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_655_, v_h_667_, v_depth_651_, v_k_658_, v_v_659_);
v_i_654_ = v___x_668_;
v_entries_655_ = v___x_669_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_651_ = stack[0].m_num;
lean_object* v_keys_652_ = stack[1].m_obj;
lean_object* v_vals_653_ = stack[2].m_obj;
lean_object* v_i_654_ = stack[3].m_obj;
lean_object* v_entries_655_ = stack[4].m_obj;
lean_object* v_res_671_;
v_res_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_651_, v_keys_652_, v_vals_653_, v_i_654_, v_entries_655_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_i_675_, lean_object* v_entries_676_){
_start:
{
size_t v_depth_boxed_677_; lean_object* v_res_678_; 
v_depth_boxed_677_ = lean_unbox_usize(v_depth_672_);
lean_dec(v_depth_672_);
v_res_678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_677_, v_keys_673_, v_vals_674_, v_i_675_, v_entries_676_);
lean_dec_ref(v_vals_674_);
lean_dec_ref(v_keys_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
size_t v_x_4772__boxed_684_; size_t v_x_4773__boxed_685_; lean_object* v_res_686_; 
v_x_4772__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_x_4773__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_686_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_679_, v_x_4772__boxed_684_, v_x_4773__boxed_685_, v_x_682_, v_x_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint64_t v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_690_ = l_Lean_instHashableMVarId_hash(v_x_688_);
v___x_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_687_, v___x_691_, v___x_692_, v_x_688_, v_x_689_);
return v___x_693_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_694_, lean_object* v_val_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v_mctx_699_; lean_object* v_cache_700_; lean_object* v_zetaDeltaFVarIds_701_; lean_object* v_postponed_702_; lean_object* v_diag_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_733_; 
v___x_698_ = lean_st_ref_take(v___y_696_);
v_mctx_699_ = lean_ctor_get(v___x_698_, 0);
v_cache_700_ = lean_ctor_get(v___x_698_, 1);
v_zetaDeltaFVarIds_701_ = lean_ctor_get(v___x_698_, 2);
v_postponed_702_ = lean_ctor_get(v___x_698_, 3);
v_diag_703_ = lean_ctor_get(v___x_698_, 4);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_733_ == 0)
{
v___x_705_ = v___x_698_;
v_isShared_706_ = v_isSharedCheck_733_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_diag_703_);
lean_inc(v_postponed_702_);
lean_inc(v_zetaDeltaFVarIds_701_);
lean_inc(v_cache_700_);
lean_inc(v_mctx_699_);
lean_dec(v___x_698_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_733_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_depth_707_; lean_object* v_levelAssignDepth_708_; lean_object* v_lmvarCounter_709_; lean_object* v_mvarCounter_710_; lean_object* v_lDecls_711_; lean_object* v_decls_712_; lean_object* v_userNames_713_; lean_object* v_lAssignment_714_; lean_object* v_eAssignment_715_; lean_object* v_dAssignment_716_; lean_object* v_instanceTypedMVars_717_; lean_object* v_synthNormMemo_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_depth_707_ = lean_ctor_get(v_mctx_699_, 0);
v_levelAssignDepth_708_ = lean_ctor_get(v_mctx_699_, 1);
v_lmvarCounter_709_ = lean_ctor_get(v_mctx_699_, 2);
v_mvarCounter_710_ = lean_ctor_get(v_mctx_699_, 3);
v_lDecls_711_ = lean_ctor_get(v_mctx_699_, 4);
v_decls_712_ = lean_ctor_get(v_mctx_699_, 5);
v_userNames_713_ = lean_ctor_get(v_mctx_699_, 6);
v_lAssignment_714_ = lean_ctor_get(v_mctx_699_, 7);
v_eAssignment_715_ = lean_ctor_get(v_mctx_699_, 8);
v_dAssignment_716_ = lean_ctor_get(v_mctx_699_, 9);
v_instanceTypedMVars_717_ = lean_ctor_get(v_mctx_699_, 10);
v_synthNormMemo_718_ = lean_ctor_get(v_mctx_699_, 11);
v_isSharedCheck_732_ = !lean_is_exclusive(v_mctx_699_);
if (v_isSharedCheck_732_ == 0)
{
v___x_720_ = v_mctx_699_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_synthNormMemo_718_);
lean_inc(v_instanceTypedMVars_717_);
lean_inc(v_dAssignment_716_);
lean_inc(v_eAssignment_715_);
lean_inc(v_lAssignment_714_);
lean_inc(v_userNames_713_);
lean_inc(v_decls_712_);
lean_inc(v_lDecls_711_);
lean_inc(v_mvarCounter_710_);
lean_inc(v_lmvarCounter_709_);
lean_inc(v_levelAssignDepth_708_);
lean_inc(v_depth_707_);
lean_dec(v_mctx_699_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_722_ = lean_box(0);
v___x_723_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_715_, v_mvarId_694_, v_val_695_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 8, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_depth_707_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_levelAssignDepth_708_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_lmvarCounter_709_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_mvarCounter_710_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_lDecls_711_);
lean_ctor_set(v_reuseFailAlloc_731_, 5, v_decls_712_);
lean_ctor_set(v_reuseFailAlloc_731_, 6, v_userNames_713_);
lean_ctor_set(v_reuseFailAlloc_731_, 7, v_lAssignment_714_);
lean_ctor_set(v_reuseFailAlloc_731_, 8, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 9, v_dAssignment_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 10, v_instanceTypedMVars_717_);
lean_ctor_set(v_reuseFailAlloc_731_, 11, v_synthNormMemo_718_);
v___x_725_ = v_reuseFailAlloc_731_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_725_);
v___x_727_ = v___x_705_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_cache_700_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_zetaDeltaFVarIds_701_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_postponed_702_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_diag_703_);
v___x_727_ = v_reuseFailAlloc_730_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_st_ref_put(v___y_696_, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_722_);
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_694_ = stack[0].m_obj;
lean_object* v_val_695_ = stack[1].m_obj;
lean_object* v___y_696_ = stack[2].m_obj;
lean_object* v_res_734_;
v_res_734_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_694_, v_val_695_, v___y_696_);
stack->m_obj
 = v_res_734_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_735_, lean_object* v_val_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_735_, v_val_736_, v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_743_, lean_object* v___x_744_, lean_object* v_args_745_, uint8_t v_transparency_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
lean_inc(v___x_744_);
lean_inc(v_mvarId_743_);
v___x_752_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_743_, v___x_744_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; 
lean_dec_ref_known(v___x_752_, 1);
lean_inc(v_mvarId_743_);
v___x_753_ = l_Lean_MVarId_getTag(v_mvarId_743_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
lean_inc(v_mvarId_743_);
v___x_755_ = l_Lean_MVarId_getType(v_mvarId_743_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_871_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_756_, v___y_748_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_871_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_871_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_871_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_745_, v_transparency_746_, v_a_758_, v___x_762_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___x_839_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_n(v_a_764_, 2);
lean_dec_ref_known(v___x_763_, 1);
v___x_839_ = l_Lean_Meta_isTypeCorrect(v_a_764_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; uint8_t v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_unbox(v_a_840_);
lean_dec(v_a_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_764_);
v___x_843_ = l_Lean_indentExpr(v_a_764_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_inc(v_mvarId_743_);
v___x_846_ = l_Lean_Meta_throwTacticEx___redArg(v___x_744_, v_mvarId_743_, v___x_845_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_dec_ref_known(v___x_846_, 1);
v___y_790_ = v___y_747_;
v___y_791_ = v___y_748_;
v___y_792_ = v___y_749_;
v___y_793_ = v___y_750_;
goto v___jp_789_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_764_);
lean_del_object(v___x_760_);
lean_dec(v_a_754_);
lean_dec_ref(v_args_745_);
lean_dec(v_mvarId_743_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_dec(v___x_744_);
v___y_790_ = v___y_747_;
v___y_791_ = v___y_748_;
v___y_792_ = v___y_749_;
v___y_793_ = v___y_750_;
goto v___jp_789_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_764_);
lean_del_object(v___x_760_);
lean_dec(v_a_754_);
lean_dec_ref(v_args_745_);
lean_dec(v___x_744_);
lean_dec(v_mvarId_743_);
v_a_855_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_839_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_839_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
v___jp_765_:
{
uint8_t v___x_773_; lean_object* v___x_774_; 
v___x_773_ = 1;
v___x_774_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_764_, v_a_754_, v___y_770_, v___y_769_, v___y_771_, v___y_767_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_n(v_a_775_, 2);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = l_Lean_mkAppN(v_a_775_, v___y_768_);
lean_dec_ref(v___y_768_);
v___x_777_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_743_, v___x_776_, v___y_769_);
lean_dec_ref(v___x_777_);
v___x_778_ = l_Lean_Expr_mvarId_x21(v_a_775_);
lean_dec(v_a_775_);
v___x_779_ = lean_box(0);
v___x_780_ = l_Lean_Meta_introNCore(v___x_778_, v___y_766_, v___x_779_, v___y_772_, v___x_773_, v___y_770_, v___y_769_, v___y_771_, v___y_767_);
return v___x_780_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___y_768_);
lean_dec(v___y_766_);
lean_dec(v_mvarId_743_);
v_a_781_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_774_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_774_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
v___jp_789_:
{
size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_sz_794_ = lean_array_size(v_args_745_);
v___x_795_ = ((size_t)0ULL);
lean_inc_ref(v_args_745_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_794_, v___x_795_, v_args_745_);
v___x_797_ = lean_array_get_size(v_args_745_);
v___x_798_ = lean_nat_dec_lt(v___x_762_, v___x_797_);
if (v___x_798_ == 0)
{
lean_del_object(v___x_760_);
lean_dec_ref(v_args_745_);
v___y_766_ = v___x_797_;
v___y_767_ = v___y_793_;
v___y_768_ = v___x_796_;
v___y_769_ = v___y_791_;
v___y_770_ = v___y_790_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_798_;
goto v___jp_765_;
}
else
{
if (v___x_798_ == 0)
{
lean_del_object(v___x_760_);
lean_dec_ref(v_args_745_);
v___y_766_ = v___x_797_;
v___y_767_ = v___y_793_;
v___y_768_ = v___x_796_;
v___y_769_ = v___y_791_;
v___y_770_ = v___y_790_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_798_;
goto v___jp_765_;
}
else
{
size_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_usize_of_nat(v___x_797_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_745_, v___x_795_, v___x_799_);
if (v___x_800_ == 0)
{
lean_del_object(v___x_760_);
lean_dec_ref(v_args_745_);
v___y_766_ = v___x_797_;
v___y_767_ = v___y_793_;
v___y_768_ = v___x_796_;
v___y_769_ = v___y_791_;
v___y_770_ = v___y_790_;
v___y_771_ = v___y_792_;
v___y_772_ = v___x_800_;
goto v___jp_765_;
}
else
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_806_; 
v___x_801_ = 0;
v___x_802_ = lean_box(v___x_801_);
v___x_803_ = lean_box(v___x_800_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_804_, 0, v_args_745_);
lean_closure_set(v___f_804_, 1, v___x_762_);
lean_closure_set(v___f_804_, 2, v___x_802_);
lean_closure_set(v___f_804_, 3, v___x_803_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 1);
lean_ctor_set(v___x_760_, 0, v___x_797_);
v___x_806_ = v___x_760_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_797_);
v___x_806_ = v_reuseFailAlloc_838_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_764_, v___x_806_, v___f_804_, v___x_801_, v___x_801_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_811_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_fst_809_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_fst_809_);
v_snd_810_ = lean_ctor_get(v_a_808_, 1);
lean_inc(v_snd_810_);
lean_dec(v_a_808_);
v___x_811_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_810_, v_a_754_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_n(v_a_812_, 2);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = l_Lean_mkAppN(v_a_812_, v___x_796_);
lean_dec_ref(v___x_796_);
lean_inc(v_fst_809_);
v___x_814_ = lean_array_mk(v_fst_809_);
v___x_815_ = l_Lean_mkAppN(v___x_813_, v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_743_, v___x_815_, v___y_791_);
lean_dec_ref(v___x_816_);
v___x_817_ = l_Lean_Expr_mvarId_x21(v_a_812_);
lean_dec(v_a_812_);
v___x_818_ = l_List_lengthTR___redArg(v_fst_809_);
lean_dec(v_fst_809_);
v___x_819_ = lean_nat_add(v___x_797_, v___x_818_);
lean_dec(v___x_818_);
v___x_820_ = lean_box(0);
v___x_821_ = l_Lean_Meta_introNCore(v___x_817_, v___x_819_, v___x_820_, v___x_801_, v___x_800_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_fst_809_);
lean_dec_ref(v___x_796_);
lean_dec(v_mvarId_743_);
v_a_822_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_811_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_811_);
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
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___x_796_);
lean_dec(v_a_754_);
lean_dec(v_mvarId_743_);
v_a_830_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_807_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_807_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
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
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_del_object(v___x_760_);
lean_dec(v_a_754_);
lean_dec_ref(v_args_745_);
lean_dec(v___x_744_);
lean_dec(v_mvarId_743_);
v_a_863_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_763_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_763_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_754_);
lean_dec_ref(v_args_745_);
lean_dec(v___x_744_);
lean_dec(v_mvarId_743_);
v_a_872_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_755_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_755_);
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
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_args_745_);
lean_dec(v___x_744_);
lean_dec(v_mvarId_743_);
v_a_880_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_753_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_753_);
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
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_args_745_);
lean_dec(v___x_744_);
lean_dec(v_mvarId_743_);
v_a_888_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_752_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_752_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_743_ = stack[0].m_obj;
lean_object* v___x_744_ = stack[1].m_obj;
lean_object* v_args_745_ = stack[2].m_obj;
uint8_t v_transparency_746_ = stack[3].m_num;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v_res_896_;
v_res_896_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_743_, v___x_744_, v_args_745_, v_transparency_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_896_;
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
lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_911_, lean_object* v_args_912_, uint8_t v_transparency_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_911_ = stack[0].m_obj;
lean_object* v_args_912_ = stack[1].m_obj;
uint8_t v_transparency_913_ = stack[2].m_num;
lean_object* v_a_914_ = stack[3].m_obj;
lean_object* v_a_915_ = stack[4].m_obj;
lean_object* v_a_916_ = stack[5].m_obj;
lean_object* v_a_917_ = stack[6].m_obj;
lean_object* v_res_923_;
v_res_923_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_911_, v_args_912_, v_transparency_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_924_, lean_object* v_args_925_, lean_object* v_transparency_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_transparency_boxed_932_; lean_object* v_res_933_; 
v_transparency_boxed_932_ = lean_unbox(v_transparency_926_);
v_res_933_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_924_, v_args_925_, v_transparency_boxed_932_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
return v_res_933_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_934_, lean_object* v_val_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_934_, v_val_935_, v___y_937_);
return v___x_941_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_934_ = stack[0].m_obj;
lean_object* v_val_935_ = stack[1].m_obj;
lean_object* v___y_936_ = stack[2].m_obj;
lean_object* v___y_937_ = stack[3].m_obj;
lean_object* v___y_938_ = stack[4].m_obj;
lean_object* v___y_939_ = stack[5].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_934_, v_val_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_943_, lean_object* v_val_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_943_, v_val_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, size_t v_x_958_, size_t v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_957_, v_x_958_, v_x_959_, v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_957_ = stack[1].m_obj;
size_t v_x_958_ = stack[2].m_num;
size_t v_x_959_ = stack[3].m_num;
lean_object* v_x_960_ = stack[4].m_obj;
lean_object* v_x_961_ = stack[5].m_obj;
lean_object* v_res_963_;
v_res_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_box(0), v_x_957_, v_x_958_, v_x_959_, v_x_960_, v_x_961_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
size_t v_x_5643__boxed_970_; size_t v_x_5644__boxed_971_; lean_object* v_res_972_; 
v_x_5643__boxed_970_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_x_5644__boxed_971_ = lean_unbox_usize(v_x_967_);
lean_dec(v_x_967_);
v_res_972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_964_, v_x_965_, v_x_5643__boxed_970_, v_x_5644__boxed_971_, v_x_968_, v_x_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_973_, lean_object* v_n_974_, lean_object* v_k_975_, lean_object* v_v_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_974_, v_k_975_, v_v_976_);
return v___x_977_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_978_, size_t v_depth_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_entries_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_979_, v_keys_980_, v_vals_981_, v_i_983_, v_entries_984_);
return v___x_985_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_depth_979_ = stack[1].m_num;
lean_object* v_keys_980_ = stack[2].m_obj;
lean_object* v_vals_981_ = stack[3].m_obj;
lean_object* v_i_983_ = stack[5].m_obj;
lean_object* v_entries_984_ = stack[6].m_obj;
lean_object* v_res_986_;
v_res_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_box(0), v_depth_979_, v_keys_980_, v_vals_981_, lean_box(0), v_i_983_, v_entries_984_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_987_, lean_object* v_depth_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_entries_993_){
_start:
{
size_t v_depth_boxed_994_; lean_object* v_res_995_; 
v_depth_boxed_994_ = lean_unbox_usize(v_depth_988_);
lean_dec(v_depth_988_);
v_res_995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_987_, v_depth_boxed_994_, v_keys_989_, v_vals_990_, v_heq_991_, v_i_992_, v_entries_993_);
lean_dec_ref(v_vals_990_);
lean_dec_ref(v_keys_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_997_, v_x_998_, v_x_999_, v_x_1000_);
return v___x_1001_;
}
}
lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_1002_, lean_object* v_args_1003_, uint8_t v_transparency_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1002_, v_args_1003_, v_transparency_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT void l_Lean_MVarId_generalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1002_ = stack[0].m_obj;
lean_object* v_args_1003_ = stack[1].m_obj;
uint8_t v_transparency_1004_ = stack[2].m_num;
lean_object* v_a_1005_ = stack[3].m_obj;
lean_object* v_a_1006_ = stack[4].m_obj;
lean_object* v_a_1007_ = stack[5].m_obj;
lean_object* v_a_1008_ = stack[6].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_MVarId_generalize(v_mvarId_1002_, v_args_1003_, v_transparency_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_1012_, lean_object* v_args_1013_, lean_object* v_transparency_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_transparency_boxed_1020_; lean_object* v_res_1021_; 
v_transparency_boxed_1020_ = lean_unbox(v_transparency_1014_);
v_res_1021_ = l_Lean_MVarId_generalize(v_mvarId_1012_, v_args_1013_, v_transparency_boxed_1020_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1021_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1022_, size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_b_1025_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_lt(v_i_1024_, v_sz_1023_);
if (v___x_1026_ == 0)
{
return v_b_1025_;
}
else
{
lean_object* v_snd_1027_; lean_object* v_fst_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1061_; 
v_snd_1027_ = lean_ctor_get(v_b_1025_, 1);
v_fst_1028_ = lean_ctor_get(v_b_1025_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_b_1025_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1030_ = v_b_1025_;
v_isShared_1031_ = v_isSharedCheck_1061_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1027_);
lean_inc(v_fst_1028_);
lean_dec(v_b_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1061_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_array_1032_; lean_object* v_start_1033_; lean_object* v_stop_1034_; uint8_t v___x_1035_; 
v_array_1032_ = lean_ctor_get(v_snd_1027_, 0);
v_start_1033_ = lean_ctor_get(v_snd_1027_, 1);
v_stop_1034_ = lean_ctor_get(v_snd_1027_, 2);
v___x_1035_ = lean_nat_dec_lt(v_start_1033_, v_stop_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1037_; 
if (v_isShared_1031_ == 0)
{
v___x_1037_ = v___x_1030_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fst_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_snd_1027_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1057_; 
lean_inc(v_stop_1034_);
lean_inc(v_start_1033_);
lean_inc_ref(v_array_1032_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_snd_1027_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; 
v_unused_1058_ = lean_ctor_get(v_snd_1027_, 2);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_snd_1027_, 1);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_snd_1027_, 0);
lean_dec(v_unused_1060_);
v___x_1040_ = v_snd_1027_;
v_isShared_1041_ = v_isSharedCheck_1057_;
goto v_resetjp_1039_;
}
else
{
lean_dec(v_snd_1027_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1057_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v_a_1042_ = lean_array_uget_borrowed(v_as_1022_, v_i_1024_);
v___x_1043_ = lean_array_fget(v_array_1032_, v_start_1033_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_add(v_start_1033_, v___x_1044_);
lean_dec(v_start_1033_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1045_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_array_1032_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_stop_1034_);
v___x_1047_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = l_Lean_mkFVar(v___x_1043_);
lean_inc(v_a_1042_);
v___x_1049_ = l_Lean_Meta_FVarSubst_insert(v_fst_1028_, v_a_1042_, v___x_1048_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1047_);
lean_ctor_set(v___x_1030_, 0, v___x_1049_);
v___x_1051_ = v___x_1030_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1047_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
size_t v___x_1052_; size_t v___x_1053_; 
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1024_, v___x_1052_);
v_i_1024_ = v___x_1053_;
v_b_1025_ = v___x_1051_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1022_ = stack[0].m_obj;
size_t v_sz_1023_ = stack[1].m_num;
size_t v_i_1024_ = stack[2].m_num;
lean_object* v_b_1025_ = stack[3].m_obj;
lean_object* v_res_1062_;
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1022_, v_sz_1023_, v_i_1024_, v_b_1025_);
stack->m_obj
 = v_res_1062_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1063_, lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_b_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1063_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1066_);
lean_dec_ref(v_as_1063_);
return v_res_1069_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_bs_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_bs_1072_);
return v___x_1076_;
}
else
{
lean_object* v_v_1077_; lean_object* v_expr_1078_; lean_object* v_xName_x3f_1079_; lean_object* v_hName_x3f_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1103_; 
v_v_1077_ = lean_array_uget(v_bs_1072_, v_i_1071_);
v_expr_1078_ = lean_ctor_get(v_v_1077_, 0);
v_xName_x3f_1079_ = lean_ctor_get(v_v_1077_, 1);
v_hName_x3f_1080_ = lean_ctor_get(v_v_1077_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_v_1077_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1082_ = v_v_1077_;
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_hName_x3f_1080_);
lean_inc(v_xName_x3f_1079_);
lean_inc(v_expr_1078_);
lean_dec(v_v_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v_bs_x27_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(0u);
v_bs_x27_1085_ = lean_array_uset(v_bs_1072_, v_i_1071_, v___x_1084_);
v___x_1086_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1078_, v___y_1073_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_a_1087_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_xName_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_hName_x3f_1080_);
v___x_1089_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_add(v_i_1071_, v___x_1090_);
v___x_1092_ = lean_array_uset(v_bs_x27_1085_, v_i_1071_, v___x_1089_);
v_i_1071_ = v___x_1091_;
v_bs_1072_ = v___x_1092_;
goto _start;
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_bs_x27_1085_);
lean_del_object(v___x_1082_);
lean_dec(v_hName_x3f_1080_);
lean_dec(v_xName_x3f_1079_);
v_a_1095_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1086_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1086_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1070_ = stack[0].m_num;
size_t v_i_1071_ = stack[1].m_num;
lean_object* v_bs_1072_ = stack[2].m_obj;
lean_object* v___y_1073_ = stack[3].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1070_, v_i_1071_, v_bs_1072_, v___y_1073_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_bs_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1110_, v_i_boxed_1111_, v_bs_1107_, v___y_1108_);
lean_dec(v___y_1108_);
return v_res_1112_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1113_, lean_object* v_a_1114_, lean_object* v_as_1115_, size_t v_i_1116_, size_t v_stop_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_usize_dec_eq(v_i_1116_, v_stop_1117_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v_expr_1125_; lean_object* v___x_1126_; uint8_t v_transparency_1127_; uint8_t v___x_1128_; lean_object* v___y_1130_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1124_ = lean_array_uget_borrowed(v_as_1115_, v_i_1116_);
v_expr_1125_ = lean_ctor_get(v___x_1124_, 0);
v___x_1126_ = l_Lean_Meta_Context_config(v___y_1118_);
v_transparency_1127_ = lean_ctor_get_uint8(v___x_1126_, 9);
lean_dec_ref(v___x_1126_);
v___x_1128_ = 1;
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1127_, v_transparency_1113_);
if (v___x_1153_ == 0)
{
lean_object* v_keyedConfig_1154_; uint8_t v_trackZetaDelta_1155_; lean_object* v_zetaDeltaSet_1156_; lean_object* v_lctx_1157_; lean_object* v_localInstances_1158_; lean_object* v_defEqCtx_x3f_1159_; lean_object* v_synthPendingDepth_1160_; lean_object* v_customCanUnfoldPredicate_x3f_1161_; uint8_t v_univApprox_1162_; uint8_t v_inTypeClassResolution_1163_; uint8_t v_cacheInferType_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_keyedConfig_1154_ = lean_ctor_get(v___y_1118_, 0);
v_trackZetaDelta_1155_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*7);
v_zetaDeltaSet_1156_ = lean_ctor_get(v___y_1118_, 1);
v_lctx_1157_ = lean_ctor_get(v___y_1118_, 2);
v_localInstances_1158_ = lean_ctor_get(v___y_1118_, 3);
v_defEqCtx_x3f_1159_ = lean_ctor_get(v___y_1118_, 4);
v_synthPendingDepth_1160_ = lean_ctor_get(v___y_1118_, 5);
v_customCanUnfoldPredicate_x3f_1161_ = lean_ctor_get(v___y_1118_, 6);
v_univApprox_1162_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1163_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*7 + 2);
v_cacheInferType_1164_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1154_);
v___x_1165_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_1113_, v_keyedConfig_1154_);
lean_inc(v_customCanUnfoldPredicate_x3f_1161_);
lean_inc(v_synthPendingDepth_1160_);
lean_inc(v_defEqCtx_x3f_1159_);
lean_inc_ref(v_localInstances_1158_);
lean_inc_ref(v_lctx_1157_);
lean_inc(v_zetaDeltaSet_1156_);
v___x_1166_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_zetaDeltaSet_1156_);
lean_ctor_set(v___x_1166_, 2, v_lctx_1157_);
lean_ctor_set(v___x_1166_, 3, v_localInstances_1158_);
lean_ctor_set(v___x_1166_, 4, v_defEqCtx_x3f_1159_);
lean_ctor_set(v___x_1166_, 5, v_synthPendingDepth_1160_);
lean_ctor_set(v___x_1166_, 6, v_customCanUnfoldPredicate_x3f_1161_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7, v_trackZetaDelta_1155_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 1, v_univApprox_1162_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1163_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 3, v_cacheInferType_1164_);
lean_inc_ref(v_expr_1125_);
lean_inc_ref(v_a_1114_);
v___x_1167_ = l_Lean_Meta_kabstract(v_a_1114_, v_expr_1125_, v___x_1152_, v___x_1166_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec_ref_known(v___x_1166_, 7);
v___y_1130_ = v___x_1167_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1168_; 
lean_inc_ref(v_expr_1125_);
lean_inc_ref(v_a_1114_);
v___x_1168_ = l_Lean_Meta_kabstract(v_a_1114_, v_expr_1125_, v___x_1152_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
v___y_1130_ = v___x_1168_;
goto v___jp_1129_;
}
v___jp_1129_:
{
if (lean_obj_tag(v___y_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1143_; 
v_a_1131_ = lean_ctor_get(v___y_1130_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___y_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1133_ = v___y_1130_;
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___y_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_Expr_hasLooseBVars(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1135_ == 0)
{
size_t v___x_1136_; size_t v___x_1137_; 
lean_del_object(v___x_1133_);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1116_, v___x_1136_);
v_i_1116_ = v___x_1137_;
goto _start;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec_ref(v_a_1114_);
v___x_1139_ = lean_box(v___x_1128_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1139_);
v___x_1141_ = v___x_1133_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_a_1114_);
v_a_1144_ = lean_ctor_get(v___y_1130_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___y_1130_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___y_1130_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___y_1130_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
else
{
uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec_ref(v_a_1114_);
v___x_1169_ = 0;
v___x_1170_ = lean_box(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_transparency_1113_ = stack[0].m_num;
lean_object* v_a_1114_ = stack[1].m_obj;
lean_object* v_as_1115_ = stack[2].m_obj;
size_t v_i_1116_ = stack[3].m_num;
size_t v_stop_1117_ = stack[4].m_num;
lean_object* v___y_1118_ = stack[5].m_obj;
lean_object* v___y_1119_ = stack[6].m_obj;
lean_object* v___y_1120_ = stack[7].m_obj;
lean_object* v___y_1121_ = stack[8].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1113_, v_a_1114_, v_as_1115_, v_i_1116_, v_stop_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1173_, lean_object* v_a_1174_, lean_object* v_as_1175_, lean_object* v_i_1176_, lean_object* v_stop_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_transparency_boxed_1183_; size_t v_i_boxed_1184_; size_t v_stop_boxed_1185_; lean_object* v_res_1186_; 
v_transparency_boxed_1183_ = lean_unbox(v_transparency_1173_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_stop_boxed_1185_ = lean_unbox_usize(v_stop_1177_);
lean_dec(v_stop_1177_);
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1183_, v_a_1174_, v_as_1175_, v_i_boxed_1184_, v_stop_boxed_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_as_1175_);
return v_res_1186_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1187_, uint8_t v_transparency_1188_, lean_object* v_as_1189_, size_t v_i_1190_, size_t v_stop_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_a_1199_; uint8_t v___x_1203_; 
v___x_1203_ = lean_usize_dec_eq(v_i_1190_, v_stop_1191_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_array_uget_borrowed(v_as_1189_, v_i_1190_);
lean_inc(v___x_1204_);
v___x_1205_ = l_Lean_FVarId_getType___redArg(v___x_1204_, v___y_1193_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1206_, v___y_1194_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_array_get_size(v_a_1187_);
v___x_1211_ = lean_nat_dec_lt(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_a_1208_);
v_a_1199_ = v_b_1192_;
goto v___jp_1198_;
}
else
{
if (v___x_1211_ == 0)
{
lean_dec(v_a_1208_);
v_a_1199_ = v_b_1192_;
goto v___jp_1198_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1210_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1188_, v_a_1208_, v_a_1187_, v___x_1212_, v___x_1213_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; uint8_t v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
if (v___x_1216_ == 0)
{
v_a_1199_ = v_b_1192_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1217_; 
lean_inc(v___x_1204_);
v___x_1217_ = lean_array_push(v_b_1192_, v___x_1204_);
v_a_1199_ = v___x_1217_;
goto v___jp_1198_;
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_b_1192_);
v_a_1218_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1214_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_b_1192_);
v_a_1226_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1207_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1207_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_b_1192_);
v_a_1234_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1205_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1205_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_b_1192_);
return v___x_1242_;
}
v___jp_1198_:
{
size_t v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_i_1190_, v___x_1200_);
v_i_1190_ = v___x_1201_;
v_b_1192_ = v_a_1199_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1187_ = stack[0].m_obj;
uint8_t v_transparency_1188_ = stack[1].m_num;
lean_object* v_as_1189_ = stack[2].m_obj;
size_t v_i_1190_ = stack[3].m_num;
size_t v_stop_1191_ = stack[4].m_num;
lean_object* v_b_1192_ = stack[5].m_obj;
lean_object* v___y_1193_ = stack[6].m_obj;
lean_object* v___y_1194_ = stack[7].m_obj;
lean_object* v___y_1195_ = stack[8].m_obj;
lean_object* v___y_1196_ = stack[9].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1187_, v_transparency_1188_, v_as_1189_, v_i_1190_, v_stop_1191_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1244_, lean_object* v_transparency_1245_, lean_object* v_as_1246_, lean_object* v_i_1247_, lean_object* v_stop_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v_transparency_boxed_1255_; size_t v_i_boxed_1256_; size_t v_stop_boxed_1257_; lean_object* v_res_1258_; 
v_transparency_boxed_1255_ = lean_unbox(v_transparency_1245_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1247_);
lean_dec(v_i_1247_);
v_stop_boxed_1257_ = lean_unbox_usize(v_stop_1248_);
lean_dec(v_stop_1248_);
v_res_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1244_, v_transparency_boxed_1255_, v_as_1246_, v_i_boxed_1256_, v_stop_boxed_1257_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_as_1246_);
lean_dec_ref(v_a_1244_);
return v_res_1258_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1259_, lean_object* v_a_1260_, lean_object* v_as_1261_, size_t v_i_1262_, size_t v_stop_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_a_1271_; uint8_t v___x_1275_; 
v___x_1275_ = lean_usize_dec_eq(v_i_1262_, v_stop_1263_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_array_uget_borrowed(v_as_1261_, v_i_1262_);
lean_inc(v___x_1276_);
v___x_1277_ = l_Lean_FVarId_getType___redArg(v___x_1276_, v___y_1265_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1278_, v___y_1266_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_array_get_size(v_a_1260_);
v___x_1283_ = lean_nat_dec_lt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v_a_1280_);
v_a_1271_ = v_b_1264_;
goto v___jp_1270_;
}
else
{
if (v___x_1283_ == 0)
{
lean_dec(v_a_1280_);
v_a_1271_ = v_b_1264_;
goto v___jp_1270_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1282_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1259_, v_a_1280_, v_a_1260_, v___x_1284_, v___x_1285_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
v_a_1271_ = v_b_1264_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1289_; 
lean_inc(v___x_1276_);
v___x_1289_ = lean_array_push(v_b_1264_, v___x_1276_);
v_a_1271_ = v___x_1289_;
goto v___jp_1270_;
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_b_1264_);
v_a_1290_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1286_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1286_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_b_1264_);
v_a_1298_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1279_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1279_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_b_1264_);
v_a_1306_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1277_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1277_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_b_1264_);
return v___x_1314_;
}
v___jp_1270_:
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_i_1262_, v___x_1272_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1260_, v_transparency_1259_, v_as_1261_, v___x_1273_, v_stop_1263_, v_a_1271_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1274_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_transparency_1259_ = stack[0].m_num;
lean_object* v_a_1260_ = stack[1].m_obj;
lean_object* v_as_1261_ = stack[2].m_obj;
size_t v_i_1262_ = stack[3].m_num;
size_t v_stop_1263_ = stack[4].m_num;
lean_object* v_b_1264_ = stack[5].m_obj;
lean_object* v___y_1265_ = stack[6].m_obj;
lean_object* v___y_1266_ = stack[7].m_obj;
lean_object* v___y_1267_ = stack[8].m_obj;
lean_object* v___y_1268_ = stack[9].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1259_, v_a_1260_, v_as_1261_, v_i_1262_, v_stop_1263_, v_b_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1316_, lean_object* v_a_1317_, lean_object* v_as_1318_, lean_object* v_i_1319_, lean_object* v_stop_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_transparency_boxed_1327_; size_t v_i_boxed_1328_; size_t v_stop_boxed_1329_; lean_object* v_res_1330_; 
v_transparency_boxed_1327_ = lean_unbox(v_transparency_1316_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_stop_boxed_1329_ = lean_unbox_usize(v_stop_1320_);
lean_dec(v_stop_1320_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1327_, v_a_1317_, v_as_1318_, v_i_boxed_1328_, v_stop_boxed_1329_, v_b_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v_as_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1330_;
}
}
lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1333_, lean_object* v_args_1334_, lean_object* v_hyps_1335_, lean_object* v_fvarSubst_1336_, uint8_t v_transparency_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_array_get_size(v_hyps_1335_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_nat_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = 1;
v_sz_1347_ = lean_array_size(v_args_1334_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1347_, v___x_1348_, v_args_1334_, v_a_1339_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_a_1352_; lean_object* v___y_1426_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1436_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1437_ = lean_nat_dec_lt(v___x_1344_, v___x_1343_);
if (v___x_1437_ == 0)
{
v_a_1352_ = v___x_1436_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_le(v___x_1343_, v___x_1343_);
if (v___x_1438_ == 0)
{
if (v___x_1437_ == 0)
{
v_a_1352_ = v___x_1436_;
goto v___jp_1351_;
}
else
{
size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_usize_of_nat(v___x_1343_);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1337_, v_a_1350_, v_hyps_1335_, v___x_1348_, v___x_1439_, v___x_1436_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
v___y_1426_ = v___x_1440_;
goto v___jp_1425_;
}
}
else
{
size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_usize_of_nat(v___x_1343_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1337_, v_a_1350_, v_hyps_1335_, v___x_1348_, v___x_1441_, v___x_1436_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
v___y_1426_ = v___x_1442_;
goto v___jp_1425_;
}
}
v___jp_1351_:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_MVarId_revert(v_mvarId_1333_, v_a_1352_, v___x_1346_, v___x_1345_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v_fst_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_fst_1355_);
v_snd_1356_ = lean_ctor_get(v_a_1354_, 1);
lean_inc(v_snd_1356_);
lean_dec(v_a_1354_);
v___x_1357_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1356_, v_a_1350_, v_transparency_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1408_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v_fst_1359_ = lean_ctor_get(v_a_1358_, 0);
v_snd_1360_ = lean_ctor_get(v_a_1358_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1358_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1362_ = v_a_1358_;
v_isShared_1363_ = v_isSharedCheck_1408_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_inc(v_fst_1359_);
lean_dec(v_a_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1408_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_array_get_size(v_fst_1355_);
v___x_1365_ = lean_box(0);
v___x_1366_ = l_Lean_Meta_introNCore(v_snd_1360_, v___x_1364_, v___x_1365_, v___x_1345_, v___x_1346_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1399_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1399_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1399_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1398_; 
v_fst_1371_ = lean_ctor_get(v_a_1367_, 0);
v_snd_1372_ = lean_ctor_get(v_a_1367_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1367_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1374_ = v_a_1367_;
v_isShared_1375_ = v_isSharedCheck_1398_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_a_1367_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1398_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_array_get_size(v_fst_1371_);
v___x_1377_ = l_Array_toSubarray___redArg(v_fst_1371_, v___x_1344_, v___x_1376_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1377_);
lean_ctor_set(v___x_1374_, 0, v_fvarSubst_1336_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_fvarSubst_1336_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v_sz_1380_; lean_object* v___x_1381_; lean_object* v_fst_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1395_; 
v_sz_1380_ = lean_array_size(v_fst_1355_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1355_, v_sz_1380_, v___x_1348_, v___x_1379_);
lean_dec(v_fst_1355_);
v_fst_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v___x_1381_, 1);
lean_dec(v_unused_1396_);
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_fst_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_snd_1372_);
lean_ctor_set(v___x_1384_, 0, v_fst_1359_);
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_fst_1359_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_snd_1372_);
v___x_1387_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1387_);
lean_ctor_set(v___x_1362_, 0, v_fst_1382_);
v___x_1389_ = v___x_1362_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_fst_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1389_);
v___x_1391_ = v___x_1369_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
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
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1362_);
lean_dec(v_fst_1359_);
lean_dec(v_fst_1355_);
lean_dec(v_fvarSubst_1336_);
v_a_1400_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1366_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1366_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_fst_1355_);
lean_dec(v_fvarSubst_1336_);
v_a_1409_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1357_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1357_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_a_1350_);
lean_dec(v_fvarSubst_1336_);
v_a_1417_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1353_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1353_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
v___jp_1425_:
{
if (lean_obj_tag(v___y_1426_) == 0)
{
lean_object* v_a_1427_; 
v_a_1427_ = lean_ctor_get(v___y_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___y_1426_, 1);
v_a_1352_ = v_a_1427_;
goto v___jp_1351_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1350_);
lean_dec(v_fvarSubst_1336_);
lean_dec(v_mvarId_1333_);
v_a_1428_ = lean_ctor_get(v___y_1426_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___y_1426_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___y_1426_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___y_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_fvarSubst_1336_);
lean_dec(v_mvarId_1333_);
v_a_1443_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1349_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1349_);
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
else
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1333_, v_args_1334_, v_transparency_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1460_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_fvarSubst_1336_);
lean_ctor_set(v___x_1456_, 1, v_a_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_fvarSubst_1336_);
v_a_1461_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1451_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_generalizeHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1333_ = stack[0].m_obj;
lean_object* v_args_1334_ = stack[1].m_obj;
lean_object* v_hyps_1335_ = stack[2].m_obj;
lean_object* v_fvarSubst_1336_ = stack[3].m_obj;
uint8_t v_transparency_1337_ = stack[4].m_num;
lean_object* v_a_1338_ = stack[5].m_obj;
lean_object* v_a_1339_ = stack[6].m_obj;
lean_object* v_a_1340_ = stack[7].m_obj;
lean_object* v_a_1341_ = stack[8].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1333_, v_args_1334_, v_hyps_1335_, v_fvarSubst_1336_, v_transparency_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1470_, lean_object* v_args_1471_, lean_object* v_hyps_1472_, lean_object* v_fvarSubst_1473_, lean_object* v_transparency_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
uint8_t v_transparency_boxed_1480_; lean_object* v_res_1481_; 
v_transparency_boxed_1480_ = lean_unbox(v_transparency_1474_);
v_res_1481_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1470_, v_args_1471_, v_hyps_1472_, v_fvarSubst_1473_, v_transparency_boxed_1480_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_hyps_1472_);
return v_res_1481_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1482_, size_t v_i_1483_, lean_object* v_bs_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1482_, v_i_1483_, v_bs_1484_, v___y_1486_);
return v___x_1490_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1482_ = stack[0].m_num;
size_t v_i_1483_ = stack[1].m_num;
lean_object* v_bs_1484_ = stack[2].m_obj;
lean_object* v___y_1485_ = stack[3].m_obj;
lean_object* v___y_1486_ = stack[4].m_obj;
lean_object* v___y_1487_ = stack[5].m_obj;
lean_object* v___y_1488_ = stack[6].m_obj;
lean_object* v_res_1491_;
v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_1482_, v_i_1483_, v_bs_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
stack->m_obj
 = v_res_1491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1492_, lean_object* v_i_1493_, lean_object* v_bs_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
size_t v_sz_boxed_1500_; size_t v_i_boxed_1501_; lean_object* v_res_1502_; 
v_sz_boxed_1500_ = lean_unbox_usize(v_sz_1492_);
lean_dec(v_sz_1492_);
v_i_boxed_1501_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1500_, v_i_boxed_1501_, v_bs_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1502_;
}
}
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
