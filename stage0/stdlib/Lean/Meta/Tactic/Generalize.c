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
v___x_32_ = lean_st_ref_put(v___y_13_, v___x_31_);
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
lean_object* v_a_78_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_i_61_, v___x_100_);
v___x_102_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_58_, v_transparency_59_, v_target_60_, v___x_101_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v___x_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_xName_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
if (lean_obj_tag(v_xName_x3f_72_) == 1)
{
lean_object* v_val_129_; 
v_val_129_ = lean_ctor_get(v_xName_x3f_72_, 0);
lean_inc(v_val_129_);
v_xName_105_ = v_val_129_;
v___y_106_ = v_a_62_;
v___y_107_ = v_a_63_;
v___y_108_ = v_a_64_;
v___y_109_ = v_a_65_;
goto v___jp_104_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
v___x_131_ = l_Lean_Core_mkFreshUserName(v___x_130_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v_xName_105_ = v_a_132_;
v___y_106_ = v_a_62_;
v___y_107_ = v_a_63_;
v___y_108_ = v_a_64_;
v___y_109_ = v_a_65_;
goto v___jp_104_;
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_a_103_);
lean_dec(v_a_78_);
lean_dec(v_a_74_);
v_a_133_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_131_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
v___jp_104_:
{
lean_object* v___x_110_; uint8_t v_transparency_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = l_Lean_Meta_Context_config(v___y_106_);
v_transparency_111_ = lean_ctor_get_uint8(v___x_110_, 9);
lean_dec_ref(v___x_110_);
v___x_112_ = lean_box(0);
v___x_113_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_111_, v_transparency_59_);
if (v___x_113_ == 0)
{
lean_object* v_keyedConfig_114_; uint8_t v_trackZetaDelta_115_; lean_object* v_zetaDeltaSet_116_; lean_object* v_lctx_117_; lean_object* v_localInstances_118_; lean_object* v_defEqCtx_x3f_119_; lean_object* v_synthPendingDepth_120_; lean_object* v_customCanUnfoldPredicate_x3f_121_; uint8_t v_univApprox_122_; uint8_t v_inTypeClassResolution_123_; uint8_t v_cacheInferType_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_keyedConfig_114_ = lean_ctor_get(v___y_106_, 0);
v_trackZetaDelta_115_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*7);
v_zetaDeltaSet_116_ = lean_ctor_get(v___y_106_, 1);
v_lctx_117_ = lean_ctor_get(v___y_106_, 2);
v_localInstances_118_ = lean_ctor_get(v___y_106_, 3);
v_defEqCtx_x3f_119_ = lean_ctor_get(v___y_106_, 4);
v_synthPendingDepth_120_ = lean_ctor_get(v___y_106_, 5);
v_customCanUnfoldPredicate_x3f_121_ = lean_ctor_get(v___y_106_, 6);
v_univApprox_122_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_123_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*7 + 2);
v_cacheInferType_124_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_114_);
v___x_125_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_59_, v_keyedConfig_114_);
lean_inc(v_customCanUnfoldPredicate_x3f_121_);
lean_inc(v_synthPendingDepth_120_);
lean_inc(v_defEqCtx_x3f_119_);
lean_inc_ref(v_localInstances_118_);
lean_inc_ref(v_lctx_117_);
lean_inc(v_zetaDeltaSet_116_);
v___x_126_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_zetaDeltaSet_116_);
lean_ctor_set(v___x_126_, 2, v_lctx_117_);
lean_ctor_set(v___x_126_, 3, v_localInstances_118_);
lean_ctor_set(v___x_126_, 4, v_defEqCtx_x3f_119_);
lean_ctor_set(v___x_126_, 5, v_synthPendingDepth_120_);
lean_ctor_set(v___x_126_, 6, v_customCanUnfoldPredicate_x3f_121_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*7, v_trackZetaDelta_115_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*7 + 1, v_univApprox_122_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*7 + 2, v_inTypeClassResolution_123_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*7 + 3, v_cacheInferType_124_);
v___x_127_ = l_Lean_Meta_kabstract(v_a_103_, v_a_74_, v___x_112_, v___x_126_, v___y_107_, v___y_108_, v___y_109_);
lean_dec_ref_known(v___x_126_, 7);
v___y_80_ = v_xName_105_;
v___y_81_ = v___x_127_;
goto v___jp_79_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_kabstract(v_a_103_, v_a_74_, v___x_112_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
v___y_80_ = v_xName_105_;
v___y_81_ = v___x_128_;
goto v___jp_79_;
}
}
}
else
{
lean_dec(v_a_78_);
lean_dec(v_a_74_);
return v___x_102_;
}
v___jp_79_:
{
if (lean_obj_tag(v___y_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_91_; 
v_a_82_ = lean_ctor_get(v___y_81_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___y_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_84_ = v___y_81_;
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___y_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_86_ = 0;
v___x_87_ = l_Lean_mkForall(v___y_80_, v___x_86_, v_a_78_, v_a_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_87_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v___y_80_);
lean_dec(v_a_78_);
v_a_92_ = lean_ctor_get(v___y_81_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___y_81_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___y_81_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___y_81_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_141_, lean_object* v_transparency_142_, lean_object* v_target_143_, lean_object* v_i_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_transparency_boxed_150_; lean_object* v_res_151_; 
v_transparency_boxed_150_ = lean_unbox(v_transparency_142_);
v_res_151_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_141_, v_transparency_boxed_150_, v_target_143_, v_i_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_i_144_);
lean_dec_ref(v_args_141_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_152_, lean_object* v_xs_153_, lean_object* v_type_154_, lean_object* v_i_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_array_get_size(v_xs_153_);
v___x_162_ = lean_nat_dec_lt(v_i_155_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_i_155_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_type_154_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v_arg_167_; lean_object* v_hName_x3f_168_; 
v___x_166_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_167_ = lean_array_get_borrowed(v___x_166_, v_args_152_, v_i_155_);
v_hName_x3f_168_ = lean_ctor_get(v_arg_167_, 2);
if (lean_obj_tag(v_hName_x3f_168_) == 1)
{
lean_object* v_expr_169_; lean_object* v_val_170_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_expr_169_ = lean_ctor_get(v_arg_167_, 0);
v_val_170_ = lean_ctor_get(v_hName_x3f_168_, 0);
v___x_201_ = lean_array_fget_borrowed(v_xs_153_, v_i_155_);
lean_inc(v_a_159_);
lean_inc_ref(v_a_158_);
lean_inc(v_a_157_);
lean_inc_ref(v_a_156_);
lean_inc(v___x_201_);
v___x_202_ = lean_infer_type(v___x_201_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
lean_inc_ref(v_expr_169_);
v___x_204_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_169_, v_a_157_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_n(v_a_205_, 2);
lean_dec_ref_known(v___x_204_, 1);
lean_inc(v_a_159_);
lean_inc_ref(v_a_158_);
lean_inc(v_a_157_);
lean_inc_ref(v_a_156_);
v___x_206_ = lean_infer_type(v_a_205_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_207_, v_a_157_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_Meta_isExprDefEq(v_a_203_, v_a_209_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; uint8_t v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = lean_unbox(v_a_211_);
lean_dec(v_a_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_inc(v___x_201_);
lean_inc(v_a_205_);
v___x_213_ = l_Lean_Meta_mkHEq(v_a_205_, v___x_201_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_Meta_mkHEqRefl(v_a_205_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v_fst_172_ = v_a_214_;
v_snd_173_ = v_a_216_;
v___y_174_ = v_a_156_;
v___y_175_ = v_a_157_;
v___y_176_ = v_a_158_;
v___y_177_ = v_a_159_;
goto v___jp_171_;
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_214_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_217_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_215_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_215_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_a_205_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_225_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_213_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_213_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v___x_233_; 
lean_inc(v___x_201_);
lean_inc(v_a_205_);
v___x_233_ = l_Lean_Meta_mkEq(v_a_205_, v___x_201_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = l_Lean_Meta_mkEqRefl(v_a_205_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v_fst_172_ = v_a_234_;
v_snd_173_ = v_a_236_;
v___y_174_ = v_a_156_;
v___y_175_ = v_a_157_;
v___y_176_ = v_a_158_;
v___y_177_ = v_a_159_;
goto v___jp_171_;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_a_234_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_237_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_a_205_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_245_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_233_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_233_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_205_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_253_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_210_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_210_);
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
lean_dec(v_a_205_);
lean_dec(v_a_203_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_261_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_208_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_208_);
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
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_205_);
lean_dec(v_a_203_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_269_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_206_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_206_);
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
lean_dec(v_a_203_);
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_277_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_204_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_204_);
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
lean_dec(v_i_155_);
lean_dec_ref(v_type_154_);
v_a_285_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_202_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_202_);
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
v___jp_171_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_i_155_, v___x_178_);
lean_dec(v_i_155_);
v___x_180_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_152_, v_xs_153_, v_type_154_, v___x_179_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_200_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_200_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_fst_185_ = lean_ctor_get(v_a_181_, 0);
v_snd_186_ = lean_ctor_get(v_a_181_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_a_181_);
if (v_isSharedCheck_199_ == 0)
{
v___x_188_ = v_a_181_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
lean_dec(v_a_181_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v_snd_173_);
lean_ctor_set(v___x_190_, 1, v_fst_185_);
v___x_191_ = 0;
lean_inc(v_val_170_);
v___x_192_ = l_Lean_mkForall(v_val_170_, v___x_191_, v_fst_172_, v_snd_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_192_);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_194_ = v___x_188_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_198_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_194_);
v___x_196_ = v___x_183_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_173_);
lean_dec_ref(v_fst_172_);
return v___x_180_;
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_i_155_, v___x_293_);
lean_dec(v_i_155_);
v_i_155_ = v___x_294_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_296_, lean_object* v_xs_297_, lean_object* v_type_298_, lean_object* v_i_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_296_, v_xs_297_, v_type_298_, v_i_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_xs_297_);
lean_dec_ref(v_args_296_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* v_k_306_, lean_object* v_b_307_, lean_object* v_c_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; 
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
v___x_314_ = lean_apply_7(v_k_306_, v_b_307_, v_c_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, lean_box(0));
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* v_k_315_, lean_object* v_b_316_, lean_object* v_c_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_315_, v_b_316_, v_c_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* v_type_324_, lean_object* v_maxFVars_x3f_325_, lean_object* v_k_326_, uint8_t v_cleanupAnnotations_327_, uint8_t v_whnfType_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; 
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_334_, 0, v_k_326_);
v___x_335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_324_, v_maxFVars_x3f_325_, v___f_334_, v_cleanupAnnotations_327_, v_whnfType_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* v_type_352_, lean_object* v_maxFVars_x3f_353_, lean_object* v_k_354_, lean_object* v_cleanupAnnotations_355_, lean_object* v_whnfType_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_362_; uint8_t v_whnfType_boxed_363_; lean_object* v_res_364_; 
v_cleanupAnnotations_boxed_362_ = lean_unbox(v_cleanupAnnotations_355_);
v_whnfType_boxed_363_ = lean_unbox(v_whnfType_356_);
v_res_364_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_352_, v_maxFVars_x3f_353_, v_k_354_, v_cleanupAnnotations_boxed_362_, v_whnfType_boxed_363_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_00_u03b1_365_, lean_object* v_type_366_, lean_object* v_maxFVars_x3f_367_, lean_object* v_k_368_, uint8_t v_cleanupAnnotations_369_, uint8_t v_whnfType_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_366_, v_maxFVars_x3f_367_, v_k_368_, v_cleanupAnnotations_369_, v_whnfType_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_00_u03b1_377_, lean_object* v_type_378_, lean_object* v_maxFVars_x3f_379_, lean_object* v_k_380_, lean_object* v_cleanupAnnotations_381_, lean_object* v_whnfType_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_388_; uint8_t v_whnfType_boxed_389_; lean_object* v_res_390_; 
v_cleanupAnnotations_boxed_388_ = lean_unbox(v_cleanupAnnotations_381_);
v_whnfType_boxed_389_ = lean_unbox(v_whnfType_382_);
v_res_390_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_377_, v_type_378_, v_maxFVars_x3f_379_, v_k_380_, v_cleanupAnnotations_boxed_388_, v_whnfType_boxed_389_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_391_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_398_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_398_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_415_, lean_object* v_x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_415_, v_x_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_423_, lean_object* v_mvarId_424_, lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_424_, v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_432_, lean_object* v_mvarId_433_, lean_object* v_x_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_432_, v_mvarId_433_, v_x_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_441_, lean_object* v___x_442_, uint8_t v___x_443_, uint8_t v___x_444_, lean_object* v_xs_445_, lean_object* v_type_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_441_, v_xs_445_, v_type_446_, v___x_442_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_480_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v_fst_454_ = lean_ctor_get(v_a_453_, 0);
v_snd_455_ = lean_ctor_get(v_a_453_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_457_ = v_a_453_;
v_isShared_458_ = v_isSharedCheck_480_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v_a_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_480_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_459_ = 1;
v___x_460_ = l_Lean_Meta_mkForallFVars(v_xs_445_, v_snd_455_, v___x_443_, v___x_444_, v___x_444_, v___x_459_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_471_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_471_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_a_461_);
v___x_466_ = v___x_457_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_fst_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_a_461_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_457_);
lean_dec(v_fst_454_);
v_a_472_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_460_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_460_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
}
else
{
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v_xs_485_, lean_object* v_type_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v___x_4409__boxed_492_; uint8_t v___x_4410__boxed_493_; lean_object* v_res_494_; 
v___x_4409__boxed_492_ = lean_unbox(v___x_483_);
v___x_4410__boxed_493_ = lean_unbox(v___x_484_);
v_res_494_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_481_, v___x_482_, v___x_4409__boxed_492_, v___x_4410__boxed_493_, v_xs_485_, v_type_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_xs_485_);
lean_dec_ref(v_args_481_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v_hName_x3f_500_; 
v___x_499_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
v_hName_x3f_500_ = lean_ctor_get(v___x_499_, 2);
if (lean_obj_tag(v_hName_x3f_500_) == 0)
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_496_, v___x_501_);
v_i_496_ = v___x_502_;
goto _start;
}
else
{
uint8_t v___x_504_; 
v___x_504_ = 1;
return v___x_504_;
}
}
else
{
uint8_t v___x_505_; 
v___x_505_ = 0;
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_as_506_, lean_object* v_i_507_, lean_object* v_stop_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; uint8_t v_res_511_; lean_object* v_r_512_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_508_);
lean_dec(v_stop_508_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_506_, v_i_boxed_509_, v_stop_boxed_510_);
lean_dec_ref(v_as_506_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_513_, size_t v_i_514_, lean_object* v_bs_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_516_ == 0)
{
return v_bs_515_;
}
else
{
lean_object* v_v_517_; lean_object* v_expr_518_; lean_object* v___x_519_; lean_object* v_bs_x27_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_v_517_ = lean_array_uget_borrowed(v_bs_515_, v_i_514_);
v_expr_518_ = lean_ctor_get(v_v_517_, 0);
lean_inc_ref(v_expr_518_);
v___x_519_ = lean_unsigned_to_nat(0u);
v_bs_x27_520_ = lean_array_uset(v_bs_515_, v_i_514_, v___x_519_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_514_, v___x_521_);
v___x_523_ = lean_array_uset(v_bs_x27_520_, v_i_514_, v_expr_518_);
v_i_514_ = v___x_522_;
v_bs_515_ = v___x_523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_528_, v_i_boxed_529_, v_bs_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_560_; 
v_ks_535_ = lean_ctor_get(v_x_531_, 0);
v_vs_536_ = lean_ctor_get(v_x_531_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_560_ == 0)
{
v___x_538_ = v_x_531_;
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_vs_536_);
lean_inc(v_ks_535_);
lean_dec(v_x_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_array_get_size(v_ks_535_);
v___x_541_ = lean_nat_dec_lt(v_x_532_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
lean_dec(v_x_532_);
v___x_542_ = lean_array_push(v_ks_535_, v_x_533_);
v___x_543_ = lean_array_push(v_vs_536_, v_x_534_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_543_);
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_545_ = v___x_538_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v_k_x27_547_; uint8_t v___x_548_; 
v_k_x27_547_ = lean_array_fget_borrowed(v_ks_535_, v_x_532_);
v___x_548_ = l_Lean_instBEqMVarId_beq(v_x_533_, v_k_x27_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; 
if (v_isShared_539_ == 0)
{
v___x_550_ = v___x_538_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_ks_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_vs_536_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_add(v_x_532_, v___x_551_);
lean_dec(v_x_532_);
v_x_531_ = v___x_550_;
v_x_532_ = v___x_552_;
goto _start;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_array_fset(v_ks_535_, v_x_532_, v_x_533_);
v___x_556_ = lean_array_fset(v_vs_536_, v_x_532_, v_x_534_);
lean_dec(v_x_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_556_);
lean_ctor_set(v___x_538_, 0, v___x_555_);
v___x_558_ = v___x_538_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* v_n_561_, lean_object* v_k_562_, lean_object* v_v_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_561_, v___x_564_, v_k_562_, v_v_563_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_567_, size_t v_x_568_, size_t v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_es_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v_j_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_es_572_ = lean_ctor_get(v_x_567_, 0);
v___x_573_ = ((size_t)31ULL);
v___x_574_ = lean_usize_land(v_x_568_, v___x_573_);
v_j_575_ = lean_usize_to_nat(v___x_574_);
v___x_576_ = lean_array_get_size(v_es_572_);
v___x_577_ = lean_nat_dec_lt(v_j_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_dec(v_j_575_);
lean_dec(v_x_571_);
lean_dec(v_x_570_);
return v_x_567_;
}
else
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_616_; 
lean_inc_ref(v_es_572_);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v_x_567_, 0);
lean_dec(v_unused_617_);
v___x_579_ = v_x_567_;
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_x_567_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_v_581_; lean_object* v___x_582_; lean_object* v_xs_x27_583_; lean_object* v___y_585_; 
v_v_581_ = lean_array_fget(v_es_572_, v_j_575_);
v___x_582_ = lean_box(0);
v_xs_x27_583_ = lean_array_fset(v_es_572_, v_j_575_, v___x_582_);
switch(lean_obj_tag(v_v_581_))
{
case 0:
{
lean_object* v_key_590_; lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_601_; 
v_key_590_ = lean_ctor_get(v_v_581_, 0);
v_val_591_ = lean_ctor_get(v_v_581_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_v_581_);
if (v_isSharedCheck_601_ == 0)
{
v___x_593_ = v_v_581_;
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_inc(v_key_590_);
lean_dec(v_v_581_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_instBEqMVarId_beq(v_x_570_, v_key_590_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_593_);
v___x_596_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_590_, v_val_591_, v_x_570_, v_x_571_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___y_585_ = v___x_597_;
goto v___jp_584_;
}
else
{
lean_object* v___x_599_; 
lean_dec(v_val_591_);
lean_dec(v_key_590_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_x_571_);
lean_ctor_set(v___x_593_, 0, v_x_570_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_x_570_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_x_571_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
v___y_585_ = v___x_599_;
goto v___jp_584_;
}
}
}
}
case 1:
{
lean_object* v_node_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_614_; 
v_node_602_ = lean_ctor_get(v_v_581_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_v_581_);
if (v_isSharedCheck_614_ == 0)
{
v___x_604_ = v_v_581_;
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_node_602_);
lean_dec(v_v_581_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_usize_shift_right(v_x_568_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_x_569_, v___x_608_);
v___x_610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_602_, v___x_607_, v___x_609_, v_x_570_, v_x_571_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_610_);
v___x_612_ = v___x_604_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v___y_585_ = v___x_612_;
goto v___jp_584_;
}
}
}
default: 
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_x_570_);
lean_ctor_set(v___x_615_, 1, v_x_571_);
v___y_585_ = v___x_615_;
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_array_fset(v_xs_x27_583_, v_j_575_, v___y_585_);
lean_dec(v_j_575_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_586_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v_ks_618_; lean_object* v_vs_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_637_; 
v_ks_618_ = lean_ctor_get(v_x_567_, 0);
v_vs_619_ = lean_ctor_get(v_x_567_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_637_ == 0)
{
v___x_621_ = v_x_567_;
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_vs_619_);
lean_inc(v_ks_618_);
lean_dec(v_x_567_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_ks_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_vs_619_);
v___x_624_ = v_reuseFailAlloc_636_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v_newNode_625_; size_t v___x_626_; uint8_t v___x_627_; 
v_newNode_625_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_624_, v_x_570_, v_x_571_);
v___x_626_ = ((size_t)7ULL);
v___x_627_ = lean_usize_dec_le(v___x_626_, v_x_569_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_625_);
v___x_629_ = lean_unsigned_to_nat(4u);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
lean_dec(v___x_628_);
if (v___x_630_ == 0)
{
lean_object* v_ks_631_; lean_object* v_vs_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_ks_631_ = lean_ctor_get(v_newNode_625_, 0);
lean_inc_ref(v_ks_631_);
v_vs_632_ = lean_ctor_get(v_newNode_625_, 1);
lean_inc_ref(v_vs_632_);
lean_dec_ref(v_newNode_625_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_635_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_569_, v_ks_631_, v_vs_632_, v___x_633_, v___x_634_);
lean_dec_ref(v_vs_632_);
lean_dec_ref(v_ks_631_);
return v___x_635_;
}
else
{
return v_newNode_625_;
}
}
else
{
return v_newNode_625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_638_, lean_object* v_keys_639_, lean_object* v_vals_640_, lean_object* v_i_641_, lean_object* v_entries_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_array_get_size(v_keys_639_);
v___x_644_ = lean_nat_dec_lt(v_i_641_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v_i_641_);
return v_entries_642_;
}
else
{
lean_object* v_k_645_; lean_object* v_v_646_; uint64_t v___x_647_; size_t v_h_648_; size_t v___x_649_; lean_object* v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v_h_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_k_645_ = lean_array_fget_borrowed(v_keys_639_, v_i_641_);
v_v_646_ = lean_array_fget_borrowed(v_vals_640_, v_i_641_);
v___x_647_ = l_Lean_instHashableMVarId_hash(v_k_645_);
v_h_648_ = lean_uint64_to_usize(v___x_647_);
v___x_649_ = ((size_t)5ULL);
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_sub(v_depth_638_, v___x_651_);
v___x_653_ = lean_usize_mul(v___x_649_, v___x_652_);
v_h_654_ = lean_usize_shift_right(v_h_648_, v___x_653_);
v___x_655_ = lean_nat_add(v_i_641_, v___x_650_);
lean_dec(v_i_641_);
lean_inc(v_v_646_);
lean_inc(v_k_645_);
v___x_656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_642_, v_h_654_, v_depth_638_, v_k_645_, v_v_646_);
v_i_641_ = v___x_655_;
v_entries_642_ = v___x_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_658_, lean_object* v_keys_659_, lean_object* v_vals_660_, lean_object* v_i_661_, lean_object* v_entries_662_){
_start:
{
size_t v_depth_boxed_663_; lean_object* v_res_664_; 
v_depth_boxed_663_ = lean_unbox_usize(v_depth_658_);
lean_dec(v_depth_658_);
v_res_664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_663_, v_keys_659_, v_vals_660_, v_i_661_, v_entries_662_);
lean_dec_ref(v_vals_660_);
lean_dec_ref(v_keys_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
size_t v_x_4595__boxed_670_; size_t v_x_4596__boxed_671_; lean_object* v_res_672_; 
v_x_4595__boxed_670_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_x_4596__boxed_671_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_res_672_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_665_, v_x_4595__boxed_670_, v_x_4596__boxed_671_, v_x_668_, v_x_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
uint64_t v___x_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_676_ = l_Lean_instHashableMVarId_hash(v_x_674_);
v___x_677_ = lean_uint64_to_usize(v___x_676_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_673_, v___x_677_, v___x_678_, v_x_674_, v_x_675_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_680_, lean_object* v_val_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v_mctx_685_; lean_object* v_cache_686_; lean_object* v_zetaDeltaFVarIds_687_; lean_object* v_postponed_688_; lean_object* v_diag_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_719_; 
v___x_684_ = lean_st_ref_take(v___y_682_);
v_mctx_685_ = lean_ctor_get(v___x_684_, 0);
v_cache_686_ = lean_ctor_get(v___x_684_, 1);
v_zetaDeltaFVarIds_687_ = lean_ctor_get(v___x_684_, 2);
v_postponed_688_ = lean_ctor_get(v___x_684_, 3);
v_diag_689_ = lean_ctor_get(v___x_684_, 4);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_719_ == 0)
{
v___x_691_ = v___x_684_;
v_isShared_692_ = v_isSharedCheck_719_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_diag_689_);
lean_inc(v_postponed_688_);
lean_inc(v_zetaDeltaFVarIds_687_);
lean_inc(v_cache_686_);
lean_inc(v_mctx_685_);
lean_dec(v___x_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_719_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_depth_693_; lean_object* v_levelAssignDepth_694_; lean_object* v_lmvarCounter_695_; lean_object* v_mvarCounter_696_; lean_object* v_lDecls_697_; lean_object* v_decls_698_; lean_object* v_userNames_699_; lean_object* v_lAssignment_700_; lean_object* v_eAssignment_701_; lean_object* v_dAssignment_702_; lean_object* v_instanceTypedMVars_703_; lean_object* v_synthNormMemo_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_718_; 
v_depth_693_ = lean_ctor_get(v_mctx_685_, 0);
v_levelAssignDepth_694_ = lean_ctor_get(v_mctx_685_, 1);
v_lmvarCounter_695_ = lean_ctor_get(v_mctx_685_, 2);
v_mvarCounter_696_ = lean_ctor_get(v_mctx_685_, 3);
v_lDecls_697_ = lean_ctor_get(v_mctx_685_, 4);
v_decls_698_ = lean_ctor_get(v_mctx_685_, 5);
v_userNames_699_ = lean_ctor_get(v_mctx_685_, 6);
v_lAssignment_700_ = lean_ctor_get(v_mctx_685_, 7);
v_eAssignment_701_ = lean_ctor_get(v_mctx_685_, 8);
v_dAssignment_702_ = lean_ctor_get(v_mctx_685_, 9);
v_instanceTypedMVars_703_ = lean_ctor_get(v_mctx_685_, 10);
v_synthNormMemo_704_ = lean_ctor_get(v_mctx_685_, 11);
v_isSharedCheck_718_ = !lean_is_exclusive(v_mctx_685_);
if (v_isSharedCheck_718_ == 0)
{
v___x_706_ = v_mctx_685_;
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_synthNormMemo_704_);
lean_inc(v_instanceTypedMVars_703_);
lean_inc(v_dAssignment_702_);
lean_inc(v_eAssignment_701_);
lean_inc(v_lAssignment_700_);
lean_inc(v_userNames_699_);
lean_inc(v_decls_698_);
lean_inc(v_lDecls_697_);
lean_inc(v_mvarCounter_696_);
lean_inc(v_lmvarCounter_695_);
lean_inc(v_levelAssignDepth_694_);
lean_inc(v_depth_693_);
lean_dec(v_mctx_685_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_box(0);
v___x_709_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_701_, v_mvarId_680_, v_val_681_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 8, v___x_709_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_depth_693_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_levelAssignDepth_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_lmvarCounter_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_mvarCounter_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_lDecls_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_decls_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_userNames_699_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_lAssignment_700_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_717_, 9, v_dAssignment_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 10, v_instanceTypedMVars_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 11, v_synthNormMemo_704_);
v___x_711_ = v_reuseFailAlloc_717_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_711_);
v___x_713_ = v___x_691_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_cache_686_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_zetaDeltaFVarIds_687_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_postponed_688_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_diag_689_);
v___x_713_ = v_reuseFailAlloc_716_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_st_ref_put(v___y_682_, v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_708_);
return v___x_715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_720_, lean_object* v_val_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_720_, v_val_721_, v___y_722_);
lean_dec(v___y_722_);
return v_res_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_728_, lean_object* v___x_729_, lean_object* v_args_730_, uint8_t v_transparency_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
lean_inc(v___x_729_);
lean_inc(v_mvarId_728_);
v___x_737_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_728_, v___x_729_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
lean_dec_ref_known(v___x_737_, 1);
lean_inc(v_mvarId_728_);
v___x_738_ = l_Lean_MVarId_getTag(v_mvarId_728_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
lean_inc(v_mvarId_728_);
v___x_740_ = l_Lean_MVarId_getType(v_mvarId_728_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_856_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_741_, v___y_733_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_856_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_856_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_856_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_730_, v_transparency_731_, v_a_743_, v___x_747_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___x_824_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_n(v_a_749_, 2);
lean_dec_ref_known(v___x_748_, 1);
v___x_824_ = l_Lean_Meta_isTypeCorrect(v_a_749_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; uint8_t v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = lean_unbox(v_a_825_);
lean_dec(v_a_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_749_);
v___x_828_ = l_Lean_indentExpr(v_a_749_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_inc(v_mvarId_728_);
v___x_831_ = l_Lean_Meta_throwTacticEx___redArg(v___x_729_, v_mvarId_728_, v___x_830_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
v___y_775_ = v___y_732_;
v___y_776_ = v___y_733_;
v___y_777_ = v___y_734_;
v___y_778_ = v___y_735_;
goto v___jp_774_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_749_);
lean_del_object(v___x_745_);
lean_dec(v_a_739_);
lean_dec_ref(v_args_730_);
lean_dec(v_mvarId_728_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec(v___x_729_);
v___y_775_ = v___y_732_;
v___y_776_ = v___y_733_;
v___y_777_ = v___y_734_;
v___y_778_ = v___y_735_;
goto v___jp_774_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_749_);
lean_del_object(v___x_745_);
lean_dec(v_a_739_);
lean_dec_ref(v_args_730_);
lean_dec(v___x_729_);
lean_dec(v_mvarId_728_);
v_a_840_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_824_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_824_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
v___jp_750_:
{
uint8_t v___x_758_; lean_object* v___x_759_; 
v___x_758_ = 1;
v___x_759_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_749_, v_a_739_, v___y_755_, v___y_754_, v___y_756_, v___y_752_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_n(v_a_760_, 2);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = l_Lean_mkAppN(v_a_760_, v___y_753_);
lean_dec_ref(v___y_753_);
v___x_762_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_728_, v___x_761_, v___y_754_);
lean_dec_ref(v___x_762_);
v___x_763_ = l_Lean_Expr_mvarId_x21(v_a_760_);
lean_dec(v_a_760_);
v___x_764_ = lean_box(0);
v___x_765_ = l_Lean_Meta_introNCore(v___x_763_, v___y_751_, v___x_764_, v___y_757_, v___x_758_, v___y_755_, v___y_754_, v___y_756_, v___y_752_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___y_753_);
lean_dec(v___y_751_);
lean_dec(v_mvarId_728_);
v_a_766_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_759_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
v___jp_774_:
{
size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_sz_779_ = lean_array_size(v_args_730_);
v___x_780_ = ((size_t)0ULL);
lean_inc_ref(v_args_730_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_779_, v___x_780_, v_args_730_);
v___x_782_ = lean_array_get_size(v_args_730_);
v___x_783_ = lean_nat_dec_lt(v___x_747_, v___x_782_);
if (v___x_783_ == 0)
{
lean_del_object(v___x_745_);
lean_dec_ref(v_args_730_);
v___y_751_ = v___x_782_;
v___y_752_ = v___y_778_;
v___y_753_ = v___x_781_;
v___y_754_ = v___y_776_;
v___y_755_ = v___y_775_;
v___y_756_ = v___y_777_;
v___y_757_ = v___x_783_;
goto v___jp_750_;
}
else
{
if (v___x_783_ == 0)
{
lean_del_object(v___x_745_);
lean_dec_ref(v_args_730_);
v___y_751_ = v___x_782_;
v___y_752_ = v___y_778_;
v___y_753_ = v___x_781_;
v___y_754_ = v___y_776_;
v___y_755_ = v___y_775_;
v___y_756_ = v___y_777_;
v___y_757_ = v___x_783_;
goto v___jp_750_;
}
else
{
size_t v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_usize_of_nat(v___x_782_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_730_, v___x_780_, v___x_784_);
if (v___x_785_ == 0)
{
lean_del_object(v___x_745_);
lean_dec_ref(v_args_730_);
v___y_751_ = v___x_782_;
v___y_752_ = v___y_778_;
v___y_753_ = v___x_781_;
v___y_754_ = v___y_776_;
v___y_755_ = v___y_775_;
v___y_756_ = v___y_777_;
v___y_757_ = v___x_785_;
goto v___jp_750_;
}
else
{
uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_791_; 
v___x_786_ = 0;
v___x_787_ = lean_box(v___x_786_);
v___x_788_ = lean_box(v___x_785_);
v___f_789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_789_, 0, v_args_730_);
lean_closure_set(v___f_789_, 1, v___x_747_);
lean_closure_set(v___f_789_, 2, v___x_787_);
lean_closure_set(v___f_789_, 3, v___x_788_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v___x_782_);
v___x_791_ = v___x_745_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_782_);
v___x_791_ = v_reuseFailAlloc_823_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_749_, v___x_791_, v___f_789_, v___x_786_, v___x_786_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_796_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v_fst_794_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_fst_794_);
v_snd_795_ = lean_ctor_get(v_a_793_, 1);
lean_inc(v_snd_795_);
lean_dec(v_a_793_);
v___x_796_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_795_, v_a_739_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_n(v_a_797_, 2);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_mkAppN(v_a_797_, v___x_781_);
lean_dec_ref(v___x_781_);
lean_inc(v_fst_794_);
v___x_799_ = lean_array_mk(v_fst_794_);
v___x_800_ = l_Lean_mkAppN(v___x_798_, v___x_799_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_728_, v___x_800_, v___y_776_);
lean_dec_ref(v___x_801_);
v___x_802_ = l_Lean_Expr_mvarId_x21(v_a_797_);
lean_dec(v_a_797_);
v___x_803_ = l_List_lengthTR___redArg(v_fst_794_);
lean_dec(v_fst_794_);
v___x_804_ = lean_nat_add(v___x_782_, v___x_803_);
lean_dec(v___x_803_);
v___x_805_ = lean_box(0);
v___x_806_ = l_Lean_Meta_introNCore(v___x_802_, v___x_804_, v___x_805_, v___x_786_, v___x_785_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_fst_794_);
lean_dec_ref(v___x_781_);
lean_dec(v_mvarId_728_);
v_a_807_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_796_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_796_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v___x_781_);
lean_dec(v_a_739_);
lean_dec(v_mvarId_728_);
v_a_815_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_792_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_792_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
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
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_745_);
lean_dec(v_a_739_);
lean_dec_ref(v_args_730_);
lean_dec(v___x_729_);
lean_dec(v_mvarId_728_);
v_a_848_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_748_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_748_);
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
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v_a_739_);
lean_dec_ref(v_args_730_);
lean_dec(v___x_729_);
lean_dec(v_mvarId_728_);
v_a_857_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_740_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_740_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_args_730_);
lean_dec(v___x_729_);
lean_dec(v_mvarId_728_);
v_a_865_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_738_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_738_);
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
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_args_730_);
lean_dec(v___x_729_);
lean_dec(v_mvarId_728_);
v_a_873_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_737_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_737_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_881_, lean_object* v___x_882_, lean_object* v_args_883_, lean_object* v_transparency_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_transparency_boxed_890_; lean_object* v_res_891_; 
v_transparency_boxed_890_ = lean_unbox(v_transparency_884_);
v_res_891_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_881_, v___x_882_, v_args_883_, v_transparency_boxed_890_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_895_, lean_object* v_args_896_, uint8_t v_transparency_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___x_906_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_904_ = lean_box(v_transparency_897_);
lean_inc(v_mvarId_895_);
v___f_905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_905_, 0, v_mvarId_895_);
lean_closure_set(v___f_905_, 1, v___x_903_);
lean_closure_set(v___f_905_, 2, v_args_896_);
lean_closure_set(v___f_905_, 3, v___x_904_);
v___x_906_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_895_, v___f_905_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_907_, lean_object* v_args_908_, lean_object* v_transparency_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_transparency_boxed_915_; lean_object* v_res_916_; 
v_transparency_boxed_915_ = lean_unbox(v_transparency_909_);
v_res_916_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_907_, v_args_908_, v_transparency_boxed_915_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_917_, lean_object* v_val_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_917_, v_val_918_, v___y_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_925_, lean_object* v_val_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_925_, v_val_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_934_, v_x_935_, v_x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, size_t v_x_940_, size_t v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_939_, v_x_940_, v_x_941_, v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_5170__boxed_951_; size_t v_x_5171__boxed_952_; lean_object* v_res_953_; 
v_x_5170__boxed_951_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_x_5171__boxed_952_ = lean_unbox_usize(v_x_948_);
lean_dec(v_x_948_);
v_res_953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_945_, v_x_946_, v_x_5170__boxed_951_, v_x_5171__boxed_952_, v_x_949_, v_x_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_954_, lean_object* v_n_955_, lean_object* v_k_956_, lean_object* v_v_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_955_, v_k_956_, v_v_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_959_, size_t v_depth_960_, lean_object* v_keys_961_, lean_object* v_vals_962_, lean_object* v_heq_963_, lean_object* v_i_964_, lean_object* v_entries_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_960_, v_keys_961_, v_vals_962_, v_i_964_, v_entries_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_967_, lean_object* v_depth_968_, lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_heq_971_, lean_object* v_i_972_, lean_object* v_entries_973_){
_start:
{
size_t v_depth_boxed_974_; lean_object* v_res_975_; 
v_depth_boxed_974_ = lean_unbox_usize(v_depth_968_);
lean_dec(v_depth_968_);
v_res_975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_967_, v_depth_boxed_974_, v_keys_969_, v_vals_970_, v_heq_971_, v_i_972_, v_entries_973_);
lean_dec_ref(v_vals_970_);
lean_dec_ref(v_keys_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_977_, v_x_978_, v_x_979_, v_x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_982_, lean_object* v_args_983_, uint8_t v_transparency_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_982_, v_args_983_, v_transparency_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_991_, lean_object* v_args_992_, lean_object* v_transparency_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_transparency_boxed_999_; lean_object* v_res_1000_; 
v_transparency_boxed_999_ = lean_unbox(v_transparency_993_);
v_res_1000_ = l_Lean_MVarId_generalize(v_mvarId_991_, v_args_992_, v_transparency_boxed_999_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_b_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1005_ == 0)
{
return v_b_1004_;
}
else
{
lean_object* v_snd_1006_; lean_object* v_fst_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1040_; 
v_snd_1006_ = lean_ctor_get(v_b_1004_, 1);
v_fst_1007_ = lean_ctor_get(v_b_1004_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_b_1004_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1009_ = v_b_1004_;
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1006_);
lean_inc(v_fst_1007_);
lean_dec(v_b_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_array_1011_; lean_object* v_start_1012_; lean_object* v_stop_1013_; uint8_t v___x_1014_; 
v_array_1011_ = lean_ctor_get(v_snd_1006_, 0);
v_start_1012_ = lean_ctor_get(v_snd_1006_, 1);
v_stop_1013_ = lean_ctor_get(v_snd_1006_, 2);
v___x_1014_ = lean_nat_dec_lt(v_start_1012_, v_stop_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1016_; 
if (v_isShared_1010_ == 0)
{
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_snd_1006_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1036_; 
lean_inc(v_stop_1013_);
lean_inc(v_start_1012_);
lean_inc_ref(v_array_1011_);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_snd_1006_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; lean_object* v_unused_1038_; lean_object* v_unused_1039_; 
v_unused_1037_ = lean_ctor_get(v_snd_1006_, 2);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_snd_1006_, 1);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v_snd_1006_, 0);
lean_dec(v_unused_1039_);
v___x_1019_ = v_snd_1006_;
v_isShared_1020_ = v_isSharedCheck_1036_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_snd_1006_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1036_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_a_1021_ = lean_array_uget_borrowed(v_as_1001_, v_i_1003_);
v___x_1022_ = lean_array_fget(v_array_1011_, v_start_1012_);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_start_1012_, v___x_1023_);
lean_dec(v_start_1012_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1024_);
v___x_1026_ = v___x_1019_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_array_1011_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_stop_1013_);
v___x_1026_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = l_Lean_mkFVar(v___x_1022_);
lean_inc(v_a_1021_);
v___x_1028_ = l_Lean_Meta_FVarSubst_insert(v_fst_1007_, v_a_1021_, v___x_1027_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1026_);
lean_ctor_set(v___x_1009_, 0, v___x_1028_);
v___x_1030_ = v___x_1009_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1026_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
size_t v___x_1031_; size_t v___x_1032_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1003_, v___x_1031_);
v_i_1003_ = v___x_1032_;
v_b_1004_ = v___x_1030_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_){
_start:
{
size_t v_sz_boxed_1045_; size_t v_i_boxed_1046_; lean_object* v_res_1047_; 
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1046_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1041_, v_sz_boxed_1045_, v_i_boxed_1046_, v_b_1044_);
lean_dec_ref(v_as_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_bs_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_bs_1050_);
return v___x_1054_;
}
else
{
lean_object* v_v_1055_; lean_object* v_expr_1056_; lean_object* v_xName_x3f_1057_; lean_object* v_hName_x3f_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1081_; 
v_v_1055_ = lean_array_uget(v_bs_1050_, v_i_1049_);
v_expr_1056_ = lean_ctor_get(v_v_1055_, 0);
v_xName_x3f_1057_ = lean_ctor_get(v_v_1055_, 1);
v_hName_x3f_1058_ = lean_ctor_get(v_v_1055_, 2);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_v_1055_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1060_ = v_v_1055_;
v_isShared_1061_ = v_isSharedCheck_1081_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_hName_x3f_1058_);
lean_inc(v_xName_x3f_1057_);
lean_inc(v_expr_1056_);
lean_dec(v_v_1055_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1081_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v_bs_x27_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v_bs_x27_1063_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1062_);
v___x_1064_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1056_, v___y_1051_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_a_1065_);
v___x_1067_ = v___x_1060_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1065_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_xName_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_hName_x3f_1058_);
v___x_1067_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1049_, v___x_1068_);
v___x_1070_ = lean_array_uset(v_bs_x27_1063_, v_i_1049_, v___x_1067_);
v_i_1049_ = v___x_1069_;
v_bs_1050_ = v___x_1070_;
goto _start;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_bs_x27_1063_);
lean_del_object(v___x_1060_);
lean_dec(v_hName_x3f_1058_);
lean_dec(v_xName_x3f_1057_);
v_a_1073_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1064_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1082_, lean_object* v_i_1083_, lean_object* v_bs_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
size_t v_sz_boxed_1087_; size_t v_i_boxed_1088_; lean_object* v_res_1089_; 
v_sz_boxed_1087_ = lean_unbox_usize(v_sz_1082_);
lean_dec(v_sz_1082_);
v_i_boxed_1088_ = lean_unbox_usize(v_i_1083_);
lean_dec(v_i_1083_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1087_, v_i_boxed_1088_, v_bs_1084_, v___y_1085_);
lean_dec(v___y_1085_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1090_, lean_object* v_a_1091_, lean_object* v_as_1092_, size_t v_i_1093_, size_t v_stop_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_usize_dec_eq(v_i_1093_, v_stop_1094_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v_expr_1102_; lean_object* v___x_1103_; uint8_t v_transparency_1104_; uint8_t v___x_1105_; lean_object* v___y_1107_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1101_ = lean_array_uget_borrowed(v_as_1092_, v_i_1093_);
v_expr_1102_ = lean_ctor_get(v___x_1101_, 0);
v___x_1103_ = l_Lean_Meta_Context_config(v___y_1095_);
v_transparency_1104_ = lean_ctor_get_uint8(v___x_1103_, 9);
lean_dec_ref(v___x_1103_);
v___x_1105_ = 1;
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1104_, v_transparency_1090_);
if (v___x_1130_ == 0)
{
lean_object* v_keyedConfig_1131_; uint8_t v_trackZetaDelta_1132_; lean_object* v_zetaDeltaSet_1133_; lean_object* v_lctx_1134_; lean_object* v_localInstances_1135_; lean_object* v_defEqCtx_x3f_1136_; lean_object* v_synthPendingDepth_1137_; lean_object* v_customCanUnfoldPredicate_x3f_1138_; uint8_t v_univApprox_1139_; uint8_t v_inTypeClassResolution_1140_; uint8_t v_cacheInferType_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_keyedConfig_1131_ = lean_ctor_get(v___y_1095_, 0);
v_trackZetaDelta_1132_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*7);
v_zetaDeltaSet_1133_ = lean_ctor_get(v___y_1095_, 1);
v_lctx_1134_ = lean_ctor_get(v___y_1095_, 2);
v_localInstances_1135_ = lean_ctor_get(v___y_1095_, 3);
v_defEqCtx_x3f_1136_ = lean_ctor_get(v___y_1095_, 4);
v_synthPendingDepth_1137_ = lean_ctor_get(v___y_1095_, 5);
v_customCanUnfoldPredicate_x3f_1138_ = lean_ctor_get(v___y_1095_, 6);
v_univApprox_1139_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1140_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*7 + 2);
v_cacheInferType_1141_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1131_);
v___x_1142_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_1090_, v_keyedConfig_1131_);
lean_inc(v_customCanUnfoldPredicate_x3f_1138_);
lean_inc(v_synthPendingDepth_1137_);
lean_inc(v_defEqCtx_x3f_1136_);
lean_inc_ref(v_localInstances_1135_);
lean_inc_ref(v_lctx_1134_);
lean_inc(v_zetaDeltaSet_1133_);
v___x_1143_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_zetaDeltaSet_1133_);
lean_ctor_set(v___x_1143_, 2, v_lctx_1134_);
lean_ctor_set(v___x_1143_, 3, v_localInstances_1135_);
lean_ctor_set(v___x_1143_, 4, v_defEqCtx_x3f_1136_);
lean_ctor_set(v___x_1143_, 5, v_synthPendingDepth_1137_);
lean_ctor_set(v___x_1143_, 6, v_customCanUnfoldPredicate_x3f_1138_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*7, v_trackZetaDelta_1132_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*7 + 1, v_univApprox_1139_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1140_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*7 + 3, v_cacheInferType_1141_);
lean_inc_ref(v_expr_1102_);
lean_inc_ref(v_a_1091_);
v___x_1144_ = l_Lean_Meta_kabstract(v_a_1091_, v_expr_1102_, v___x_1129_, v___x_1143_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec_ref_known(v___x_1143_, 7);
v___y_1107_ = v___x_1144_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1145_; 
lean_inc_ref(v_expr_1102_);
lean_inc_ref(v_a_1091_);
v___x_1145_ = l_Lean_Meta_kabstract(v_a_1091_, v_expr_1102_, v___x_1129_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v___y_1107_ = v___x_1145_;
goto v___jp_1106_;
}
v___jp_1106_:
{
if (lean_obj_tag(v___y_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1120_; 
v_a_1108_ = lean_ctor_get(v___y_1107_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___y_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1110_ = v___y_1107_;
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___y_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1120_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Expr_hasLooseBVars(v_a_1108_);
lean_dec(v_a_1108_);
if (v___x_1112_ == 0)
{
size_t v___x_1113_; size_t v___x_1114_; 
lean_del_object(v___x_1110_);
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_add(v_i_1093_, v___x_1113_);
v_i_1093_ = v___x_1114_;
goto _start;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec_ref(v_a_1091_);
v___x_1116_ = lean_box(v___x_1105_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1116_);
v___x_1118_ = v___x_1110_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_a_1091_);
v_a_1121_ = lean_ctor_get(v___y_1107_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___y_1107_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___y_1107_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___y_1107_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
else
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_a_1091_);
v___x_1146_ = 0;
v___x_1147_ = lean_box(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1149_, lean_object* v_a_1150_, lean_object* v_as_1151_, lean_object* v_i_1152_, lean_object* v_stop_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_transparency_boxed_1159_; size_t v_i_boxed_1160_; size_t v_stop_boxed_1161_; lean_object* v_res_1162_; 
v_transparency_boxed_1159_ = lean_unbox(v_transparency_1149_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_stop_boxed_1161_ = lean_unbox_usize(v_stop_1153_);
lean_dec(v_stop_1153_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1159_, v_a_1150_, v_as_1151_, v_i_boxed_1160_, v_stop_boxed_1161_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1151_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1163_, uint8_t v_transparency_1164_, lean_object* v_as_1165_, size_t v_i_1166_, size_t v_stop_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_a_1175_; uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_eq(v_i_1166_, v_stop_1167_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_array_uget_borrowed(v_as_1165_, v_i_1166_);
lean_inc(v___x_1180_);
v___x_1181_ = l_Lean_FVarId_getType___redArg(v___x_1180_, v___y_1169_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1182_, v___y_1170_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_array_get_size(v_a_1163_);
v___x_1187_ = lean_nat_dec_lt(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_dec(v_a_1184_);
v_a_1175_ = v_b_1168_;
goto v___jp_1174_;
}
else
{
if (v___x_1187_ == 0)
{
lean_dec(v_a_1184_);
v_a_1175_ = v_b_1168_;
goto v___jp_1174_;
}
else
{
size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = lean_usize_of_nat(v___x_1186_);
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1164_, v_a_1184_, v_a_1163_, v___x_1188_, v___x_1189_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; uint8_t v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = lean_unbox(v_a_1191_);
lean_dec(v_a_1191_);
if (v___x_1192_ == 0)
{
v_a_1175_ = v_b_1168_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1193_; 
lean_inc(v___x_1180_);
v___x_1193_ = lean_array_push(v_b_1168_, v___x_1180_);
v_a_1175_ = v___x_1193_;
goto v___jp_1174_;
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_b_1168_);
v_a_1194_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1190_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1190_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_b_1168_);
v_a_1202_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1183_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1183_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_b_1168_);
v_a_1210_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1181_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1181_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_b_1168_);
return v___x_1218_;
}
v___jp_1174_:
{
size_t v___x_1176_; size_t v___x_1177_; 
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = lean_usize_add(v_i_1166_, v___x_1176_);
v_i_1166_ = v___x_1177_;
v_b_1168_ = v_a_1175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1219_, lean_object* v_transparency_1220_, lean_object* v_as_1221_, lean_object* v_i_1222_, lean_object* v_stop_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_transparency_boxed_1230_; size_t v_i_boxed_1231_; size_t v_stop_boxed_1232_; lean_object* v_res_1233_; 
v_transparency_boxed_1230_ = lean_unbox(v_transparency_1220_);
v_i_boxed_1231_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_stop_boxed_1232_ = lean_unbox_usize(v_stop_1223_);
lean_dec(v_stop_1223_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1219_, v_transparency_boxed_1230_, v_as_1221_, v_i_boxed_1231_, v_stop_boxed_1232_, v_b_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v_as_1221_);
lean_dec_ref(v_a_1219_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1234_, lean_object* v_a_1235_, lean_object* v_as_1236_, size_t v_i_1237_, size_t v_stop_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_a_1246_; uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_eq(v_i_1237_, v_stop_1238_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_array_uget_borrowed(v_as_1236_, v_i_1237_);
lean_inc(v___x_1251_);
v___x_1252_ = l_Lean_FVarId_getType___redArg(v___x_1251_, v___y_1240_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1253_, v___y_1241_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v_a_1235_);
v___x_1258_ = lean_nat_dec_lt(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_dec(v_a_1255_);
v_a_1246_ = v_b_1239_;
goto v___jp_1245_;
}
else
{
if (v___x_1258_ == 0)
{
lean_dec(v_a_1255_);
v_a_1246_ = v_b_1239_;
goto v___jp_1245_;
}
else
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = lean_usize_of_nat(v___x_1257_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1234_, v_a_1255_, v_a_1235_, v___x_1259_, v___x_1260_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; uint8_t v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1263_ == 0)
{
v_a_1246_ = v_b_1239_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1264_; 
lean_inc(v___x_1251_);
v___x_1264_ = lean_array_push(v_b_1239_, v___x_1251_);
v_a_1246_ = v___x_1264_;
goto v___jp_1245_;
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_b_1239_);
v_a_1265_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1261_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_b_1239_);
v_a_1273_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1254_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1254_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_b_1239_);
v_a_1281_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1252_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1252_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_b_1239_);
return v___x_1289_;
}
v___jp_1245_:
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1237_, v___x_1247_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1235_, v_transparency_1234_, v_as_1236_, v___x_1248_, v_stop_1238_, v_a_1246_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1290_, lean_object* v_a_1291_, lean_object* v_as_1292_, lean_object* v_i_1293_, lean_object* v_stop_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_transparency_boxed_1301_; size_t v_i_boxed_1302_; size_t v_stop_boxed_1303_; lean_object* v_res_1304_; 
v_transparency_boxed_1301_ = lean_unbox(v_transparency_1290_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_stop_boxed_1303_ = lean_unbox_usize(v_stop_1294_);
lean_dec(v_stop_1294_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1301_, v_a_1291_, v_as_1292_, v_i_boxed_1302_, v_stop_boxed_1303_, v_b_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_as_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1307_, lean_object* v_args_1308_, lean_object* v_hyps_1309_, lean_object* v_fvarSubst_1310_, uint8_t v_transparency_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_array_get_size(v_hyps_1309_);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_nat_dec_eq(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
uint8_t v___x_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = 1;
v_sz_1321_ = lean_array_size(v_args_1308_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1321_, v___x_1322_, v_args_1308_, v_a_1313_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_a_1326_; lean_object* v___y_1400_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1410_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1411_ = lean_nat_dec_lt(v___x_1318_, v___x_1317_);
if (v___x_1411_ == 0)
{
v_a_1326_ = v___x_1410_;
goto v___jp_1325_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_le(v___x_1317_, v___x_1317_);
if (v___x_1412_ == 0)
{
if (v___x_1411_ == 0)
{
v_a_1326_ = v___x_1410_;
goto v___jp_1325_;
}
else
{
size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_usize_of_nat(v___x_1317_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1311_, v_a_1324_, v_hyps_1309_, v___x_1322_, v___x_1413_, v___x_1410_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
v___y_1400_ = v___x_1414_;
goto v___jp_1399_;
}
}
else
{
size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_usize_of_nat(v___x_1317_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1311_, v_a_1324_, v_hyps_1309_, v___x_1322_, v___x_1415_, v___x_1410_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
v___y_1400_ = v___x_1416_;
goto v___jp_1399_;
}
}
v___jp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_MVarId_revert(v_mvarId_1307_, v_a_1326_, v___x_1320_, v___x_1319_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1331_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v_fst_1329_ = lean_ctor_get(v_a_1328_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v_a_1328_, 1);
lean_inc(v_snd_1330_);
lean_dec(v_a_1328_);
v___x_1331_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1330_, v_a_1324_, v_transparency_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1382_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v_fst_1333_ = lean_ctor_get(v_a_1332_, 0);
v_snd_1334_ = lean_ctor_get(v_a_1332_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1332_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1336_ = v_a_1332_;
v_isShared_1337_ = v_isSharedCheck_1382_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1334_);
lean_inc(v_fst_1333_);
lean_dec(v_a_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1382_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_array_get_size(v_fst_1329_);
v___x_1339_ = lean_box(0);
v___x_1340_ = l_Lean_Meta_introNCore(v_snd_1334_, v___x_1338_, v___x_1339_, v___x_1319_, v___x_1320_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1373_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1373_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1373_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1372_; 
v_fst_1345_ = lean_ctor_get(v_a_1341_, 0);
v_snd_1346_ = lean_ctor_get(v_a_1341_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1348_ = v_a_1341_;
v_isShared_1349_ = v_isSharedCheck_1372_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_inc(v_fst_1345_);
lean_dec(v_a_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1372_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_array_get_size(v_fst_1345_);
v___x_1351_ = l_Array_toSubarray___redArg(v_fst_1345_, v___x_1318_, v___x_1350_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1351_);
lean_ctor_set(v___x_1348_, 0, v_fvarSubst_1310_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_fvarSubst_1310_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
size_t v_sz_1354_; lean_object* v___x_1355_; lean_object* v_fst_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1369_; 
v_sz_1354_ = lean_array_size(v_fst_1329_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1329_, v_sz_1354_, v___x_1322_, v___x_1353_);
lean_dec(v_fst_1329_);
v_fst_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v___x_1355_, 1);
lean_dec(v_unused_1370_);
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1369_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_fst_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1369_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_snd_1346_);
lean_ctor_set(v___x_1358_, 0, v_fst_1333_);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1333_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_snd_1346_);
v___x_1361_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1361_);
lean_ctor_set(v___x_1336_, 0, v_fst_1356_);
v___x_1363_ = v___x_1336_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1356_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1363_);
v___x_1365_ = v___x_1343_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
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
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1336_);
lean_dec(v_fst_1333_);
lean_dec(v_fst_1329_);
lean_dec(v_fvarSubst_1310_);
v_a_1374_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1340_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1340_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_fst_1329_);
lean_dec(v_fvarSubst_1310_);
v_a_1383_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1331_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1331_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_a_1324_);
lean_dec(v_fvarSubst_1310_);
v_a_1391_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1327_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1327_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
v___jp_1399_:
{
if (lean_obj_tag(v___y_1400_) == 0)
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___y_1400_, 1);
v_a_1326_ = v_a_1401_;
goto v___jp_1325_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_a_1324_);
lean_dec(v_fvarSubst_1310_);
lean_dec(v_mvarId_1307_);
v_a_1402_ = lean_ctor_get(v___y_1400_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___y_1400_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___y_1400_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___y_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_fvarSubst_1310_);
lean_dec(v_mvarId_1307_);
v_a_1417_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1323_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1323_);
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
else
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1307_, v_args_1308_, v_transparency_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1434_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_fvarSubst_1310_);
lean_ctor_set(v___x_1430_, 1, v_a_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_fvarSubst_1310_);
v_a_1435_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1425_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1425_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1443_, lean_object* v_args_1444_, lean_object* v_hyps_1445_, lean_object* v_fvarSubst_1446_, lean_object* v_transparency_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
uint8_t v_transparency_boxed_1453_; lean_object* v_res_1454_; 
v_transparency_boxed_1453_ = lean_unbox(v_transparency_1447_);
v_res_1454_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1443_, v_args_1444_, v_hyps_1445_, v_fvarSubst_1446_, v_transparency_boxed_1453_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec_ref(v_hyps_1445_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_bs_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1455_, v_i_1456_, v_bs_1457_, v___y_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1464_, lean_object* v_i_1465_, lean_object* v_bs_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1464_);
lean_dec(v_sz_1464_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1472_, v_i_boxed_1473_, v_bs_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1474_;
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
