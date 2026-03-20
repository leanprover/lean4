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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2;
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
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
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
lean_inc(v_a_74_);
lean_dec_ref(v___x_73_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc(v_a_74_);
v___x_75_ = lean_infer_type(v_a_74_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_76_, v_a_63_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_i_61_, v___x_79_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
v___x_81_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_58_, v_transparency_59_, v_target_60_, v___x_80_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v_xName_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref(v___x_81_);
if (lean_obj_tag(v_xName_x3f_72_) == 1)
{
lean_object* v_val_158_; 
v_val_158_ = lean_ctor_get(v_xName_x3f_72_, 0);
lean_inc(v_val_158_);
v_xName_84_ = v_val_158_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1));
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
v___x_160_ = l_Lean_Core_mkFreshUserName(v___x_159_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref(v___x_160_);
v_xName_84_ = v_a_161_;
v___y_85_ = v_a_62_;
v___y_86_ = v_a_63_;
v___y_87_ = v_a_64_;
v___y_88_ = v_a_65_;
goto v___jp_83_;
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_a_82_);
lean_dec(v_a_78_);
lean_dec(v_a_74_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
v_a_162_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_160_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
v___jp_83_:
{
lean_object* v___x_89_; uint8_t v_foApprox_90_; uint8_t v_ctxApprox_91_; uint8_t v_quasiPatternApprox_92_; uint8_t v_constApprox_93_; uint8_t v_isDefEqStuckEx_94_; uint8_t v_unificationHints_95_; uint8_t v_proofIrrelevance_96_; uint8_t v_assignSyntheticOpaque_97_; uint8_t v_offsetCnstrs_98_; uint8_t v_etaStruct_99_; uint8_t v_univApprox_100_; uint8_t v_iota_101_; uint8_t v_beta_102_; uint8_t v_proj_103_; uint8_t v_zeta_104_; uint8_t v_zetaDelta_105_; uint8_t v_zetaUnused_106_; uint8_t v_zetaHave_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_157_; 
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
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_157_ == 0)
{
v___x_109_ = v___x_89_;
v_isShared_110_ = v_isSharedCheck_157_;
goto v_resetjp_108_;
}
else
{
lean_dec(v___x_89_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_157_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v_trackZetaDelta_111_; lean_object* v_zetaDeltaSet_112_; lean_object* v_lctx_113_; lean_object* v_localInstances_114_; lean_object* v_defEqCtx_x3f_115_; lean_object* v_synthPendingDepth_116_; lean_object* v_canUnfold_x3f_117_; uint8_t v_univApprox_118_; uint8_t v_inTypeClassResolution_119_; uint8_t v_cacheInferType_120_; lean_object* v_config_122_; 
v_trackZetaDelta_111_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*7);
v_zetaDeltaSet_112_ = lean_ctor_get(v___y_85_, 1);
lean_inc(v_zetaDeltaSet_112_);
v_lctx_113_ = lean_ctor_get(v___y_85_, 2);
lean_inc_ref(v_lctx_113_);
v_localInstances_114_ = lean_ctor_get(v___y_85_, 3);
lean_inc_ref(v_localInstances_114_);
v_defEqCtx_x3f_115_ = lean_ctor_get(v___y_85_, 4);
lean_inc(v_defEqCtx_x3f_115_);
v_synthPendingDepth_116_ = lean_ctor_get(v___y_85_, 5);
lean_inc(v_synthPendingDepth_116_);
v_canUnfold_x3f_117_ = lean_ctor_get(v___y_85_, 6);
lean_inc(v_canUnfold_x3f_117_);
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
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 0, v_foApprox_90_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 1, v_ctxApprox_91_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 2, v_quasiPatternApprox_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 3, v_constApprox_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 4, v_isDefEqStuckEx_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 5, v_unificationHints_95_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 6, v_proofIrrelevance_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 7, v_assignSyntheticOpaque_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 8, v_offsetCnstrs_98_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 10, v_etaStruct_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 11, v_univApprox_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 12, v_iota_101_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 13, v_beta_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 14, v_proj_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 15, v_zeta_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 16, v_zetaDelta_105_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 17, v_zetaUnused_106_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, 18, v_zetaHave_107_);
v_config_122_ = v_reuseFailAlloc_156_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
uint64_t v___x_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_148_; 
lean_ctor_set_uint8(v_config_122_, 9, v_transparency_59_);
v___x_123_ = l_Lean_Meta_Context_configKey(v___y_85_);
v_isSharedCheck_148_ = !lean_is_exclusive(v___y_85_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_149_ = lean_ctor_get(v___y_85_, 6);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v___y_85_, 5);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v___y_85_, 4);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v___y_85_, 3);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v___y_85_, 2);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v___y_85_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v___y_85_, 0);
lean_dec(v_unused_155_);
v___x_125_ = v___y_85_;
v_isShared_126_ = v_isSharedCheck_148_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___y_85_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_148_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint64_t v___x_127_; uint64_t v___x_128_; lean_object* v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v_key_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_127_ = 2ULL;
v___x_128_ = lean_uint64_shift_right(v___x_123_, v___x_127_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_uint64_shift_left(v___x_128_, v___x_127_);
v___x_131_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_59_);
v_key_132_ = lean_uint64_lor(v___x_130_, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_133_, 0, v_config_122_);
lean_ctor_set_uint64(v___x_133_, sizeof(void*)*1, v_key_132_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_133_);
v___x_135_ = v___x_125_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_zetaDeltaSet_112_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_lctx_113_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_localInstances_114_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_defEqCtx_x3f_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 5, v_synthPendingDepth_116_);
lean_ctor_set(v_reuseFailAlloc_147_, 6, v_canUnfold_x3f_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_147_, sizeof(void*)*7, v_trackZetaDelta_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_147_, sizeof(void*)*7 + 1, v_univApprox_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_147_, sizeof(void*)*7 + 2, v_inTypeClassResolution_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_147_, sizeof(void*)*7 + 3, v_cacheInferType_120_);
v___x_135_ = v_reuseFailAlloc_147_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_kabstract(v_a_82_, v_a_74_, v___x_129_, v___x_135_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_141_ = 0;
v___x_142_ = l_Lean_mkForall(v_xName_84_, v___x_141_, v_a_78_, v_a_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
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
lean_dec(v_xName_84_);
lean_dec(v_a_78_);
return v___x_136_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_78_);
lean_dec(v_a_74_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v___x_81_;
}
}
else
{
lean_dec(v_a_74_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec_ref(v_target_60_);
return v___x_77_;
}
}
else
{
lean_dec(v_a_74_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec_ref(v_target_60_);
return v___x_75_;
}
}
else
{
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec_ref(v_target_60_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* v_args_170_, lean_object* v_transparency_171_, lean_object* v_target_172_, lean_object* v_i_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
uint8_t v_transparency_boxed_179_; lean_object* v_res_180_; 
v_transparency_boxed_179_ = lean_unbox(v_transparency_171_);
v_res_180_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_170_, v_transparency_boxed_179_, v_target_172_, v_i_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_i_173_);
lean_dec_ref(v_args_170_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* v_args_181_, lean_object* v_xs_182_, lean_object* v_type_183_, lean_object* v_i_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_array_get_size(v_xs_182_);
v___x_191_ = lean_nat_dec_lt(v_i_184_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_type_183_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v_arg_196_; lean_object* v_hName_x3f_197_; 
v___x_195_ = l_Lean_Meta_instInhabitedGeneralizeArg_default;
v_arg_196_ = lean_array_get_borrowed(v___x_195_, v_args_181_, v_i_184_);
v_hName_x3f_197_ = lean_ctor_get(v_arg_196_, 2);
if (lean_obj_tag(v_hName_x3f_197_) == 1)
{
lean_object* v_expr_198_; lean_object* v_val_199_; lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_expr_198_ = lean_ctor_get(v_arg_196_, 0);
v_val_199_ = lean_ctor_get(v_hName_x3f_197_, 0);
v___x_230_ = lean_array_fget_borrowed(v_xs_182_, v_i_184_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v___x_230_);
v___x_231_ = lean_infer_type(v___x_230_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
lean_inc_ref(v_expr_198_);
v___x_233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_198_, v_a_186_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref(v___x_233_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v_a_234_);
v___x_235_ = lean_infer_type(v_a_234_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_236_, v_a_186_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref(v___x_237_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_239_ = l_Lean_Meta_isExprDefEq(v_a_232_, v_a_238_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; uint8_t v___x_241_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = lean_unbox(v_a_240_);
lean_dec(v_a_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v___x_230_);
lean_inc(v_a_234_);
v___x_242_ = l_Lean_Meta_mkHEq(v_a_234_, v___x_230_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v___x_242_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_244_ = l_Lean_Meta_mkHEqRefl(v_a_234_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
v_fst_201_ = v_a_243_;
v_snd_202_ = v_a_245_;
v___y_203_ = v_a_185_;
v___y_204_ = v_a_186_;
v___y_205_ = v_a_187_;
v___y_206_ = v_a_188_;
goto v___jp_200_;
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_243_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_246_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_244_);
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
lean_dec(v_a_234_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_254_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_242_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_242_);
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
lean_object* v___x_262_; 
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v___x_230_);
lean_inc(v_a_234_);
v___x_262_ = l_Lean_Meta_mkEq(v_a_234_, v___x_230_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v___x_262_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_264_ = l_Lean_Meta_mkEqRefl(v_a_234_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v_fst_201_ = v_a_263_;
v_snd_202_ = v_a_265_;
v___y_203_ = v_a_185_;
v___y_204_ = v_a_186_;
v___y_205_ = v_a_187_;
v___y_206_ = v_a_188_;
goto v___jp_200_;
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec(v_a_263_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_266_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_264_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_a_234_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_274_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_262_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_262_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_a_234_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_282_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_239_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_239_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_a_234_);
lean_dec(v_a_232_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_290_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_237_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_237_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_234_);
lean_dec(v_a_232_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_298_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_235_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_235_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_232_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_306_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_233_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_233_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_i_184_);
lean_dec_ref(v_type_183_);
v_a_314_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_231_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_231_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
v___jp_200_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_i_184_, v___x_207_);
lean_dec(v_i_184_);
v___x_209_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_181_, v_xs_182_, v_type_183_, v___x_208_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_229_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_229_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_229_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_229_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_228_; 
v_fst_214_ = lean_ctor_get(v_a_210_, 0);
v_snd_215_ = lean_ctor_get(v_a_210_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_217_ = v_a_210_;
v_isShared_218_ = v_isSharedCheck_228_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_a_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_228_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v_snd_202_);
lean_ctor_set(v___x_219_, 1, v_fst_214_);
v___x_220_ = 0;
lean_inc(v_val_199_);
v___x_221_ = l_Lean_mkForall(v_val_199_, v___x_220_, v_fst_201_, v_snd_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_221_);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_221_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_223_);
v___x_225_ = v___x_212_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
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
}
else
{
lean_dec_ref(v_snd_202_);
lean_dec_ref(v_fst_201_);
return v___x_209_;
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_i_184_, v___x_322_);
lean_dec(v_i_184_);
v_i_184_ = v___x_323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* v_args_325_, lean_object* v_xs_326_, lean_object* v_type_327_, lean_object* v_i_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_325_, v_xs_326_, v_type_327_, v_i_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec_ref(v_xs_326_);
lean_dec_ref(v_args_325_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* v_k_335_, lean_object* v_b_336_, lean_object* v_c_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_apply_7(v_k_335_, v_b_336_, v_c_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, lean_box(0));
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* v_k_344_, lean_object* v_b_345_, lean_object* v_c_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(v_k_344_, v_b_345_, v_c_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* v_type_353_, lean_object* v_maxFVars_x3f_354_, lean_object* v_k_355_, uint8_t v_cleanupAnnotations_356_, uint8_t v_whnfType_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_363_, 0, v_k_355_);
v___x_364_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_353_, v_maxFVars_x3f_354_, v___f_363_, v_cleanupAnnotations_356_, v_whnfType_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
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
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_364_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_364_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* v_type_381_, lean_object* v_maxFVars_x3f_382_, lean_object* v_k_383_, lean_object* v_cleanupAnnotations_384_, lean_object* v_whnfType_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_391_; uint8_t v_whnfType_boxed_392_; lean_object* v_res_393_; 
v_cleanupAnnotations_boxed_391_ = lean_unbox(v_cleanupAnnotations_384_);
v_whnfType_boxed_392_ = lean_unbox(v_whnfType_385_);
v_res_393_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_381_, v_maxFVars_x3f_382_, v_k_383_, v_cleanupAnnotations_boxed_391_, v_whnfType_boxed_392_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* v_00_u03b1_394_, lean_object* v_type_395_, lean_object* v_maxFVars_x3f_396_, lean_object* v_k_397_, uint8_t v_cleanupAnnotations_398_, uint8_t v_whnfType_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_type_395_, v_maxFVars_x3f_396_, v_k_397_, v_cleanupAnnotations_398_, v_whnfType_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* v_00_u03b1_406_, lean_object* v_type_407_, lean_object* v_maxFVars_x3f_408_, lean_object* v_k_409_, lean_object* v_cleanupAnnotations_410_, lean_object* v_whnfType_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_417_; uint8_t v_whnfType_boxed_418_; lean_object* v_res_419_; 
v_cleanupAnnotations_boxed_417_ = lean_unbox(v_cleanupAnnotations_410_);
v_whnfType_boxed_418_ = lean_unbox(v_whnfType_411_);
v_res_419_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(v_00_u03b1_406_, v_type_407_, v_maxFVars_x3f_408_, v_k_409_, v_cleanupAnnotations_boxed_417_, v_whnfType_boxed_418_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* v_mvarId_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_420_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_a_436_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_427_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* v_mvarId_444_, lean_object* v_x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_444_, v_x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* v_00_u03b1_452_, lean_object* v_mvarId_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_453_, v_x_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* v_00_u03b1_461_, lean_object* v_mvarId_462_, lean_object* v_x_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(v_00_u03b1_461_, v_mvarId_462_, v_x_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* v_args_470_, lean_object* v___x_471_, uint8_t v___x_472_, uint8_t v___x_473_, lean_object* v_xs_474_, lean_object* v_type_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
v___x_481_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(v_args_470_, v_xs_474_, v_type_475_, v___x_471_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_509_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
v_fst_483_ = lean_ctor_get(v_a_482_, 0);
v_snd_484_ = lean_ctor_get(v_a_482_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_482_);
if (v_isSharedCheck_509_ == 0)
{
v___x_486_ = v_a_482_;
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_a_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_488_ = 1;
v___x_489_ = l_Lean_Meta_mkForallFVars(v_xs_474_, v_snd_484_, v___x_472_, v___x_473_, v___x_473_, v___x_488_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_500_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_500_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_a_490_);
v___x_495_ = v___x_486_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_490_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_486_);
lean_dec(v_fst_483_);
v_a_501_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_489_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_489_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
else
{
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* v_args_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_xs_514_, lean_object* v_type_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_4915__boxed_521_; uint8_t v___x_4916__boxed_522_; lean_object* v_res_523_; 
v___x_4915__boxed_521_ = lean_unbox(v___x_512_);
v___x_4916__boxed_522_ = lean_unbox(v___x_513_);
v_res_523_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_510_, v___x_511_, v___x_4915__boxed_521_, v___x_4916__boxed_522_, v_xs_514_, v_type_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec_ref(v_xs_514_);
lean_dec_ref(v_args_510_);
return v_res_523_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* v_as_524_, size_t v_i_525_, size_t v_stop_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_eq(v_i_525_, v_stop_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v_hName_x3f_529_; uint8_t v___x_530_; 
v___x_528_ = lean_array_uget_borrowed(v_as_524_, v_i_525_);
v_hName_x3f_529_ = lean_ctor_get(v___x_528_, 2);
v___x_530_ = 1;
if (lean_obj_tag(v_hName_x3f_529_) == 0)
{
if (v___x_527_ == 0)
{
size_t v___x_531_; size_t v___x_532_; 
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_525_, v___x_531_);
v_i_525_ = v___x_532_;
goto _start;
}
else
{
return v___x_530_;
}
}
else
{
return v___x_530_;
}
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_){
_start:
{
size_t v_i_boxed_538_; size_t v_stop_boxed_539_; uint8_t v_res_540_; lean_object* v_r_541_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_539_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_as_535_, v_i_boxed_538_, v_stop_boxed_539_);
lean_dec_ref(v_as_535_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t v_sz_542_, size_t v_i_543_, lean_object* v_bs_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_545_ == 0)
{
return v_bs_544_;
}
else
{
lean_object* v_v_546_; lean_object* v_expr_547_; lean_object* v___x_548_; lean_object* v_bs_x27_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v_v_546_ = lean_array_uget_borrowed(v_bs_544_, v_i_543_);
v_expr_547_ = lean_ctor_get(v_v_546_, 0);
lean_inc_ref(v_expr_547_);
v___x_548_ = lean_unsigned_to_nat(0u);
v_bs_x27_549_ = lean_array_uset(v_bs_544_, v_i_543_, v___x_548_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_543_, v___x_550_);
v___x_552_ = lean_array_uset(v_bs_x27_549_, v_i_543_, v_expr_547_);
v_i_543_ = v___x_551_;
v_bs_544_ = v___x_552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_bs_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_boxed_557_, v_i_boxed_558_, v_bs_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_ks_564_; lean_object* v_vs_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_589_; 
v_ks_564_ = lean_ctor_get(v_x_560_, 0);
v_vs_565_ = lean_ctor_get(v_x_560_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_560_);
if (v_isSharedCheck_589_ == 0)
{
v___x_567_ = v_x_560_;
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_vs_565_);
lean_inc(v_ks_564_);
lean_dec(v_x_560_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_ks_564_);
v___x_570_ = lean_nat_dec_lt(v_x_561_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
lean_dec(v_x_561_);
v___x_571_ = lean_array_push(v_ks_564_, v_x_562_);
v___x_572_ = lean_array_push(v_vs_565_, v_x_563_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_572_);
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_574_ = v___x_567_;
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
else
{
lean_object* v_k_x27_576_; uint8_t v___x_577_; 
v_k_x27_576_ = lean_array_fget_borrowed(v_ks_564_, v_x_561_);
v___x_577_ = l_Lean_instBEqMVarId_beq(v_x_562_, v_k_x27_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; 
if (v_isShared_568_ == 0)
{
v___x_579_ = v___x_567_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_ks_564_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_vs_565_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_x_561_, v___x_580_);
lean_dec(v_x_561_);
v_x_560_ = v___x_579_;
v_x_561_ = v___x_581_;
goto _start;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = lean_array_fset(v_ks_564_, v_x_561_, v_x_562_);
v___x_585_ = lean_array_fset(v_vs_565_, v_x_561_, v_x_563_);
lean_dec(v_x_561_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_585_);
lean_ctor_set(v___x_567_, 0, v___x_584_);
v___x_587_ = v___x_567_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* v_n_590_, lean_object* v_k_591_, lean_object* v_v_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_n_590_, v___x_593_, v_k_591_, v_v_592_);
return v___x_594_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; 
v___x_595_ = ((size_t)5ULL);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_shift_left(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_600_ = lean_usize_sub(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_602_, size_t v_x_603_, size_t v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v_es_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v_j_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_es_607_ = lean_ctor_get(v_x_602_, 0);
v___x_608_ = ((size_t)5ULL);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_611_ = lean_usize_land(v_x_603_, v___x_610_);
v_j_612_ = lean_usize_to_nat(v___x_611_);
v___x_613_ = lean_array_get_size(v_es_607_);
v___x_614_ = lean_nat_dec_lt(v_j_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v_j_612_);
lean_dec(v_x_606_);
lean_dec(v_x_605_);
return v_x_602_;
}
else
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_651_; 
lean_inc_ref(v_es_607_);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_x_602_, 0);
lean_dec(v_unused_652_);
v___x_616_ = v_x_602_;
v_isShared_617_ = v_isSharedCheck_651_;
goto v_resetjp_615_;
}
else
{
lean_dec(v_x_602_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_651_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_xs_x27_620_; lean_object* v___y_622_; 
v_v_618_ = lean_array_fget(v_es_607_, v_j_612_);
v___x_619_ = lean_box(0);
v_xs_x27_620_ = lean_array_fset(v_es_607_, v_j_612_, v___x_619_);
switch(lean_obj_tag(v_v_618_))
{
case 0:
{
lean_object* v_key_627_; lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
v_key_627_ = lean_ctor_get(v_v_618_, 0);
v_val_628_ = lean_ctor_get(v_v_618_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_v_618_);
if (v_isSharedCheck_638_ == 0)
{
v___x_630_ = v_v_618_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_inc(v_key_627_);
lean_dec(v_v_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_instBEqMVarId_beq(v_x_605_, v_key_627_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_del_object(v___x_630_);
v___x_633_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_627_, v_val_628_, v_x_605_, v_x_606_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___y_622_ = v___x_634_;
goto v___jp_621_;
}
else
{
lean_object* v___x_636_; 
lean_dec(v_val_628_);
lean_dec(v_key_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_x_606_);
lean_ctor_set(v___x_630_, 0, v_x_605_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_x_605_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_x_606_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_622_ = v___x_636_;
goto v___jp_621_;
}
}
}
}
case 1:
{
lean_object* v_node_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_649_; 
v_node_639_ = lean_ctor_get(v_v_618_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_v_618_);
if (v_isSharedCheck_649_ == 0)
{
v___x_641_ = v_v_618_;
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_node_639_);
lean_dec(v_v_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_643_ = lean_usize_shift_right(v_x_603_, v___x_608_);
v___x_644_ = lean_usize_add(v_x_604_, v___x_609_);
v___x_645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_639_, v___x_643_, v___x_644_, v_x_605_, v_x_606_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_645_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_622_ = v___x_647_;
goto v___jp_621_;
}
}
}
default: 
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_x_605_);
lean_ctor_set(v___x_650_, 1, v_x_606_);
v___y_622_ = v___x_650_;
goto v___jp_621_;
}
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_array_fset(v_xs_x27_620_, v_j_612_, v___y_622_);
lean_dec(v_j_612_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_623_);
v___x_625_ = v___x_616_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
else
{
lean_object* v_ks_653_; lean_object* v_vs_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_674_; 
v_ks_653_ = lean_ctor_get(v_x_602_, 0);
v_vs_654_ = lean_ctor_get(v_x_602_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_674_ == 0)
{
v___x_656_ = v_x_602_;
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_vs_654_);
lean_inc(v_ks_653_);
lean_dec(v_x_602_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_ks_653_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_vs_654_);
v___x_659_ = v_reuseFailAlloc_673_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v_newNode_660_; uint8_t v___y_662_; size_t v___x_668_; uint8_t v___x_669_; 
v_newNode_660_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_659_, v_x_605_, v_x_606_);
v___x_668_ = ((size_t)7ULL);
v___x_669_ = lean_usize_dec_le(v___x_668_, v_x_604_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_660_);
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
lean_dec(v___x_670_);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___x_669_;
goto v___jp_661_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v_ks_663_; lean_object* v_vs_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_ks_663_ = lean_ctor_get(v_newNode_660_, 0);
lean_inc_ref(v_ks_663_);
v_vs_664_ = lean_ctor_get(v_newNode_660_, 1);
lean_inc_ref(v_vs_664_);
lean_dec_ref(v_newNode_660_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_604_, v_ks_663_, v_vs_664_, v___x_665_, v___x_666_);
lean_dec_ref(v_vs_664_);
lean_dec_ref(v_ks_663_);
return v___x_667_;
}
else
{
return v_newNode_660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_675_, lean_object* v_keys_676_, lean_object* v_vals_677_, lean_object* v_i_678_, lean_object* v_entries_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_array_get_size(v_keys_676_);
v___x_681_ = lean_nat_dec_lt(v_i_678_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec(v_i_678_);
return v_entries_679_;
}
else
{
lean_object* v_k_682_; lean_object* v_v_683_; uint64_t v___x_684_; size_t v_h_685_; size_t v___x_686_; lean_object* v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v_h_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_k_682_ = lean_array_fget_borrowed(v_keys_676_, v_i_678_);
v_v_683_ = lean_array_fget_borrowed(v_vals_677_, v_i_678_);
v___x_684_ = l_Lean_instHashableMVarId_hash(v_k_682_);
v_h_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = ((size_t)5ULL);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_sub(v_depth_675_, v___x_688_);
v___x_690_ = lean_usize_mul(v___x_686_, v___x_689_);
v_h_691_ = lean_usize_shift_right(v_h_685_, v___x_690_);
v___x_692_ = lean_nat_add(v_i_678_, v___x_687_);
lean_dec(v_i_678_);
lean_inc(v_v_683_);
lean_inc(v_k_682_);
v___x_693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_679_, v_h_691_, v_depth_675_, v_k_682_, v_v_683_);
v_i_678_ = v___x_692_;
v_entries_679_ = v___x_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_695_, lean_object* v_keys_696_, lean_object* v_vals_697_, lean_object* v_i_698_, lean_object* v_entries_699_){
_start:
{
size_t v_depth_boxed_700_; lean_object* v_res_701_; 
v_depth_boxed_700_ = lean_unbox_usize(v_depth_695_);
lean_dec(v_depth_695_);
v_res_701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_700_, v_keys_696_, v_vals_697_, v_i_698_, v_entries_699_);
lean_dec_ref(v_vals_697_);
lean_dec_ref(v_keys_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v_x_5113__boxed_707_; size_t v_x_5114__boxed_708_; lean_object* v_res_709_; 
v_x_5113__boxed_707_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_x_5114__boxed_708_ = lean_unbox_usize(v_x_704_);
lean_dec(v_x_704_);
v_res_709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_702_, v_x_5113__boxed_707_, v_x_5114__boxed_708_, v_x_705_, v_x_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint64_t v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_713_ = l_Lean_instHashableMVarId_hash(v_x_711_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_710_, v___x_714_, v___x_715_, v_x_711_, v_x_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_717_, lean_object* v_val_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; lean_object* v_mctx_722_; lean_object* v_cache_723_; lean_object* v_zetaDeltaFVarIds_724_; lean_object* v_postponed_725_; lean_object* v_diag_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_753_; 
v___x_721_ = lean_st_ref_take(v___y_719_);
v_mctx_722_ = lean_ctor_get(v___x_721_, 0);
v_cache_723_ = lean_ctor_get(v___x_721_, 1);
v_zetaDeltaFVarIds_724_ = lean_ctor_get(v___x_721_, 2);
v_postponed_725_ = lean_ctor_get(v___x_721_, 3);
v_diag_726_ = lean_ctor_get(v___x_721_, 4);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_753_ == 0)
{
v___x_728_ = v___x_721_;
v_isShared_729_ = v_isSharedCheck_753_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_diag_726_);
lean_inc(v_postponed_725_);
lean_inc(v_zetaDeltaFVarIds_724_);
lean_inc(v_cache_723_);
lean_inc(v_mctx_722_);
lean_dec(v___x_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_753_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_depth_730_; lean_object* v_levelAssignDepth_731_; lean_object* v_mvarCounter_732_; lean_object* v_lDepth_733_; lean_object* v_decls_734_; lean_object* v_userNames_735_; lean_object* v_lAssignment_736_; lean_object* v_eAssignment_737_; lean_object* v_dAssignment_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_752_; 
v_depth_730_ = lean_ctor_get(v_mctx_722_, 0);
v_levelAssignDepth_731_ = lean_ctor_get(v_mctx_722_, 1);
v_mvarCounter_732_ = lean_ctor_get(v_mctx_722_, 2);
v_lDepth_733_ = lean_ctor_get(v_mctx_722_, 3);
v_decls_734_ = lean_ctor_get(v_mctx_722_, 4);
v_userNames_735_ = lean_ctor_get(v_mctx_722_, 5);
v_lAssignment_736_ = lean_ctor_get(v_mctx_722_, 6);
v_eAssignment_737_ = lean_ctor_get(v_mctx_722_, 7);
v_dAssignment_738_ = lean_ctor_get(v_mctx_722_, 8);
v_isSharedCheck_752_ = !lean_is_exclusive(v_mctx_722_);
if (v_isSharedCheck_752_ == 0)
{
v___x_740_ = v_mctx_722_;
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_dAssignment_738_);
lean_inc(v_eAssignment_737_);
lean_inc(v_lAssignment_736_);
lean_inc(v_userNames_735_);
lean_inc(v_decls_734_);
lean_inc(v_lDepth_733_);
lean_inc(v_mvarCounter_732_);
lean_inc(v_levelAssignDepth_731_);
lean_inc(v_depth_730_);
lean_dec(v_mctx_722_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_737_, v_mvarId_717_, v_val_718_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 7, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_depth_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_levelAssignDepth_731_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_mvarCounter_732_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_lDepth_733_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_decls_734_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_userNames_735_);
lean_ctor_set(v_reuseFailAlloc_751_, 6, v_lAssignment_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 7, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 8, v_dAssignment_738_);
v___x_744_ = v_reuseFailAlloc_751_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_744_);
v___x_746_ = v___x_728_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_cache_723_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_zetaDeltaFVarIds_724_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_postponed_725_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_diag_726_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_st_ref_set(v___y_719_, v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_754_, lean_object* v_val_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_754_, v_val_755_, v___y_756_);
lean_dec(v___y_756_);
return v_res_758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_762_, lean_object* v___x_763_, lean_object* v_args_764_, uint8_t v_transparency_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
lean_inc(v___x_763_);
lean_inc(v_mvarId_762_);
v___x_771_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_762_, v___x_763_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v___x_771_);
lean_inc(v_mvarId_762_);
v___x_772_ = l_Lean_MVarId_getTag(v_mvarId_762_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
lean_inc(v_mvarId_762_);
v___x_774_ = l_Lean_MVarId_getType(v_mvarId_762_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_890_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_775_, v___y_767_);
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_890_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_890_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_890_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
v___x_782_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_764_, v_transparency_765_, v_a_777_, v___x_781_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___x_858_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v_a_783_);
v___x_858_ = l_Lean_Meta_isTypeCorrect(v_a_783_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; uint8_t v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = lean_unbox(v_a_859_);
lean_dec(v_a_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_783_);
v___x_862_ = l_Lean_indentExpr(v_a_783_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_inc(v_mvarId_762_);
v___x_865_ = l_Lean_Meta_throwTacticEx___redArg(v___x_763_, v_mvarId_762_, v___x_864_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec_ref(v___x_865_);
v___y_809_ = v___y_766_;
v___y_810_ = v___y_767_;
v___y_811_ = v___y_768_;
v___y_812_ = v___y_769_;
goto v___jp_808_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_783_);
lean_del_object(v___x_779_);
lean_dec(v_a_773_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v_mvarId_762_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
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
else
{
lean_dec(v___x_763_);
v___y_809_ = v___y_766_;
v___y_810_ = v___y_767_;
v___y_811_ = v___y_768_;
v___y_812_ = v___y_769_;
goto v___jp_808_;
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_783_);
lean_del_object(v___x_779_);
lean_dec(v_a_773_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v___x_763_);
lean_dec(v_mvarId_762_);
v_a_874_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_858_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_858_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
v___jp_784_:
{
lean_object* v___x_792_; 
lean_inc_ref(v___y_789_);
v___x_792_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_783_, v_a_773_, v___y_789_, v___y_788_, v___y_790_, v___y_787_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_792_);
lean_inc(v_a_793_);
v___x_794_ = l_Lean_mkAppN(v_a_793_, v___y_786_);
lean_dec_ref(v___y_786_);
v___x_795_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_762_, v___x_794_, v___y_788_);
lean_dec_ref(v___x_795_);
v___x_796_ = 1;
v___x_797_ = l_Lean_Expr_mvarId_x21(v_a_793_);
lean_dec(v_a_793_);
v___x_798_ = lean_box(0);
v___x_799_ = l_Lean_Meta_introNCore(v___x_797_, v___y_785_, v___x_798_, v___y_791_, v___x_796_, v___y_789_, v___y_788_, v___y_790_, v___y_787_);
return v___x_799_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec(v_mvarId_762_);
v_a_800_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_792_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_792_);
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
v___jp_808_:
{
size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_sz_813_ = lean_array_size(v_args_764_);
v___x_814_ = ((size_t)0ULL);
lean_inc_ref(v_args_764_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_813_, v___x_814_, v_args_764_);
v___x_816_ = lean_array_get_size(v_args_764_);
v___x_817_ = lean_nat_dec_lt(v___x_781_, v___x_816_);
if (v___x_817_ == 0)
{
lean_del_object(v___x_779_);
lean_dec_ref(v_args_764_);
v___y_785_ = v___x_816_;
v___y_786_ = v___x_815_;
v___y_787_ = v___y_812_;
v___y_788_ = v___y_810_;
v___y_789_ = v___y_809_;
v___y_790_ = v___y_811_;
v___y_791_ = v___x_817_;
goto v___jp_784_;
}
else
{
if (v___x_817_ == 0)
{
lean_del_object(v___x_779_);
lean_dec_ref(v_args_764_);
v___y_785_ = v___x_816_;
v___y_786_ = v___x_815_;
v___y_787_ = v___y_812_;
v___y_788_ = v___y_810_;
v___y_789_ = v___y_809_;
v___y_790_ = v___y_811_;
v___y_791_ = v___x_817_;
goto v___jp_784_;
}
else
{
size_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_usize_of_nat(v___x_816_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_764_, v___x_814_, v___x_818_);
if (v___x_819_ == 0)
{
lean_del_object(v___x_779_);
lean_dec_ref(v_args_764_);
v___y_785_ = v___x_816_;
v___y_786_ = v___x_815_;
v___y_787_ = v___y_812_;
v___y_788_ = v___y_810_;
v___y_789_ = v___y_809_;
v___y_790_ = v___y_811_;
v___y_791_ = v___x_819_;
goto v___jp_784_;
}
else
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___f_823_; lean_object* v___x_825_; 
v___x_820_ = 0;
v___x_821_ = lean_box(v___x_820_);
v___x_822_ = lean_box(v___x_819_);
v___f_823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_823_, 0, v_args_764_);
lean_closure_set(v___f_823_, 1, v___x_781_);
lean_closure_set(v___f_823_, 2, v___x_821_);
lean_closure_set(v___f_823_, 3, v___x_822_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 1);
lean_ctor_set(v___x_779_, 0, v___x_816_);
v___x_825_ = v___x_779_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_816_);
v___x_825_ = v_reuseFailAlloc_857_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; 
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_826_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_783_, v___x_825_, v___f_823_, v___x_820_, v___x_820_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_fst_828_; lean_object* v_snd_829_; lean_object* v___x_830_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
v_fst_828_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_fst_828_);
v_snd_829_ = lean_ctor_get(v_a_827_, 1);
lean_inc(v_snd_829_);
lean_dec(v_a_827_);
lean_inc_ref(v___y_809_);
v___x_830_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_829_, v_a_773_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
lean_inc(v_a_831_);
v___x_832_ = l_Lean_mkAppN(v_a_831_, v___x_815_);
lean_dec_ref(v___x_815_);
lean_inc(v_fst_828_);
v___x_833_ = lean_array_mk(v_fst_828_);
v___x_834_ = l_Lean_mkAppN(v___x_832_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_835_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_762_, v___x_834_, v___y_810_);
lean_dec_ref(v___x_835_);
v___x_836_ = l_Lean_Expr_mvarId_x21(v_a_831_);
lean_dec(v_a_831_);
v___x_837_ = l_List_lengthTR___redArg(v_fst_828_);
lean_dec(v_fst_828_);
v___x_838_ = lean_nat_add(v___x_816_, v___x_837_);
lean_dec(v___x_837_);
v___x_839_ = lean_box(0);
v___x_840_ = l_Lean_Meta_introNCore(v___x_836_, v___x_838_, v___x_839_, v___x_820_, v___x_819_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_fst_828_);
lean_dec_ref(v___x_815_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v_mvarId_762_);
v_a_841_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_830_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_830_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_815_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v_a_773_);
lean_dec(v_mvarId_762_);
v_a_849_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_826_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_826_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
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
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_779_);
lean_dec(v_a_773_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v___x_763_);
lean_dec(v_mvarId_762_);
v_a_882_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_782_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_782_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_a_773_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v___x_763_);
lean_dec(v_mvarId_762_);
v_a_891_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_774_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_774_);
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
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v___x_763_);
lean_dec(v_mvarId_762_);
v_a_899_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_772_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_772_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v_args_764_);
lean_dec(v___x_763_);
lean_dec(v_mvarId_762_);
v_a_907_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_771_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_771_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_915_, lean_object* v___x_916_, lean_object* v_args_917_, lean_object* v_transparency_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v_transparency_boxed_924_; lean_object* v_res_925_; 
v_transparency_boxed_924_ = lean_unbox(v_transparency_918_);
v_res_925_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_915_, v___x_916_, v_args_917_, v_transparency_boxed_924_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_929_, lean_object* v_args_930_, uint8_t v_transparency_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_938_ = lean_box(v_transparency_931_);
lean_inc(v_mvarId_929_);
v___f_939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_939_, 0, v_mvarId_929_);
lean_closure_set(v___f_939_, 1, v___x_937_);
lean_closure_set(v___f_939_, 2, v_args_930_);
lean_closure_set(v___f_939_, 3, v___x_938_);
v___x_940_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_929_, v___f_939_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_941_, lean_object* v_args_942_, lean_object* v_transparency_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_transparency_boxed_949_; lean_object* v_res_950_; 
v_transparency_boxed_949_ = lean_unbox(v_transparency_943_);
v_res_950_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_941_, v_args_942_, v_transparency_boxed_949_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_951_, lean_object* v_val_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_951_, v_val_952_, v___y_954_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_959_, lean_object* v_val_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_959_, v_val_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_968_, v_x_969_, v_x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_972_, lean_object* v_x_973_, size_t v_x_974_, size_t v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_973_, v_x_974_, v_x_975_, v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
size_t v_x_5710__boxed_985_; size_t v_x_5711__boxed_986_; lean_object* v_res_987_; 
v_x_5710__boxed_985_ = lean_unbox_usize(v_x_981_);
lean_dec(v_x_981_);
v_x_5711__boxed_986_ = lean_unbox_usize(v_x_982_);
lean_dec(v_x_982_);
v_res_987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_979_, v_x_980_, v_x_5710__boxed_985_, v_x_5711__boxed_986_, v_x_983_, v_x_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_988_, lean_object* v_n_989_, lean_object* v_k_990_, lean_object* v_v_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_989_, v_k_990_, v_v_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_993_, size_t v_depth_994_, lean_object* v_keys_995_, lean_object* v_vals_996_, lean_object* v_heq_997_, lean_object* v_i_998_, lean_object* v_entries_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_994_, v_keys_995_, v_vals_996_, v_i_998_, v_entries_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1001_, lean_object* v_depth_1002_, lean_object* v_keys_1003_, lean_object* v_vals_1004_, lean_object* v_heq_1005_, lean_object* v_i_1006_, lean_object* v_entries_1007_){
_start:
{
size_t v_depth_boxed_1008_; lean_object* v_res_1009_; 
v_depth_boxed_1008_ = lean_unbox_usize(v_depth_1002_);
lean_dec(v_depth_1002_);
v_res_1009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_1001_, v_depth_boxed_1008_, v_keys_1003_, v_vals_1004_, v_heq_1005_, v_i_1006_, v_entries_1007_);
lean_dec_ref(v_vals_1004_);
lean_dec_ref(v_keys_1003_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_1011_, v_x_1012_, v_x_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_1016_, lean_object* v_args_1017_, uint8_t v_transparency_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1016_, v_args_1017_, v_transparency_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_1025_, lean_object* v_args_1026_, lean_object* v_transparency_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_transparency_boxed_1033_; lean_object* v_res_1034_; 
v_transparency_boxed_1033_ = lean_unbox(v_transparency_1027_);
v_res_1034_ = l_Lean_MVarId_generalize(v_mvarId_1025_, v_args_1026_, v_transparency_boxed_1033_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1035_, size_t v_sz_1036_, size_t v_i_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_lt(v_i_1037_, v_sz_1036_);
if (v___x_1039_ == 0)
{
return v_b_1038_;
}
else
{
lean_object* v_snd_1040_; lean_object* v_fst_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1074_; 
v_snd_1040_ = lean_ctor_get(v_b_1038_, 1);
v_fst_1041_ = lean_ctor_get(v_b_1038_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_b_1038_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1043_ = v_b_1038_;
v_isShared_1044_ = v_isSharedCheck_1074_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_snd_1040_);
lean_inc(v_fst_1041_);
lean_dec(v_b_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1074_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_array_1045_; lean_object* v_start_1046_; lean_object* v_stop_1047_; uint8_t v___x_1048_; 
v_array_1045_ = lean_ctor_get(v_snd_1040_, 0);
v_start_1046_ = lean_ctor_get(v_snd_1040_, 1);
v_stop_1047_ = lean_ctor_get(v_snd_1040_, 2);
v___x_1048_ = lean_nat_dec_lt(v_start_1046_, v_stop_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1050_; 
if (v_isShared_1044_ == 0)
{
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fst_1041_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_snd_1040_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1070_; 
lean_inc(v_stop_1047_);
lean_inc(v_start_1046_);
lean_inc_ref(v_array_1045_);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_snd_1040_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1071_ = lean_ctor_get(v_snd_1040_, 2);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_snd_1040_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_snd_1040_, 0);
lean_dec(v_unused_1073_);
v___x_1053_ = v_snd_1040_;
v_isShared_1054_ = v_isSharedCheck_1070_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v_snd_1040_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1070_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v_a_1055_ = lean_array_uget_borrowed(v_as_1035_, v_i_1037_);
v___x_1056_ = lean_array_fget(v_array_1045_, v_start_1046_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_start_1046_, v___x_1057_);
lean_dec(v_start_1046_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1058_);
v___x_1060_ = v___x_1053_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_array_1045_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_stop_1047_);
v___x_1060_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1061_ = l_Lean_mkFVar(v___x_1056_);
lean_inc(v_a_1055_);
v___x_1062_ = l_Lean_Meta_FVarSubst_insert(v_fst_1041_, v_a_1055_, v___x_1061_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1060_);
lean_ctor_set(v___x_1043_, 0, v___x_1062_);
v___x_1064_ = v___x_1043_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1060_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
size_t v___x_1065_; size_t v___x_1066_; 
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1037_, v___x_1065_);
v_i_1037_ = v___x_1066_;
v_b_1038_ = v___x_1064_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1075_, lean_object* v_sz_1076_, lean_object* v_i_1077_, lean_object* v_b_1078_){
_start:
{
size_t v_sz_boxed_1079_; size_t v_i_boxed_1080_; lean_object* v_res_1081_; 
v_sz_boxed_1079_ = lean_unbox_usize(v_sz_1076_);
lean_dec(v_sz_1076_);
v_i_boxed_1080_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1075_, v_sz_boxed_1079_, v_i_boxed_1080_, v_b_1078_);
lean_dec_ref(v_as_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1082_, size_t v_i_1083_, lean_object* v_bs_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1083_, v_sz_1082_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_bs_1084_);
return v___x_1088_;
}
else
{
lean_object* v_v_1089_; lean_object* v_expr_1090_; lean_object* v_xName_x3f_1091_; lean_object* v_hName_x3f_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1115_; 
v_v_1089_ = lean_array_uget(v_bs_1084_, v_i_1083_);
v_expr_1090_ = lean_ctor_get(v_v_1089_, 0);
v_xName_x3f_1091_ = lean_ctor_get(v_v_1089_, 1);
v_hName_x3f_1092_ = lean_ctor_get(v_v_1089_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_v_1089_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1094_ = v_v_1089_;
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_hName_x3f_1092_);
lean_inc(v_xName_x3f_1091_);
lean_inc(v_expr_1090_);
lean_dec(v_v_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1115_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1090_, v___y_1085_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v_bs_x27_1099_; lean_object* v___x_1101_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v_bs_x27_1099_ = lean_array_uset(v_bs_1084_, v_i_1083_, v___x_1098_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_a_1097_);
v___x_1101_ = v___x_1094_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1097_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_xName_x3f_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_hName_x3f_1092_);
v___x_1101_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1083_, v___x_1102_);
v___x_1104_ = lean_array_uset(v_bs_x27_1099_, v_i_1083_, v___x_1101_);
v_i_1083_ = v___x_1103_;
v_bs_1084_ = v___x_1104_;
goto _start;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1094_);
lean_dec(v_hName_x3f_1092_);
lean_dec(v_xName_x3f_1091_);
lean_dec_ref(v_bs_1084_);
v_a_1107_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1096_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1096_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1116_, lean_object* v_i_1117_, lean_object* v_bs_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_sz_boxed_1121_; size_t v_i_boxed_1122_; lean_object* v_res_1123_; 
v_sz_boxed_1121_ = lean_unbox_usize(v_sz_1116_);
lean_dec(v_sz_1116_);
v_i_boxed_1122_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1121_, v_i_boxed_1122_, v_bs_1118_, v___y_1119_);
lean_dec(v___y_1119_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1124_, lean_object* v_a_1125_, lean_object* v_as_1126_, size_t v_i_1127_, size_t v_stop_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_eq(v_i_1127_, v_stop_1128_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v_expr_1136_; lean_object* v___x_1137_; uint8_t v_foApprox_1138_; uint8_t v_ctxApprox_1139_; uint8_t v_quasiPatternApprox_1140_; uint8_t v_constApprox_1141_; uint8_t v_isDefEqStuckEx_1142_; uint8_t v_unificationHints_1143_; uint8_t v_proofIrrelevance_1144_; uint8_t v_assignSyntheticOpaque_1145_; uint8_t v_offsetCnstrs_1146_; uint8_t v_etaStruct_1147_; uint8_t v_univApprox_1148_; uint8_t v_iota_1149_; uint8_t v_beta_1150_; uint8_t v_proj_1151_; uint8_t v_zeta_1152_; uint8_t v_zetaDelta_1153_; uint8_t v_zetaUnused_1154_; uint8_t v_zetaHave_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1203_; 
v___x_1135_ = lean_array_uget_borrowed(v_as_1126_, v_i_1127_);
v_expr_1136_ = lean_ctor_get(v___x_1135_, 0);
v___x_1137_ = l_Lean_Meta_Context_config(v___y_1129_);
v_foApprox_1138_ = lean_ctor_get_uint8(v___x_1137_, 0);
v_ctxApprox_1139_ = lean_ctor_get_uint8(v___x_1137_, 1);
v_quasiPatternApprox_1140_ = lean_ctor_get_uint8(v___x_1137_, 2);
v_constApprox_1141_ = lean_ctor_get_uint8(v___x_1137_, 3);
v_isDefEqStuckEx_1142_ = lean_ctor_get_uint8(v___x_1137_, 4);
v_unificationHints_1143_ = lean_ctor_get_uint8(v___x_1137_, 5);
v_proofIrrelevance_1144_ = lean_ctor_get_uint8(v___x_1137_, 6);
v_assignSyntheticOpaque_1145_ = lean_ctor_get_uint8(v___x_1137_, 7);
v_offsetCnstrs_1146_ = lean_ctor_get_uint8(v___x_1137_, 8);
v_etaStruct_1147_ = lean_ctor_get_uint8(v___x_1137_, 10);
v_univApprox_1148_ = lean_ctor_get_uint8(v___x_1137_, 11);
v_iota_1149_ = lean_ctor_get_uint8(v___x_1137_, 12);
v_beta_1150_ = lean_ctor_get_uint8(v___x_1137_, 13);
v_proj_1151_ = lean_ctor_get_uint8(v___x_1137_, 14);
v_zeta_1152_ = lean_ctor_get_uint8(v___x_1137_, 15);
v_zetaDelta_1153_ = lean_ctor_get_uint8(v___x_1137_, 16);
v_zetaUnused_1154_ = lean_ctor_get_uint8(v___x_1137_, 17);
v_zetaHave_1155_ = lean_ctor_get_uint8(v___x_1137_, 18);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1157_ = v___x_1137_;
v_isShared_1158_ = v_isSharedCheck_1203_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v___x_1137_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1203_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v_trackZetaDelta_1159_; lean_object* v_zetaDeltaSet_1160_; lean_object* v_lctx_1161_; lean_object* v_localInstances_1162_; lean_object* v_defEqCtx_x3f_1163_; lean_object* v_synthPendingDepth_1164_; lean_object* v_canUnfold_x3f_1165_; uint8_t v_univApprox_1166_; uint8_t v_inTypeClassResolution_1167_; uint8_t v_cacheInferType_1168_; lean_object* v_config_1170_; 
v_trackZetaDelta_1159_ = lean_ctor_get_uint8(v___y_1129_, sizeof(void*)*7);
v_zetaDeltaSet_1160_ = lean_ctor_get(v___y_1129_, 1);
v_lctx_1161_ = lean_ctor_get(v___y_1129_, 2);
v_localInstances_1162_ = lean_ctor_get(v___y_1129_, 3);
v_defEqCtx_x3f_1163_ = lean_ctor_get(v___y_1129_, 4);
v_synthPendingDepth_1164_ = lean_ctor_get(v___y_1129_, 5);
v_canUnfold_x3f_1165_ = lean_ctor_get(v___y_1129_, 6);
v_univApprox_1166_ = lean_ctor_get_uint8(v___y_1129_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1167_ = lean_ctor_get_uint8(v___y_1129_, sizeof(void*)*7 + 2);
v_cacheInferType_1168_ = lean_ctor_get_uint8(v___y_1129_, sizeof(void*)*7 + 3);
if (v_isShared_1158_ == 0)
{
v_config_1170_ = v___x_1157_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 0, v_foApprox_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 1, v_ctxApprox_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 2, v_quasiPatternApprox_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 3, v_constApprox_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 4, v_isDefEqStuckEx_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 5, v_unificationHints_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 6, v_proofIrrelevance_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 7, v_assignSyntheticOpaque_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 8, v_offsetCnstrs_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 10, v_etaStruct_1147_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 11, v_univApprox_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 12, v_iota_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 13, v_beta_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 14, v_proj_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 15, v_zeta_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 16, v_zetaDelta_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 17, v_zetaUnused_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, 18, v_zetaHave_1155_);
v_config_1170_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; lean_object* v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; uint64_t v_key_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_ctor_set_uint8(v_config_1170_, 9, v_transparency_1124_);
v___x_1171_ = l_Lean_Meta_Context_configKey(v___y_1129_);
v___x_1172_ = 2ULL;
v___x_1173_ = lean_uint64_shift_right(v___x_1171_, v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_uint64_shift_left(v___x_1173_, v___x_1172_);
v___x_1176_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1124_);
v_key_1177_ = lean_uint64_lor(v___x_1175_, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1178_, 0, v_config_1170_);
lean_ctor_set_uint64(v___x_1178_, sizeof(void*)*1, v_key_1177_);
lean_inc(v_canUnfold_x3f_1165_);
lean_inc(v_synthPendingDepth_1164_);
lean_inc(v_defEqCtx_x3f_1163_);
lean_inc_ref(v_localInstances_1162_);
lean_inc_ref(v_lctx_1161_);
lean_inc(v_zetaDeltaSet_1160_);
v___x_1179_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_zetaDeltaSet_1160_);
lean_ctor_set(v___x_1179_, 2, v_lctx_1161_);
lean_ctor_set(v___x_1179_, 3, v_localInstances_1162_);
lean_ctor_set(v___x_1179_, 4, v_defEqCtx_x3f_1163_);
lean_ctor_set(v___x_1179_, 5, v_synthPendingDepth_1164_);
lean_ctor_set(v___x_1179_, 6, v_canUnfold_x3f_1165_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*7, v_trackZetaDelta_1159_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*7 + 1, v_univApprox_1166_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1167_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*7 + 3, v_cacheInferType_1168_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v_expr_1136_);
lean_inc_ref(v_a_1125_);
v___x_1180_ = l_Lean_Meta_kabstract(v_a_1125_, v_expr_1136_, v___x_1174_, v___x_1179_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1193_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_Expr_hasLooseBVars(v_a_1181_);
lean_dec(v_a_1181_);
if (v___x_1185_ == 0)
{
size_t v___x_1186_; size_t v___x_1187_; 
lean_del_object(v___x_1183_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1127_, v___x_1186_);
v_i_1127_ = v___x_1187_;
goto _start;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v_a_1125_);
v___x_1189_ = lean_box(v___x_1185_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1189_);
v___x_1191_ = v___x_1183_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v_a_1125_);
v_a_1194_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1180_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1180_);
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
uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v_a_1125_);
v___x_1204_ = 0;
v___x_1205_ = lean_box(v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1207_, lean_object* v_a_1208_, lean_object* v_as_1209_, lean_object* v_i_1210_, lean_object* v_stop_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v_transparency_boxed_1217_; size_t v_i_boxed_1218_; size_t v_stop_boxed_1219_; lean_object* v_res_1220_; 
v_transparency_boxed_1217_ = lean_unbox(v_transparency_1207_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_stop_boxed_1219_ = lean_unbox_usize(v_stop_1211_);
lean_dec(v_stop_1211_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1217_, v_a_1208_, v_as_1209_, v_i_boxed_1218_, v_stop_boxed_1219_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_as_1209_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1221_, lean_object* v___x_1222_, uint8_t v_transparency_1223_, lean_object* v_as_1224_, size_t v_i_1225_, size_t v_stop_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_a_1234_; uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_eq(v_i_1225_, v_stop_1226_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v_a_1241_; lean_object* v___x_1243_; 
v___x_1239_ = lean_array_uget_borrowed(v_as_1224_, v_i_1225_);
lean_inc_ref(v___y_1228_);
lean_inc(v___x_1239_);
v___x_1243_ = l_Lean_FVarId_getType___redArg(v___x_1239_, v___y_1228_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1244_, v___y_1229_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_nat_dec_eq(v___x_1222_, v___x_1247_);
v___x_1249_ = lean_array_get_size(v_a_1221_);
v___x_1250_ = lean_nat_dec_lt(v___x_1247_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_a_1246_);
v_a_1241_ = v___x_1248_;
goto v___jp_1240_;
}
else
{
if (v___x_1250_ == 0)
{
lean_dec(v_a_1246_);
v_a_1241_ = v___x_1248_;
goto v___jp_1240_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = lean_usize_of_nat(v___x_1249_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1223_, v_a_1246_, v_a_1221_, v___x_1251_, v___x_1252_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; uint8_t v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
v_a_1241_ = v___x_1255_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_b_1227_);
v_a_1256_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1253_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1253_);
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
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_b_1227_);
v_a_1264_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1245_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1245_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_b_1227_);
v_a_1272_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1243_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1243_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
v___jp_1240_:
{
if (v_a_1241_ == 0)
{
v_a_1234_ = v_b_1227_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1242_; 
lean_inc(v___x_1239_);
v___x_1242_ = lean_array_push(v_b_1227_, v___x_1239_);
v_a_1234_ = v___x_1242_;
goto v___jp_1233_;
}
}
}
else
{
lean_object* v___x_1280_; 
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_b_1227_);
return v___x_1280_;
}
v___jp_1233_:
{
size_t v___x_1235_; size_t v___x_1236_; 
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_add(v_i_1225_, v___x_1235_);
v_i_1225_ = v___x_1236_;
v_b_1227_ = v_a_1234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1281_, lean_object* v___x_1282_, lean_object* v_transparency_1283_, lean_object* v_as_1284_, lean_object* v_i_1285_, lean_object* v_stop_1286_, lean_object* v_b_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v_transparency_boxed_1293_; size_t v_i_boxed_1294_; size_t v_stop_boxed_1295_; lean_object* v_res_1296_; 
v_transparency_boxed_1293_ = lean_unbox(v_transparency_1283_);
v_i_boxed_1294_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_stop_boxed_1295_ = lean_unbox_usize(v_stop_1286_);
lean_dec(v_stop_1286_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1281_, v___x_1282_, v_transparency_boxed_1293_, v_as_1284_, v_i_boxed_1294_, v_stop_boxed_1295_, v_b_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec_ref(v_as_1284_);
lean_dec(v___x_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1297_, lean_object* v_a_1298_, lean_object* v___x_1299_, lean_object* v_as_1300_, size_t v_i_1301_, size_t v_stop_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_a_1310_; uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_eq(v_i_1301_, v_stop_1302_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v_a_1317_; lean_object* v___x_1319_; 
v___x_1315_ = lean_array_uget_borrowed(v_as_1300_, v_i_1301_);
lean_inc_ref(v___y_1304_);
lean_inc(v___x_1315_);
v___x_1319_ = l_Lean_FVarId_getType___redArg(v___x_1315_, v___y_1304_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1320_, v___y_1305_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_nat_dec_eq(v___x_1299_, v___x_1323_);
v___x_1325_ = lean_array_get_size(v_a_1298_);
v___x_1326_ = lean_nat_dec_lt(v___x_1323_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v_a_1322_);
v_a_1317_ = v___x_1324_;
goto v___jp_1316_;
}
else
{
if (v___x_1326_ == 0)
{
lean_dec(v_a_1322_);
v_a_1317_ = v___x_1324_;
goto v___jp_1316_;
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1325_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1297_, v_a_1322_, v_a_1298_, v___x_1327_, v___x_1328_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; uint8_t v___x_1331_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
v_a_1317_ = v___x_1331_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_b_1303_);
v_a_1332_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1329_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1329_);
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
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_b_1303_);
v_a_1340_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1321_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1321_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_b_1303_);
v_a_1348_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1319_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1319_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
v___jp_1316_:
{
if (v_a_1317_ == 0)
{
v_a_1310_ = v_b_1303_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1318_; 
lean_inc(v___x_1315_);
v___x_1318_ = lean_array_push(v_b_1303_, v___x_1315_);
v_a_1310_ = v___x_1318_;
goto v___jp_1309_;
}
}
}
else
{
lean_object* v___x_1356_; 
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1303_);
return v___x_1356_;
}
v___jp_1309_:
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1301_, v___x_1311_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1298_, v___x_1299_, v_transparency_1297_, v_as_1300_, v___x_1312_, v_stop_1302_, v_a_1310_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1357_, lean_object* v_a_1358_, lean_object* v___x_1359_, lean_object* v_as_1360_, lean_object* v_i_1361_, lean_object* v_stop_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v_transparency_boxed_1369_; size_t v_i_boxed_1370_; size_t v_stop_boxed_1371_; lean_object* v_res_1372_; 
v_transparency_boxed_1369_ = lean_unbox(v_transparency_1357_);
v_i_boxed_1370_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_stop_boxed_1371_ = lean_unbox_usize(v_stop_1362_);
lean_dec(v_stop_1362_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1369_, v_a_1358_, v___x_1359_, v_as_1360_, v_i_boxed_1370_, v_stop_boxed_1371_, v_b_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec_ref(v_as_1360_);
lean_dec(v___x_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1375_, lean_object* v_args_1376_, lean_object* v_hyps_1377_, lean_object* v_fvarSubst_1378_, uint8_t v_transparency_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = lean_array_get_size(v_hyps_1377_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_nat_dec_eq(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v_sz_1388_ = lean_array_size(v_args_1376_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1388_, v___x_1389_, v_args_1376_, v_a_1381_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; uint8_t v___x_1392_; lean_object* v_a_1394_; lean_object* v___y_1468_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = 1;
v___x_1478_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1479_ = lean_nat_dec_lt(v___x_1386_, v___x_1385_);
if (v___x_1479_ == 0)
{
v_a_1394_ = v___x_1478_;
goto v___jp_1393_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_nat_dec_le(v___x_1385_, v___x_1385_);
if (v___x_1480_ == 0)
{
if (v___x_1479_ == 0)
{
v_a_1394_ = v___x_1478_;
goto v___jp_1393_;
}
else
{
size_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_usize_of_nat(v___x_1385_);
lean_inc(v_a_1383_);
lean_inc_ref(v_a_1382_);
lean_inc(v_a_1381_);
lean_inc_ref(v_a_1380_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1379_, v_a_1391_, v___x_1385_, v_hyps_1377_, v___x_1389_, v___x_1481_, v___x_1478_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
v___y_1468_ = v___x_1482_;
goto v___jp_1467_;
}
}
else
{
size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_usize_of_nat(v___x_1385_);
lean_inc(v_a_1383_);
lean_inc_ref(v_a_1382_);
lean_inc(v_a_1381_);
lean_inc_ref(v_a_1380_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1379_, v_a_1391_, v___x_1385_, v_hyps_1377_, v___x_1389_, v___x_1483_, v___x_1478_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
v___y_1468_ = v___x_1484_;
goto v___jp_1467_;
}
}
v___jp_1393_:
{
lean_object* v___x_1395_; 
lean_inc(v_a_1383_);
lean_inc_ref(v_a_1382_);
lean_inc(v_a_1381_);
lean_inc_ref(v_a_1380_);
v___x_1395_ = l_Lean_MVarId_revert(v_mvarId_1375_, v_a_1394_, v___x_1392_, v___x_1387_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
v_fst_1397_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_fst_1397_);
v_snd_1398_ = lean_ctor_get(v_a_1396_, 1);
lean_inc(v_snd_1398_);
lean_dec(v_a_1396_);
lean_inc(v_a_1383_);
lean_inc_ref(v_a_1382_);
lean_inc(v_a_1381_);
lean_inc_ref(v_a_1380_);
v___x_1399_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1398_, v_a_1391_, v_transparency_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1450_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1399_);
v_fst_1401_ = lean_ctor_get(v_a_1400_, 0);
v_snd_1402_ = lean_ctor_get(v_a_1400_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_a_1400_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1404_ = v_a_1400_;
v_isShared_1405_ = v_isSharedCheck_1450_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_a_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1450_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_array_get_size(v_fst_1397_);
v___x_1407_ = lean_box(0);
v___x_1408_ = l_Lean_Meta_introNCore(v_snd_1402_, v___x_1406_, v___x_1407_, v___x_1387_, v___x_1392_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1441_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1441_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1441_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1440_; 
v_fst_1413_ = lean_ctor_get(v_a_1409_, 0);
v_snd_1414_ = lean_ctor_get(v_a_1409_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1409_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1416_ = v_a_1409_;
v_isShared_1417_ = v_isSharedCheck_1440_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snd_1414_);
lean_inc(v_fst_1413_);
lean_dec(v_a_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1440_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_array_get_size(v_fst_1413_);
v___x_1419_ = l_Array_toSubarray___redArg(v_fst_1413_, v___x_1386_, v___x_1418_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1419_);
lean_ctor_set(v___x_1416_, 0, v_fvarSubst_1378_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_fvarSubst_1378_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
size_t v_sz_1422_; lean_object* v___x_1423_; lean_object* v_fst_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1437_; 
v_sz_1422_ = lean_array_size(v_fst_1397_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1397_, v_sz_1422_, v___x_1389_, v___x_1421_);
lean_dec(v_fst_1397_);
v_fst_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1423_, 1);
lean_dec(v_unused_1438_);
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1437_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_fst_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1437_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_snd_1414_);
lean_ctor_set(v___x_1426_, 0, v_fst_1401_);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_fst_1401_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_snd_1414_);
v___x_1429_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1429_);
lean_ctor_set(v___x_1404_, 0, v_fst_1424_);
v___x_1431_ = v___x_1404_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_fst_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1431_);
v___x_1433_ = v___x_1411_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
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
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1404_);
lean_dec(v_fst_1401_);
lean_dec(v_fst_1397_);
lean_dec(v_fvarSubst_1378_);
v_a_1442_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1408_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1408_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_fst_1397_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_fvarSubst_1378_);
v_a_1451_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1399_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1399_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_a_1391_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_fvarSubst_1378_);
v_a_1459_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1395_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1395_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
v___jp_1467_:
{
if (lean_obj_tag(v___y_1468_) == 0)
{
lean_object* v_a_1469_; 
v_a_1469_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___y_1468_);
v_a_1394_ = v_a_1469_;
goto v___jp_1393_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1391_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_fvarSubst_1378_);
lean_dec(v_mvarId_1375_);
v_a_1470_ = lean_ctor_get(v___y_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___y_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___y_1468_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___y_1468_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_fvarSubst_1378_);
lean_dec(v_mvarId_1375_);
v_a_1485_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1390_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1390_);
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
else
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1375_, v_args_1376_, v_transparency_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_fvarSubst_1378_);
lean_ctor_set(v___x_1498_, 1, v_a_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_fvarSubst_1378_);
v_a_1503_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1493_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1493_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1511_, lean_object* v_args_1512_, lean_object* v_hyps_1513_, lean_object* v_fvarSubst_1514_, lean_object* v_transparency_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
uint8_t v_transparency_boxed_1521_; lean_object* v_res_1522_; 
v_transparency_boxed_1521_ = lean_unbox(v_transparency_1515_);
v_res_1522_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1511_, v_args_1512_, v_hyps_1513_, v_fvarSubst_1514_, v_transparency_boxed_1521_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec_ref(v_hyps_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1523_, size_t v_i_1524_, lean_object* v_bs_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1523_, v_i_1524_, v_bs_1525_, v___y_1527_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_bs_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
size_t v_sz_boxed_1540_; size_t v_i_boxed_1541_; lean_object* v_res_1542_; 
v_sz_boxed_1540_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1541_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1540_, v_i_boxed_1541_, v_bs_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1542_;
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
