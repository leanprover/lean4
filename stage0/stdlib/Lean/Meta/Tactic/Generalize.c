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
lean_dec_ref(v___x_73_);
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
lean_dec_ref(v___x_147_);
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
v___x_124_ = 2ULL;
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
lean_dec_ref(v___x_131_);
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
lean_dec_ref(v___x_218_);
lean_inc_ref(v_expr_185_);
v___x_220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_185_, v_a_173_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_n(v_a_221_, 2);
lean_dec_ref(v___x_220_);
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
lean_dec_ref(v___x_222_);
v___x_224_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_223_, v_a_173_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
v___x_226_ = l_Lean_Meta_isExprDefEq(v_a_219_, v_a_225_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; uint8_t v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
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
lean_dec_ref(v___x_229_);
v___x_231_ = l_Lean_Meta_mkHEqRefl(v_a_221_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
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
lean_dec_ref(v___x_249_);
v___x_251_ = l_Lean_Meta_mkEqRefl(v_a_221_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref(v___x_251_);
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
lean_dec_ref(v___x_468_);
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
uint8_t v___x_4822__boxed_508_; uint8_t v___x_4823__boxed_509_; lean_object* v_res_510_; 
v___x_4822__boxed_508_ = lean_unbox(v___x_499_);
v___x_4823__boxed_509_ = lean_unbox(v___x_500_);
v_res_510_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_497_, v___x_498_, v___x_4822__boxed_508_, v___x_4823__boxed_509_, v_xs_501_, v_type_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; 
v___x_582_ = ((size_t)5ULL);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_shift_left(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_587_ = lean_usize_sub(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* v_x_589_, size_t v_x_590_, size_t v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_es_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_j_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_es_594_ = lean_ctor_get(v_x_589_, 0);
v___x_595_ = ((size_t)5ULL);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_598_ = lean_usize_land(v_x_590_, v___x_597_);
v_j_599_ = lean_usize_to_nat(v___x_598_);
v___x_600_ = lean_array_get_size(v_es_594_);
v___x_601_ = lean_nat_dec_lt(v_j_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_j_599_);
lean_dec(v_x_593_);
lean_dec(v_x_592_);
return v_x_589_;
}
else
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_638_; 
lean_inc_ref(v_es_594_);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_x_589_, 0);
lean_dec(v_unused_639_);
v___x_603_ = v_x_589_;
v_isShared_604_ = v_isSharedCheck_638_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_x_589_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_638_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_v_605_; lean_object* v___x_606_; lean_object* v_xs_x27_607_; lean_object* v___y_609_; 
v_v_605_ = lean_array_fget(v_es_594_, v_j_599_);
v___x_606_ = lean_box(0);
v_xs_x27_607_ = lean_array_fset(v_es_594_, v_j_599_, v___x_606_);
switch(lean_obj_tag(v_v_605_))
{
case 0:
{
lean_object* v_key_614_; lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_625_; 
v_key_614_ = lean_ctor_get(v_v_605_, 0);
v_val_615_ = lean_ctor_get(v_v_605_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_625_ == 0)
{
v___x_617_ = v_v_605_;
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_inc(v_key_614_);
lean_dec(v_v_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = l_Lean_instBEqMVarId_beq(v_x_592_, v_key_614_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_del_object(v___x_617_);
v___x_620_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_614_, v_val_615_, v_x_592_, v_x_593_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___y_609_ = v___x_621_;
goto v___jp_608_;
}
else
{
lean_object* v___x_623_; 
lean_dec(v_val_615_);
lean_dec(v_key_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v_x_593_);
lean_ctor_set(v___x_617_, 0, v_x_592_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_x_592_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_x_593_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
}
}
}
case 1:
{
lean_object* v_node_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
v_node_626_ = lean_ctor_get(v_v_605_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_636_ == 0)
{
v___x_628_ = v_v_605_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_node_626_);
lean_dec(v_v_605_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_630_ = lean_usize_shift_right(v_x_590_, v___x_595_);
v___x_631_ = lean_usize_add(v_x_591_, v___x_596_);
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_node_626_, v___x_630_, v___x_631_, v_x_592_, v_x_593_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_634_ = v___x_628_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v___y_609_ = v___x_634_;
goto v___jp_608_;
}
}
}
default: 
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_x_592_);
lean_ctor_set(v___x_637_, 1, v_x_593_);
v___y_609_ = v___x_637_;
goto v___jp_608_;
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_array_fset(v_xs_x27_607_, v_j_599_, v___y_609_);
lean_dec(v_j_599_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_610_);
v___x_612_ = v___x_603_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_object* v_ks_640_; lean_object* v_vs_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_661_; 
v_ks_640_ = lean_ctor_get(v_x_589_, 0);
v_vs_641_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_661_ == 0)
{
v___x_643_ = v_x_589_;
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_vs_641_);
lean_inc(v_ks_640_);
lean_dec(v_x_589_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_ks_640_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_vs_641_);
v___x_646_ = v_reuseFailAlloc_660_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v_newNode_647_; uint8_t v___y_649_; size_t v___x_655_; uint8_t v___x_656_; 
v_newNode_647_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v___x_646_, v_x_592_, v_x_593_);
v___x_655_ = ((size_t)7ULL);
v___x_656_ = lean_usize_dec_le(v___x_655_, v_x_591_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_647_);
v___x_658_ = lean_unsigned_to_nat(4u);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
v___y_649_ = v___x_659_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___x_656_;
goto v___jp_648_;
}
v___jp_648_:
{
if (v___y_649_ == 0)
{
lean_object* v_ks_650_; lean_object* v_vs_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_ks_650_ = lean_ctor_get(v_newNode_647_, 0);
lean_inc_ref(v_ks_650_);
v_vs_651_ = lean_ctor_get(v_newNode_647_, 1);
lean_inc_ref(v_vs_651_);
lean_dec_ref(v_newNode_647_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_x_591_, v_ks_650_, v_vs_651_, v___x_652_, v___x_653_);
lean_dec_ref(v_vs_651_);
lean_dec_ref(v_ks_650_);
return v___x_654_;
}
else
{
return v_newNode_647_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t v_depth_662_, lean_object* v_keys_663_, lean_object* v_vals_664_, lean_object* v_i_665_, lean_object* v_entries_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_array_get_size(v_keys_663_);
v___x_668_ = lean_nat_dec_lt(v_i_665_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_i_665_);
return v_entries_666_;
}
else
{
lean_object* v_k_669_; lean_object* v_v_670_; uint64_t v___x_671_; size_t v_h_672_; size_t v___x_673_; lean_object* v___x_674_; size_t v___x_675_; size_t v___x_676_; size_t v___x_677_; size_t v_h_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_k_669_ = lean_array_fget_borrowed(v_keys_663_, v_i_665_);
v_v_670_ = lean_array_fget_borrowed(v_vals_664_, v_i_665_);
v___x_671_ = l_Lean_instHashableMVarId_hash(v_k_669_);
v_h_672_ = lean_uint64_to_usize(v___x_671_);
v___x_673_ = ((size_t)5ULL);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_sub(v_depth_662_, v___x_675_);
v___x_677_ = lean_usize_mul(v___x_673_, v___x_676_);
v_h_678_ = lean_usize_shift_right(v_h_672_, v___x_677_);
v___x_679_ = lean_nat_add(v_i_665_, v___x_674_);
lean_dec(v_i_665_);
lean_inc(v_v_670_);
lean_inc(v_k_669_);
v___x_680_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_entries_666_, v_h_678_, v_depth_662_, v_k_669_, v_v_670_);
v_i_665_ = v___x_679_;
v_entries_666_ = v___x_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_depth_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_i_685_, lean_object* v_entries_686_){
_start:
{
size_t v_depth_boxed_687_; lean_object* v_res_688_; 
v_depth_boxed_687_ = lean_unbox_usize(v_depth_682_);
lean_dec(v_depth_682_);
v_res_688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_boxed_687_, v_keys_683_, v_vals_684_, v_i_685_, v_entries_686_);
lean_dec_ref(v_vals_684_);
lean_dec_ref(v_keys_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
size_t v_x_5020__boxed_694_; size_t v_x_5021__boxed_695_; lean_object* v_res_696_; 
v_x_5020__boxed_694_ = lean_unbox_usize(v_x_690_);
lean_dec(v_x_690_);
v_x_5021__boxed_695_ = lean_unbox_usize(v_x_691_);
lean_dec(v_x_691_);
v_res_696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_689_, v_x_5020__boxed_694_, v_x_5021__boxed_695_, v_x_692_, v_x_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
uint64_t v___x_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_700_ = l_Lean_instHashableMVarId_hash(v_x_698_);
v___x_701_ = lean_uint64_to_usize(v___x_700_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_697_, v___x_701_, v___x_702_, v_x_698_, v_x_699_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* v_mvarId_704_, lean_object* v_val_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v_mctx_709_; lean_object* v_cache_710_; lean_object* v_zetaDeltaFVarIds_711_; lean_object* v_postponed_712_; lean_object* v_diag_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_741_; 
v___x_708_ = lean_st_ref_take(v___y_706_);
v_mctx_709_ = lean_ctor_get(v___x_708_, 0);
v_cache_710_ = lean_ctor_get(v___x_708_, 1);
v_zetaDeltaFVarIds_711_ = lean_ctor_get(v___x_708_, 2);
v_postponed_712_ = lean_ctor_get(v___x_708_, 3);
v_diag_713_ = lean_ctor_get(v___x_708_, 4);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_741_ == 0)
{
v___x_715_ = v___x_708_;
v_isShared_716_ = v_isSharedCheck_741_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_diag_713_);
lean_inc(v_postponed_712_);
lean_inc(v_zetaDeltaFVarIds_711_);
lean_inc(v_cache_710_);
lean_inc(v_mctx_709_);
lean_dec(v___x_708_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_741_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_depth_717_; lean_object* v_levelAssignDepth_718_; lean_object* v_lmvarCounter_719_; lean_object* v_mvarCounter_720_; lean_object* v_lDecls_721_; lean_object* v_decls_722_; lean_object* v_userNames_723_; lean_object* v_lAssignment_724_; lean_object* v_eAssignment_725_; lean_object* v_dAssignment_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_740_; 
v_depth_717_ = lean_ctor_get(v_mctx_709_, 0);
v_levelAssignDepth_718_ = lean_ctor_get(v_mctx_709_, 1);
v_lmvarCounter_719_ = lean_ctor_get(v_mctx_709_, 2);
v_mvarCounter_720_ = lean_ctor_get(v_mctx_709_, 3);
v_lDecls_721_ = lean_ctor_get(v_mctx_709_, 4);
v_decls_722_ = lean_ctor_get(v_mctx_709_, 5);
v_userNames_723_ = lean_ctor_get(v_mctx_709_, 6);
v_lAssignment_724_ = lean_ctor_get(v_mctx_709_, 7);
v_eAssignment_725_ = lean_ctor_get(v_mctx_709_, 8);
v_dAssignment_726_ = lean_ctor_get(v_mctx_709_, 9);
v_isSharedCheck_740_ = !lean_is_exclusive(v_mctx_709_);
if (v_isSharedCheck_740_ == 0)
{
v___x_728_ = v_mctx_709_;
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_dAssignment_726_);
lean_inc(v_eAssignment_725_);
lean_inc(v_lAssignment_724_);
lean_inc(v_userNames_723_);
lean_inc(v_decls_722_);
lean_inc(v_lDecls_721_);
lean_inc(v_mvarCounter_720_);
lean_inc(v_lmvarCounter_719_);
lean_inc(v_levelAssignDepth_718_);
lean_inc(v_depth_717_);
lean_dec(v_mctx_709_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_740_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_725_, v_mvarId_704_, v_val_705_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 8, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_depth_717_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_levelAssignDepth_718_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_lmvarCounter_719_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_mvarCounter_720_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_lDecls_721_);
lean_ctor_set(v_reuseFailAlloc_739_, 5, v_decls_722_);
lean_ctor_set(v_reuseFailAlloc_739_, 6, v_userNames_723_);
lean_ctor_set(v_reuseFailAlloc_739_, 7, v_lAssignment_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 8, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_739_, 9, v_dAssignment_726_);
v___x_732_ = v_reuseFailAlloc_739_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_732_);
v___x_734_ = v___x_715_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_cache_710_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_zetaDeltaFVarIds_711_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_postponed_712_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_diag_713_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_st_ref_set(v___y_706_, v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_742_, lean_object* v_val_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_742_, v_val_743_, v___y_744_);
lean_dec(v___y_744_);
return v_res_746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_750_, lean_object* v___x_751_, lean_object* v_args_752_, uint8_t v_transparency_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
lean_inc(v___x_751_);
lean_inc(v_mvarId_750_);
v___x_759_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_750_, v___x_751_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v___x_759_);
lean_inc(v_mvarId_750_);
v___x_760_ = l_Lean_MVarId_getTag(v_mvarId_750_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v___x_760_);
lean_inc(v_mvarId_750_);
v___x_762_ = l_Lean_MVarId_getType(v_mvarId_750_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_878_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
v___x_764_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_763_, v___y_755_);
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_878_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_878_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_878_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_752_, v_transparency_753_, v_a_765_, v___x_769_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___x_846_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_n(v_a_771_, 2);
lean_dec_ref(v___x_770_);
v___x_846_ = l_Lean_Meta_isTypeCorrect(v_a_771_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; uint8_t v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_771_);
v___x_850_ = l_Lean_indentExpr(v_a_771_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_inc(v_mvarId_750_);
v___x_853_ = l_Lean_Meta_throwTacticEx___redArg(v___x_751_, v_mvarId_750_, v___x_852_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec_ref(v___x_853_);
v___y_797_ = v___y_754_;
v___y_798_ = v___y_755_;
v___y_799_ = v___y_756_;
v___y_800_ = v___y_757_;
goto v___jp_796_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_771_);
lean_del_object(v___x_767_);
lean_dec(v_a_761_);
lean_dec_ref(v_args_752_);
lean_dec(v_mvarId_750_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_dec(v___x_751_);
v___y_797_ = v___y_754_;
v___y_798_ = v___y_755_;
v___y_799_ = v___y_756_;
v___y_800_ = v___y_757_;
goto v___jp_796_;
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_771_);
lean_del_object(v___x_767_);
lean_dec(v_a_761_);
lean_dec_ref(v_args_752_);
lean_dec(v___x_751_);
lean_dec(v_mvarId_750_);
v_a_862_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_846_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_846_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
v___jp_772_:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_771_, v_a_761_, v___y_774_, v___y_778_, v___y_777_, v___y_775_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_n(v_a_781_, 2);
lean_dec_ref(v___x_780_);
v___x_782_ = l_Lean_mkAppN(v_a_781_, v___y_773_);
lean_dec_ref(v___y_773_);
v___x_783_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_750_, v___x_782_, v___y_778_);
lean_dec_ref(v___x_783_);
v___x_784_ = 1;
v___x_785_ = l_Lean_Expr_mvarId_x21(v_a_781_);
lean_dec(v_a_781_);
v___x_786_ = lean_box(0);
v___x_787_ = l_Lean_Meta_introNCore(v___x_785_, v___y_776_, v___x_786_, v___y_779_, v___x_784_, v___y_774_, v___y_778_, v___y_777_, v___y_775_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v___y_776_);
lean_dec_ref(v___y_773_);
lean_dec(v_mvarId_750_);
v_a_788_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_780_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_780_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
v___jp_796_:
{
size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_sz_801_ = lean_array_size(v_args_752_);
v___x_802_ = ((size_t)0ULL);
lean_inc_ref(v_args_752_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_801_, v___x_802_, v_args_752_);
v___x_804_ = lean_array_get_size(v_args_752_);
v___x_805_ = lean_nat_dec_lt(v___x_769_, v___x_804_);
if (v___x_805_ == 0)
{
lean_del_object(v___x_767_);
lean_dec_ref(v_args_752_);
v___y_773_ = v___x_803_;
v___y_774_ = v___y_797_;
v___y_775_ = v___y_800_;
v___y_776_ = v___x_804_;
v___y_777_ = v___y_799_;
v___y_778_ = v___y_798_;
v___y_779_ = v___x_805_;
goto v___jp_772_;
}
else
{
if (v___x_805_ == 0)
{
lean_del_object(v___x_767_);
lean_dec_ref(v_args_752_);
v___y_773_ = v___x_803_;
v___y_774_ = v___y_797_;
v___y_775_ = v___y_800_;
v___y_776_ = v___x_804_;
v___y_777_ = v___y_799_;
v___y_778_ = v___y_798_;
v___y_779_ = v___x_805_;
goto v___jp_772_;
}
else
{
size_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_usize_of_nat(v___x_804_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_752_, v___x_802_, v___x_806_);
if (v___x_807_ == 0)
{
lean_del_object(v___x_767_);
lean_dec_ref(v_args_752_);
v___y_773_ = v___x_803_;
v___y_774_ = v___y_797_;
v___y_775_ = v___y_800_;
v___y_776_ = v___x_804_;
v___y_777_ = v___y_799_;
v___y_778_ = v___y_798_;
v___y_779_ = v___x_807_;
goto v___jp_772_;
}
else
{
uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_813_; 
v___x_808_ = 0;
v___x_809_ = lean_box(v___x_808_);
v___x_810_ = lean_box(v___x_807_);
v___f_811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_811_, 0, v_args_752_);
lean_closure_set(v___f_811_, 1, v___x_769_);
lean_closure_set(v___f_811_, 2, v___x_809_);
lean_closure_set(v___f_811_, 3, v___x_810_);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 1);
lean_ctor_set(v___x_767_, 0, v___x_804_);
v___x_813_ = v___x_767_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_804_);
v___x_813_ = v_reuseFailAlloc_845_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_771_, v___x_813_, v___f_811_, v___x_808_, v___x_808_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_818_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_fst_816_);
v_snd_817_ = lean_ctor_get(v_a_815_, 1);
lean_inc(v_snd_817_);
lean_dec(v_a_815_);
v___x_818_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_817_, v_a_761_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_n(v_a_819_, 2);
lean_dec_ref(v___x_818_);
v___x_820_ = l_Lean_mkAppN(v_a_819_, v___x_803_);
lean_dec_ref(v___x_803_);
lean_inc(v_fst_816_);
v___x_821_ = lean_array_mk(v_fst_816_);
v___x_822_ = l_Lean_mkAppN(v___x_820_, v___x_821_);
lean_dec_ref(v___x_821_);
v___x_823_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_750_, v___x_822_, v___y_798_);
lean_dec_ref(v___x_823_);
v___x_824_ = l_Lean_Expr_mvarId_x21(v_a_819_);
lean_dec(v_a_819_);
v___x_825_ = l_List_lengthTR___redArg(v_fst_816_);
lean_dec(v_fst_816_);
v___x_826_ = lean_nat_add(v___x_804_, v___x_825_);
lean_dec(v___x_825_);
v___x_827_ = lean_box(0);
v___x_828_ = l_Lean_Meta_introNCore(v___x_824_, v___x_826_, v___x_827_, v___x_808_, v___x_807_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_828_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_fst_816_);
lean_dec_ref(v___x_803_);
lean_dec(v_mvarId_750_);
v_a_829_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_818_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v___x_803_);
lean_dec(v_a_761_);
lean_dec(v_mvarId_750_);
v_a_837_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_814_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_814_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
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
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_del_object(v___x_767_);
lean_dec(v_a_761_);
lean_dec_ref(v_args_752_);
lean_dec(v___x_751_);
lean_dec(v_mvarId_750_);
v_a_870_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_770_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_770_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_761_);
lean_dec_ref(v_args_752_);
lean_dec(v___x_751_);
lean_dec(v_mvarId_750_);
v_a_879_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_762_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_762_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_args_752_);
lean_dec(v___x_751_);
lean_dec(v_mvarId_750_);
v_a_887_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_760_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_760_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_args_752_);
lean_dec(v___x_751_);
lean_dec(v_mvarId_750_);
v_a_895_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_759_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_759_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_903_, lean_object* v___x_904_, lean_object* v_args_905_, lean_object* v_transparency_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_transparency_boxed_912_; lean_object* v_res_913_; 
v_transparency_boxed_912_ = lean_unbox(v_transparency_906_);
v_res_913_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_903_, v___x_904_, v_args_905_, v_transparency_boxed_912_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_917_, lean_object* v_args_918_, uint8_t v_transparency_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_926_ = lean_box(v_transparency_919_);
lean_inc(v_mvarId_917_);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_927_, 0, v_mvarId_917_);
lean_closure_set(v___f_927_, 1, v___x_925_);
lean_closure_set(v___f_927_, 2, v_args_918_);
lean_closure_set(v___f_927_, 3, v___x_926_);
v___x_928_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_917_, v___f_927_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_929_, lean_object* v_args_930_, lean_object* v_transparency_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_transparency_boxed_937_; lean_object* v_res_938_; 
v_transparency_boxed_937_ = lean_unbox(v_transparency_931_);
v_res_938_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_929_, v_args_930_, v_transparency_boxed_937_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_939_, lean_object* v_val_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_939_, v_val_940_, v___y_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_947_, lean_object* v_val_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_947_, v_val_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_956_, v_x_957_, v_x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_960_, lean_object* v_x_961_, size_t v_x_962_, size_t v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_961_, v_x_962_, v_x_963_, v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
size_t v_x_5605__boxed_973_; size_t v_x_5606__boxed_974_; lean_object* v_res_975_; 
v_x_5605__boxed_973_ = lean_unbox_usize(v_x_969_);
lean_dec(v_x_969_);
v_x_5606__boxed_974_ = lean_unbox_usize(v_x_970_);
lean_dec(v_x_970_);
v_res_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_967_, v_x_968_, v_x_5605__boxed_973_, v_x_5606__boxed_974_, v_x_971_, v_x_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_976_, lean_object* v_n_977_, lean_object* v_k_978_, lean_object* v_v_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_977_, v_k_978_, v_v_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_981_, size_t v_depth_982_, lean_object* v_keys_983_, lean_object* v_vals_984_, lean_object* v_heq_985_, lean_object* v_i_986_, lean_object* v_entries_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_982_, v_keys_983_, v_vals_984_, v_i_986_, v_entries_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_989_, lean_object* v_depth_990_, lean_object* v_keys_991_, lean_object* v_vals_992_, lean_object* v_heq_993_, lean_object* v_i_994_, lean_object* v_entries_995_){
_start:
{
size_t v_depth_boxed_996_; lean_object* v_res_997_; 
v_depth_boxed_996_ = lean_unbox_usize(v_depth_990_);
lean_dec(v_depth_990_);
v_res_997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_989_, v_depth_boxed_996_, v_keys_991_, v_vals_992_, v_heq_993_, v_i_994_, v_entries_995_);
lean_dec_ref(v_vals_992_);
lean_dec_ref(v_keys_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_1004_, lean_object* v_args_1005_, uint8_t v_transparency_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1004_, v_args_1005_, v_transparency_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* v_mvarId_1013_, lean_object* v_args_1014_, lean_object* v_transparency_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_transparency_boxed_1021_; lean_object* v_res_1022_; 
v_transparency_boxed_1021_ = lean_unbox(v_transparency_1015_);
v_res_1022_ = l_Lean_MVarId_generalize(v_mvarId_1013_, v_args_1014_, v_transparency_boxed_1021_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1023_, size_t v_sz_1024_, size_t v_i_1025_, lean_object* v_b_1026_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_usize_dec_lt(v_i_1025_, v_sz_1024_);
if (v___x_1027_ == 0)
{
return v_b_1026_;
}
else
{
lean_object* v_snd_1028_; lean_object* v_fst_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1062_; 
v_snd_1028_ = lean_ctor_get(v_b_1026_, 1);
v_fst_1029_ = lean_ctor_get(v_b_1026_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_b_1026_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1031_ = v_b_1026_;
v_isShared_1032_ = v_isSharedCheck_1062_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1029_);
lean_dec(v_b_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1062_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_array_1033_; lean_object* v_start_1034_; lean_object* v_stop_1035_; uint8_t v___x_1036_; 
v_array_1033_ = lean_ctor_get(v_snd_1028_, 0);
v_start_1034_ = lean_ctor_get(v_snd_1028_, 1);
v_stop_1035_ = lean_ctor_get(v_snd_1028_, 2);
v___x_1036_ = lean_nat_dec_lt(v_start_1034_, v_stop_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1038_; 
if (v_isShared_1032_ == 0)
{
v___x_1038_ = v___x_1031_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_fst_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1028_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1058_; 
lean_inc(v_stop_1035_);
lean_inc(v_start_1034_);
lean_inc_ref(v_array_1033_);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_snd_1028_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1059_ = lean_ctor_get(v_snd_1028_, 2);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_snd_1028_, 1);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_snd_1028_, 0);
lean_dec(v_unused_1061_);
v___x_1041_ = v_snd_1028_;
v_isShared_1042_ = v_isSharedCheck_1058_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v_snd_1028_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1058_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v_a_1043_ = lean_array_uget_borrowed(v_as_1023_, v_i_1025_);
v___x_1044_ = lean_array_fget(v_array_1033_, v_start_1034_);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_start_1034_, v___x_1045_);
lean_dec(v_start_1034_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1046_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_array_1033_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_stop_1035_);
v___x_1048_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = l_Lean_mkFVar(v___x_1044_);
lean_inc(v_a_1043_);
v___x_1050_ = l_Lean_Meta_FVarSubst_insert(v_fst_1029_, v_a_1043_, v___x_1049_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1048_);
lean_ctor_set(v___x_1031_, 0, v___x_1050_);
v___x_1052_ = v___x_1031_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1048_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
size_t v___x_1053_; size_t v___x_1054_; 
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1025_, v___x_1053_);
v_i_1025_ = v___x_1054_;
v_b_1026_ = v___x_1052_;
goto _start;
}
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_bs_1072_, lean_object* v___y_1073_){
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
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1078_, v___y_1073_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v_bs_x27_1087_; lean_object* v___x_1089_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v_bs_x27_1087_ = lean_array_uset(v_bs_1072_, v_i_1071_, v___x_1086_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_a_1085_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1085_);
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
v___x_1092_ = lean_array_uset(v_bs_x27_1087_, v_i_1071_, v___x_1089_);
v_i_1071_ = v___x_1091_;
v_bs_1072_ = v___x_1092_;
goto _start;
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_1082_);
lean_dec(v_hName_x3f_1080_);
lean_dec(v_xName_x3f_1079_);
lean_dec_ref(v_bs_1072_);
v_a_1095_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1084_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1084_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_bs_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
size_t v_sz_boxed_1109_; size_t v_i_boxed_1110_; lean_object* v_res_1111_; 
v_sz_boxed_1109_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1110_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1109_, v_i_boxed_1110_, v_bs_1106_, v___y_1107_);
lean_dec(v___y_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1112_, lean_object* v_a_1113_, lean_object* v_as_1114_, size_t v_i_1115_, size_t v_stop_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_usize_dec_eq(v_i_1115_, v_stop_1116_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v_expr_1124_; lean_object* v___x_1125_; uint8_t v_foApprox_1126_; uint8_t v_ctxApprox_1127_; uint8_t v_quasiPatternApprox_1128_; uint8_t v_constApprox_1129_; uint8_t v_isDefEqStuckEx_1130_; uint8_t v_unificationHints_1131_; uint8_t v_proofIrrelevance_1132_; uint8_t v_assignSyntheticOpaque_1133_; uint8_t v_offsetCnstrs_1134_; uint8_t v_etaStruct_1135_; uint8_t v_univApprox_1136_; uint8_t v_iota_1137_; uint8_t v_beta_1138_; uint8_t v_proj_1139_; uint8_t v_zeta_1140_; uint8_t v_zetaDelta_1141_; uint8_t v_zetaUnused_1142_; uint8_t v_zetaHave_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1191_; 
v___x_1123_ = lean_array_uget_borrowed(v_as_1114_, v_i_1115_);
v_expr_1124_ = lean_ctor_get(v___x_1123_, 0);
v___x_1125_ = l_Lean_Meta_Context_config(v___y_1117_);
v_foApprox_1126_ = lean_ctor_get_uint8(v___x_1125_, 0);
v_ctxApprox_1127_ = lean_ctor_get_uint8(v___x_1125_, 1);
v_quasiPatternApprox_1128_ = lean_ctor_get_uint8(v___x_1125_, 2);
v_constApprox_1129_ = lean_ctor_get_uint8(v___x_1125_, 3);
v_isDefEqStuckEx_1130_ = lean_ctor_get_uint8(v___x_1125_, 4);
v_unificationHints_1131_ = lean_ctor_get_uint8(v___x_1125_, 5);
v_proofIrrelevance_1132_ = lean_ctor_get_uint8(v___x_1125_, 6);
v_assignSyntheticOpaque_1133_ = lean_ctor_get_uint8(v___x_1125_, 7);
v_offsetCnstrs_1134_ = lean_ctor_get_uint8(v___x_1125_, 8);
v_etaStruct_1135_ = lean_ctor_get_uint8(v___x_1125_, 10);
v_univApprox_1136_ = lean_ctor_get_uint8(v___x_1125_, 11);
v_iota_1137_ = lean_ctor_get_uint8(v___x_1125_, 12);
v_beta_1138_ = lean_ctor_get_uint8(v___x_1125_, 13);
v_proj_1139_ = lean_ctor_get_uint8(v___x_1125_, 14);
v_zeta_1140_ = lean_ctor_get_uint8(v___x_1125_, 15);
v_zetaDelta_1141_ = lean_ctor_get_uint8(v___x_1125_, 16);
v_zetaUnused_1142_ = lean_ctor_get_uint8(v___x_1125_, 17);
v_zetaHave_1143_ = lean_ctor_get_uint8(v___x_1125_, 18);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1145_ = v___x_1125_;
v_isShared_1146_ = v_isSharedCheck_1191_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v___x_1125_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1191_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v_trackZetaDelta_1147_; lean_object* v_zetaDeltaSet_1148_; lean_object* v_lctx_1149_; lean_object* v_localInstances_1150_; lean_object* v_defEqCtx_x3f_1151_; lean_object* v_synthPendingDepth_1152_; lean_object* v_canUnfold_x3f_1153_; uint8_t v_univApprox_1154_; uint8_t v_inTypeClassResolution_1155_; uint8_t v_cacheInferType_1156_; lean_object* v_config_1158_; 
v_trackZetaDelta_1147_ = lean_ctor_get_uint8(v___y_1117_, sizeof(void*)*7);
v_zetaDeltaSet_1148_ = lean_ctor_get(v___y_1117_, 1);
v_lctx_1149_ = lean_ctor_get(v___y_1117_, 2);
v_localInstances_1150_ = lean_ctor_get(v___y_1117_, 3);
v_defEqCtx_x3f_1151_ = lean_ctor_get(v___y_1117_, 4);
v_synthPendingDepth_1152_ = lean_ctor_get(v___y_1117_, 5);
v_canUnfold_x3f_1153_ = lean_ctor_get(v___y_1117_, 6);
v_univApprox_1154_ = lean_ctor_get_uint8(v___y_1117_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1155_ = lean_ctor_get_uint8(v___y_1117_, sizeof(void*)*7 + 2);
v_cacheInferType_1156_ = lean_ctor_get_uint8(v___y_1117_, sizeof(void*)*7 + 3);
if (v_isShared_1146_ == 0)
{
v_config_1158_ = v___x_1145_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 0, v_foApprox_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 1, v_ctxApprox_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 2, v_quasiPatternApprox_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 3, v_constApprox_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 4, v_isDefEqStuckEx_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 5, v_unificationHints_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 6, v_proofIrrelevance_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 7, v_assignSyntheticOpaque_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 8, v_offsetCnstrs_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 10, v_etaStruct_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 11, v_univApprox_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 12, v_iota_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 13, v_beta_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 14, v_proj_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 15, v_zeta_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 16, v_zetaDelta_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 17, v_zetaUnused_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, 18, v_zetaHave_1143_);
v_config_1158_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; lean_object* v___x_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; uint64_t v_key_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_ctor_set_uint8(v_config_1158_, 9, v_transparency_1112_);
v___x_1159_ = l_Lean_Meta_Context_configKey(v___y_1117_);
v___x_1160_ = 2ULL;
v___x_1161_ = lean_uint64_shift_right(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_uint64_shift_left(v___x_1161_, v___x_1160_);
v___x_1164_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1112_);
v_key_1165_ = lean_uint64_lor(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1166_, 0, v_config_1158_);
lean_ctor_set_uint64(v___x_1166_, sizeof(void*)*1, v_key_1165_);
lean_inc(v_canUnfold_x3f_1153_);
lean_inc(v_synthPendingDepth_1152_);
lean_inc(v_defEqCtx_x3f_1151_);
lean_inc_ref(v_localInstances_1150_);
lean_inc_ref(v_lctx_1149_);
lean_inc(v_zetaDeltaSet_1148_);
v___x_1167_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_zetaDeltaSet_1148_);
lean_ctor_set(v___x_1167_, 2, v_lctx_1149_);
lean_ctor_set(v___x_1167_, 3, v_localInstances_1150_);
lean_ctor_set(v___x_1167_, 4, v_defEqCtx_x3f_1151_);
lean_ctor_set(v___x_1167_, 5, v_synthPendingDepth_1152_);
lean_ctor_set(v___x_1167_, 6, v_canUnfold_x3f_1153_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*7, v_trackZetaDelta_1147_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*7 + 1, v_univApprox_1154_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1155_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*7 + 3, v_cacheInferType_1156_);
lean_inc_ref(v_expr_1124_);
lean_inc_ref(v_a_1113_);
v___x_1168_ = l_Lean_Meta_kabstract(v_a_1113_, v_expr_1124_, v___x_1162_, v___x_1167_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec_ref(v___x_1167_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1181_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = l_Lean_Expr_hasLooseBVars(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1173_ == 0)
{
size_t v___x_1174_; size_t v___x_1175_; 
lean_del_object(v___x_1171_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1115_, v___x_1174_);
v_i_1115_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec_ref(v_a_1113_);
v___x_1177_ = lean_box(v___x_1173_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1177_);
v___x_1179_ = v___x_1171_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_a_1113_);
v_a_1182_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1168_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1168_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
else
{
uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_a_1113_);
v___x_1192_ = 0;
v___x_1193_ = lean_box(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1195_, lean_object* v_a_1196_, lean_object* v_as_1197_, lean_object* v_i_1198_, lean_object* v_stop_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_transparency_boxed_1205_; size_t v_i_boxed_1206_; size_t v_stop_boxed_1207_; lean_object* v_res_1208_; 
v_transparency_boxed_1205_ = lean_unbox(v_transparency_1195_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_stop_boxed_1207_ = lean_unbox_usize(v_stop_1199_);
lean_dec(v_stop_1199_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1205_, v_a_1196_, v_as_1197_, v_i_boxed_1206_, v_stop_boxed_1207_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_as_1197_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1209_, lean_object* v___x_1210_, uint8_t v_transparency_1211_, lean_object* v_as_1212_, size_t v_i_1213_, size_t v_stop_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_a_1222_; uint8_t v___x_1226_; 
v___x_1226_ = lean_usize_dec_eq(v_i_1213_, v_stop_1214_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; uint8_t v_a_1229_; lean_object* v___x_1231_; 
v___x_1227_ = lean_array_uget_borrowed(v_as_1212_, v_i_1213_);
lean_inc(v___x_1227_);
v___x_1231_ = l_Lean_FVarId_getType___redArg(v___x_1227_, v___y_1216_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1233_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1232_, v___y_1217_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_nat_dec_eq(v___x_1210_, v___x_1235_);
v___x_1237_ = lean_array_get_size(v_a_1209_);
v___x_1238_ = lean_nat_dec_lt(v___x_1235_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_a_1234_);
v_a_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
if (v___x_1238_ == 0)
{
lean_dec(v_a_1234_);
v_a_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1237_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1211_, v_a_1234_, v_a_1209_, v___x_1239_, v___x_1240_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
v_a_1229_ = v___x_1243_;
goto v___jp_1228_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_b_1215_);
v_a_1244_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1241_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_b_1215_);
v_a_1252_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1233_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1233_);
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
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_b_1215_);
v_a_1260_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1231_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1231_);
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
v___jp_1228_:
{
if (v_a_1229_ == 0)
{
v_a_1222_ = v_b_1215_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1230_; 
lean_inc(v___x_1227_);
v___x_1230_ = lean_array_push(v_b_1215_, v___x_1227_);
v_a_1222_ = v___x_1230_;
goto v___jp_1221_;
}
}
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_b_1215_);
return v___x_1268_;
}
v___jp_1221_:
{
size_t v___x_1223_; size_t v___x_1224_; 
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1213_, v___x_1223_);
v_i_1213_ = v___x_1224_;
v_b_1215_ = v_a_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1269_, lean_object* v___x_1270_, lean_object* v_transparency_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_transparency_boxed_1281_; size_t v_i_boxed_1282_; size_t v_stop_boxed_1283_; lean_object* v_res_1284_; 
v_transparency_boxed_1281_ = lean_unbox(v_transparency_1271_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1283_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1269_, v___x_1270_, v_transparency_boxed_1281_, v_as_1272_, v_i_boxed_1282_, v_stop_boxed_1283_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v_as_1272_);
lean_dec(v___x_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1285_, lean_object* v_a_1286_, lean_object* v___x_1287_, lean_object* v_as_1288_, size_t v_i_1289_, size_t v_stop_1290_, lean_object* v_b_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_a_1298_; uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_eq(v_i_1289_, v_stop_1290_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v_a_1305_; lean_object* v___x_1307_; 
v___x_1303_ = lean_array_uget_borrowed(v_as_1288_, v_i_1289_);
lean_inc(v___x_1303_);
v___x_1307_ = l_Lean_FVarId_getType___redArg(v___x_1303_, v___y_1292_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref(v___x_1307_);
v___x_1309_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1308_, v___y_1293_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_nat_dec_eq(v___x_1287_, v___x_1311_);
v___x_1313_ = lean_array_get_size(v_a_1286_);
v___x_1314_ = lean_nat_dec_lt(v___x_1311_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec(v_a_1310_);
v_a_1305_ = v___x_1312_;
goto v___jp_1304_;
}
else
{
if (v___x_1314_ == 0)
{
lean_dec(v_a_1310_);
v_a_1305_ = v___x_1312_;
goto v___jp_1304_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1313_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1285_, v_a_1310_, v_a_1286_, v___x_1315_, v___x_1316_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; uint8_t v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = lean_unbox(v_a_1318_);
lean_dec(v_a_1318_);
v_a_1305_ = v___x_1319_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_b_1291_);
v_a_1320_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1317_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_b_1291_);
v_a_1328_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1309_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1309_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_b_1291_);
v_a_1336_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1307_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1307_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
v___jp_1304_:
{
if (v_a_1305_ == 0)
{
v_a_1298_ = v_b_1291_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1306_; 
lean_inc(v___x_1303_);
v___x_1306_ = lean_array_push(v_b_1291_, v___x_1303_);
v_a_1298_ = v___x_1306_;
goto v___jp_1297_;
}
}
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1291_);
return v___x_1344_;
}
v___jp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1289_, v___x_1299_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1286_, v___x_1287_, v_transparency_1285_, v_as_1288_, v___x_1300_, v_stop_1290_, v_a_1298_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1345_, lean_object* v_a_1346_, lean_object* v___x_1347_, lean_object* v_as_1348_, lean_object* v_i_1349_, lean_object* v_stop_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_transparency_boxed_1357_; size_t v_i_boxed_1358_; size_t v_stop_boxed_1359_; lean_object* v_res_1360_; 
v_transparency_boxed_1357_ = lean_unbox(v_transparency_1345_);
v_i_boxed_1358_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_stop_boxed_1359_ = lean_unbox_usize(v_stop_1350_);
lean_dec(v_stop_1350_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1357_, v_a_1346_, v___x_1347_, v_as_1348_, v_i_boxed_1358_, v_stop_boxed_1359_, v_b_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec_ref(v_as_1348_);
lean_dec(v___x_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1363_, lean_object* v_args_1364_, lean_object* v_hyps_1365_, lean_object* v_fvarSubst_1366_, uint8_t v_transparency_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_array_get_size(v_hyps_1365_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_nat_dec_eq(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_sz_1376_ = lean_array_size(v_args_1364_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1376_, v___x_1377_, v_args_1364_, v_a_1369_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; uint8_t v___x_1380_; lean_object* v_a_1382_; lean_object* v___y_1456_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = 1;
v___x_1466_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1467_ = lean_nat_dec_lt(v___x_1374_, v___x_1373_);
if (v___x_1467_ == 0)
{
v_a_1382_ = v___x_1466_;
goto v___jp_1381_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_le(v___x_1373_, v___x_1373_);
if (v___x_1468_ == 0)
{
if (v___x_1467_ == 0)
{
v_a_1382_ = v___x_1466_;
goto v___jp_1381_;
}
else
{
size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_usize_of_nat(v___x_1373_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1367_, v_a_1379_, v___x_1373_, v_hyps_1365_, v___x_1377_, v___x_1469_, v___x_1466_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
v___y_1456_ = v___x_1470_;
goto v___jp_1455_;
}
}
else
{
size_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_usize_of_nat(v___x_1373_);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1367_, v_a_1379_, v___x_1373_, v_hyps_1365_, v___x_1377_, v___x_1471_, v___x_1466_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
v___y_1456_ = v___x_1472_;
goto v___jp_1455_;
}
}
v___jp_1381_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_MVarId_revert(v_mvarId_1363_, v_a_1382_, v___x_1380_, v___x_1375_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v_fst_1385_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_fst_1385_);
v_snd_1386_ = lean_ctor_get(v_a_1384_, 1);
lean_inc(v_snd_1386_);
lean_dec(v_a_1384_);
v___x_1387_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1386_, v_a_1379_, v_transparency_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1438_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
v_fst_1389_ = lean_ctor_get(v_a_1388_, 0);
v_snd_1390_ = lean_ctor_get(v_a_1388_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_a_1388_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1392_ = v_a_1388_;
v_isShared_1393_ = v_isSharedCheck_1438_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_inc(v_fst_1389_);
lean_dec(v_a_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1438_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_array_get_size(v_fst_1385_);
v___x_1395_ = lean_box(0);
v___x_1396_ = l_Lean_Meta_introNCore(v_snd_1390_, v___x_1394_, v___x_1395_, v___x_1375_, v___x_1380_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1429_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1429_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1429_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1428_; 
v_fst_1401_ = lean_ctor_get(v_a_1397_, 0);
v_snd_1402_ = lean_ctor_get(v_a_1397_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1404_ = v_a_1397_;
v_isShared_1405_ = v_isSharedCheck_1428_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_a_1397_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1428_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_array_get_size(v_fst_1401_);
v___x_1407_ = l_Array_toSubarray___redArg(v_fst_1401_, v___x_1374_, v___x_1406_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1407_);
lean_ctor_set(v___x_1404_, 0, v_fvarSubst_1366_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fvarSubst_1366_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
size_t v_sz_1410_; lean_object* v___x_1411_; lean_object* v_fst_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1425_; 
v_sz_1410_ = lean_array_size(v_fst_1385_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1385_, v_sz_1410_, v___x_1377_, v___x_1409_);
lean_dec(v_fst_1385_);
v_fst_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1411_, 1);
lean_dec(v_unused_1426_);
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_fst_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_snd_1402_);
lean_ctor_set(v___x_1414_, 0, v_fst_1389_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_fst_1389_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1402_);
v___x_1417_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___x_1417_);
lean_ctor_set(v___x_1392_, 0, v_fst_1412_);
v___x_1419_ = v___x_1392_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1419_);
v___x_1421_ = v___x_1399_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
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
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1392_);
lean_dec(v_fst_1389_);
lean_dec(v_fst_1385_);
lean_dec(v_fvarSubst_1366_);
v_a_1430_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1396_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1396_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_fst_1385_);
lean_dec(v_fvarSubst_1366_);
v_a_1439_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1387_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1387_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1379_);
lean_dec(v_fvarSubst_1366_);
v_a_1447_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1383_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1383_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
v___jp_1455_:
{
if (lean_obj_tag(v___y_1456_) == 0)
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v___y_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___y_1456_);
v_a_1382_ = v_a_1457_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1379_);
lean_dec(v_fvarSubst_1366_);
lean_dec(v_mvarId_1363_);
v_a_1458_ = lean_ctor_get(v___y_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___y_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___y_1456_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___y_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_fvarSubst_1366_);
lean_dec(v_mvarId_1363_);
v_a_1473_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1378_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1378_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1363_, v_args_1364_, v_transparency_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1490_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_fvarSubst_1366_);
lean_ctor_set(v___x_1486_, 1, v_a_1482_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1486_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_fvarSubst_1366_);
v_a_1491_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1481_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1481_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1499_, lean_object* v_args_1500_, lean_object* v_hyps_1501_, lean_object* v_fvarSubst_1502_, lean_object* v_transparency_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
uint8_t v_transparency_boxed_1509_; lean_object* v_res_1510_; 
v_transparency_boxed_1509_ = lean_unbox(v_transparency_1503_);
v_res_1510_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1499_, v_args_1500_, v_hyps_1501_, v_fvarSubst_1502_, v_transparency_boxed_1509_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec_ref(v_hyps_1501_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1511_, v_i_1512_, v_bs_1513_, v___y_1515_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1520_, lean_object* v_i_1521_, lean_object* v_bs_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1520_);
lean_dec(v_sz_1520_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1528_, v_i_boxed_1529_, v_bs_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1530_;
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
