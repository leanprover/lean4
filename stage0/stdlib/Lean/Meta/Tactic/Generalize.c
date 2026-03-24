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
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
lean_inc(v_a_221_);
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
uint8_t v___x_4818__boxed_508_; uint8_t v___x_4819__boxed_509_; lean_object* v_res_510_; 
v___x_4818__boxed_508_ = lean_unbox(v___x_499_);
v___x_4819__boxed_509_ = lean_unbox(v___x_500_);
v_res_510_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(v_args_497_, v___x_498_, v___x_4818__boxed_508_, v___x_4819__boxed_509_, v_xs_501_, v_type_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
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
size_t v_x_5016__boxed_694_; size_t v_x_5017__boxed_695_; lean_object* v_res_696_; 
v_x_5016__boxed_694_ = lean_unbox_usize(v_x_690_);
lean_dec(v_x_690_);
v_x_5017__boxed_695_ = lean_unbox_usize(v_x_691_);
lean_dec(v_x_691_);
v_res_696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_689_, v_x_5016__boxed_694_, v_x_5017__boxed_695_, v_x_692_, v_x_693_);
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
lean_object* v___x_708_; lean_object* v_mctx_709_; lean_object* v_cache_710_; lean_object* v_zetaDeltaFVarIds_711_; lean_object* v_postponed_712_; lean_object* v_diag_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_740_; 
v___x_708_ = lean_st_ref_take(v___y_706_);
v_mctx_709_ = lean_ctor_get(v___x_708_, 0);
v_cache_710_ = lean_ctor_get(v___x_708_, 1);
v_zetaDeltaFVarIds_711_ = lean_ctor_get(v___x_708_, 2);
v_postponed_712_ = lean_ctor_get(v___x_708_, 3);
v_diag_713_ = lean_ctor_get(v___x_708_, 4);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_740_ == 0)
{
v___x_715_ = v___x_708_;
v_isShared_716_ = v_isSharedCheck_740_;
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
v_isShared_716_ = v_isSharedCheck_740_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_depth_717_; lean_object* v_levelAssignDepth_718_; lean_object* v_mvarCounter_719_; lean_object* v_lDepth_720_; lean_object* v_decls_721_; lean_object* v_userNames_722_; lean_object* v_lAssignment_723_; lean_object* v_eAssignment_724_; lean_object* v_dAssignment_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_739_; 
v_depth_717_ = lean_ctor_get(v_mctx_709_, 0);
v_levelAssignDepth_718_ = lean_ctor_get(v_mctx_709_, 1);
v_mvarCounter_719_ = lean_ctor_get(v_mctx_709_, 2);
v_lDepth_720_ = lean_ctor_get(v_mctx_709_, 3);
v_decls_721_ = lean_ctor_get(v_mctx_709_, 4);
v_userNames_722_ = lean_ctor_get(v_mctx_709_, 5);
v_lAssignment_723_ = lean_ctor_get(v_mctx_709_, 6);
v_eAssignment_724_ = lean_ctor_get(v_mctx_709_, 7);
v_dAssignment_725_ = lean_ctor_get(v_mctx_709_, 8);
v_isSharedCheck_739_ = !lean_is_exclusive(v_mctx_709_);
if (v_isSharedCheck_739_ == 0)
{
v___x_727_ = v_mctx_709_;
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_dAssignment_725_);
lean_inc(v_eAssignment_724_);
lean_inc(v_lAssignment_723_);
lean_inc(v_userNames_722_);
lean_inc(v_decls_721_);
lean_inc(v_lDepth_720_);
lean_inc(v_mvarCounter_719_);
lean_inc(v_levelAssignDepth_718_);
lean_inc(v_depth_717_);
lean_dec(v_mctx_709_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_eAssignment_724_, v_mvarId_704_, v_val_705_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 7, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_depth_717_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_levelAssignDepth_718_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_mvarCounter_719_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_lDepth_720_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_decls_721_);
lean_ctor_set(v_reuseFailAlloc_738_, 5, v_userNames_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 6, v_lAssignment_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 7, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_738_, 8, v_dAssignment_725_);
v___x_731_ = v_reuseFailAlloc_738_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_731_);
v___x_733_ = v___x_715_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_cache_710_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_zetaDeltaFVarIds_711_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_postponed_712_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_diag_713_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_st_ref_set(v___y_706_, v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* v_mvarId_741_, lean_object* v_val_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_741_, v_val_742_, v___y_743_);
lean_dec(v___y_743_);
return v_res_745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* v_mvarId_749_, lean_object* v___x_750_, lean_object* v_args_751_, uint8_t v_transparency_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
lean_inc(v___x_750_);
lean_inc(v_mvarId_749_);
v___x_758_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_749_, v___x_750_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v___x_758_);
lean_inc(v_mvarId_749_);
v___x_759_ = l_Lean_MVarId_getTag(v_mvarId_749_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
lean_inc(v_mvarId_749_);
v___x_761_ = l_Lean_MVarId_getType(v_mvarId_749_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_877_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_762_, v___y_754_);
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_877_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_877_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_877_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(v_args_751_, v_transparency_752_, v_a_764_, v___x_768_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; uint8_t v___y_778_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___x_845_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
lean_inc(v_a_770_);
v___x_845_ = l_Lean_Meta_isTypeCorrect(v_a_770_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; uint8_t v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
lean_inc(v_a_770_);
v___x_849_ = l_Lean_indentExpr(v_a_770_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_inc(v_mvarId_749_);
v___x_852_ = l_Lean_Meta_throwTacticEx___redArg(v___x_750_, v_mvarId_749_, v___x_851_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref(v___x_852_);
v___y_796_ = v___y_753_;
v___y_797_ = v___y_754_;
v___y_798_ = v___y_755_;
v___y_799_ = v___y_756_;
goto v___jp_795_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_770_);
lean_del_object(v___x_766_);
lean_dec(v_a_760_);
lean_dec_ref(v_args_751_);
lean_dec(v_mvarId_749_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_dec(v___x_750_);
v___y_796_ = v___y_753_;
v___y_797_ = v___y_754_;
v___y_798_ = v___y_755_;
v___y_799_ = v___y_756_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_770_);
lean_del_object(v___x_766_);
lean_dec(v_a_760_);
lean_dec_ref(v_args_751_);
lean_dec(v___x_750_);
lean_dec(v_mvarId_749_);
v_a_861_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_845_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_845_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
v___jp_771_:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_770_, v_a_760_, v___y_774_, v___y_775_, v___y_777_, v___y_773_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
lean_inc(v_a_780_);
v___x_781_ = l_Lean_mkAppN(v_a_780_, v___y_776_);
lean_dec_ref(v___y_776_);
v___x_782_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_749_, v___x_781_, v___y_775_);
lean_dec_ref(v___x_782_);
v___x_783_ = 1;
v___x_784_ = l_Lean_Expr_mvarId_x21(v_a_780_);
lean_dec(v_a_780_);
v___x_785_ = lean_box(0);
v___x_786_ = l_Lean_Meta_introNCore(v___x_784_, v___y_772_, v___x_785_, v___y_778_, v___x_783_, v___y_774_, v___y_775_, v___y_777_, v___y_773_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___y_776_);
lean_dec(v___y_772_);
lean_dec(v_mvarId_749_);
v_a_787_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_779_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_779_);
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
v___jp_795_:
{
size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_sz_800_ = lean_array_size(v_args_751_);
v___x_801_ = ((size_t)0ULL);
lean_inc_ref(v_args_751_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(v_sz_800_, v___x_801_, v_args_751_);
v___x_803_ = lean_array_get_size(v_args_751_);
v___x_804_ = lean_nat_dec_lt(v___x_768_, v___x_803_);
if (v___x_804_ == 0)
{
lean_del_object(v___x_766_);
lean_dec_ref(v_args_751_);
v___y_772_ = v___x_803_;
v___y_773_ = v___y_799_;
v___y_774_ = v___y_796_;
v___y_775_ = v___y_797_;
v___y_776_ = v___x_802_;
v___y_777_ = v___y_798_;
v___y_778_ = v___x_804_;
goto v___jp_771_;
}
else
{
if (v___x_804_ == 0)
{
lean_del_object(v___x_766_);
lean_dec_ref(v_args_751_);
v___y_772_ = v___x_803_;
v___y_773_ = v___y_799_;
v___y_774_ = v___y_796_;
v___y_775_ = v___y_797_;
v___y_776_ = v___x_802_;
v___y_777_ = v___y_798_;
v___y_778_ = v___x_804_;
goto v___jp_771_;
}
else
{
size_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_usize_of_nat(v___x_803_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(v_args_751_, v___x_801_, v___x_805_);
if (v___x_806_ == 0)
{
lean_del_object(v___x_766_);
lean_dec_ref(v_args_751_);
v___y_772_ = v___x_803_;
v___y_773_ = v___y_799_;
v___y_774_ = v___y_796_;
v___y_775_ = v___y_797_;
v___y_776_ = v___x_802_;
v___y_777_ = v___y_798_;
v___y_778_ = v___x_806_;
goto v___jp_771_;
}
else
{
uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_812_; 
v___x_807_ = 0;
v___x_808_ = lean_box(v___x_807_);
v___x_809_ = lean_box(v___x_806_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_810_, 0, v_args_751_);
lean_closure_set(v___f_810_, 1, v___x_768_);
lean_closure_set(v___f_810_, 2, v___x_808_);
lean_closure_set(v___f_810_, 3, v___x_809_);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 1);
lean_ctor_set(v___x_766_, 0, v___x_803_);
v___x_812_ = v___x_766_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_803_);
v___x_812_ = v_reuseFailAlloc_844_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(v_a_770_, v___x_812_, v___f_810_, v___x_807_, v___x_807_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v_fst_815_; lean_object* v_snd_816_; lean_object* v___x_817_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v_fst_815_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_fst_815_);
v_snd_816_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_snd_816_);
lean_dec(v_a_814_);
v___x_817_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_snd_816_, v_a_760_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_817_);
lean_inc(v_a_818_);
v___x_819_ = l_Lean_mkAppN(v_a_818_, v___x_802_);
lean_dec_ref(v___x_802_);
lean_inc(v_fst_815_);
v___x_820_ = lean_array_mk(v_fst_815_);
v___x_821_ = l_Lean_mkAppN(v___x_819_, v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_749_, v___x_821_, v___y_797_);
lean_dec_ref(v___x_822_);
v___x_823_ = l_Lean_Expr_mvarId_x21(v_a_818_);
lean_dec(v_a_818_);
v___x_824_ = l_List_lengthTR___redArg(v_fst_815_);
lean_dec(v_fst_815_);
v___x_825_ = lean_nat_add(v___x_803_, v___x_824_);
lean_dec(v___x_824_);
v___x_826_ = lean_box(0);
v___x_827_ = l_Lean_Meta_introNCore(v___x_823_, v___x_825_, v___x_826_, v___x_807_, v___x_806_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_827_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_fst_815_);
lean_dec_ref(v___x_802_);
lean_dec(v_mvarId_749_);
v_a_828_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_817_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_817_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v___x_802_);
lean_dec(v_a_760_);
lean_dec(v_mvarId_749_);
v_a_836_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_813_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_813_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
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
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_del_object(v___x_766_);
lean_dec(v_a_760_);
lean_dec_ref(v_args_751_);
lean_dec(v___x_750_);
lean_dec(v_mvarId_749_);
v_a_869_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_769_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_769_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_760_);
lean_dec_ref(v_args_751_);
lean_dec(v___x_750_);
lean_dec(v_mvarId_749_);
v_a_878_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_761_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_761_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_args_751_);
lean_dec(v___x_750_);
lean_dec(v_mvarId_749_);
v_a_886_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_759_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_759_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_args_751_);
lean_dec(v___x_750_);
lean_dec(v_mvarId_749_);
v_a_894_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_758_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_758_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* v_mvarId_902_, lean_object* v___x_903_, lean_object* v_args_904_, lean_object* v_transparency_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_transparency_boxed_911_; lean_object* v_res_912_; 
v_transparency_boxed_911_ = lean_unbox(v_transparency_905_);
v_res_912_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(v_mvarId_902_, v___x_903_, v_args_904_, v_transparency_boxed_911_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* v_mvarId_916_, lean_object* v_args_917_, uint8_t v_transparency_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___x_927_; 
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1));
v___x_925_ = lean_box(v_transparency_918_);
lean_inc(v_mvarId_916_);
v___f_926_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(v___f_926_, 0, v_mvarId_916_);
lean_closure_set(v___f_926_, 1, v___x_924_);
lean_closure_set(v___f_926_, 2, v_args_917_);
lean_closure_set(v___f_926_, 3, v___x_925_);
v___x_927_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(v_mvarId_916_, v___f_926_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* v_mvarId_928_, lean_object* v_args_929_, lean_object* v_transparency_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_transparency_boxed_936_; lean_object* v_res_937_; 
v_transparency_boxed_936_ = lean_unbox(v_transparency_930_);
v_res_937_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_928_, v_args_929_, v_transparency_boxed_936_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* v_mvarId_938_, lean_object* v_val_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(v_mvarId_938_, v_val_939_, v___y_941_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* v_mvarId_946_, lean_object* v_val_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(v_mvarId_946_, v_val_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(v_x_955_, v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, size_t v_x_961_, size_t v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(v_x_960_, v_x_961_, v_x_962_, v_x_963_, v_x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
size_t v_x_5601__boxed_972_; size_t v_x_5602__boxed_973_; lean_object* v_res_974_; 
v_x_5601__boxed_972_ = lean_unbox_usize(v_x_968_);
lean_dec(v_x_968_);
v_x_5602__boxed_973_ = lean_unbox_usize(v_x_969_);
lean_dec(v_x_969_);
v_res_974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(v_00_u03b2_966_, v_x_967_, v_x_5601__boxed_972_, v_x_5602__boxed_973_, v_x_970_, v_x_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_975_, lean_object* v_n_976_, lean_object* v_k_977_, lean_object* v_v_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(v_n_976_, v_k_977_, v_v_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_980_, size_t v_depth_981_, lean_object* v_keys_982_, lean_object* v_vals_983_, lean_object* v_heq_984_, lean_object* v_i_985_, lean_object* v_entries_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(v_depth_981_, v_keys_982_, v_vals_983_, v_i_985_, v_entries_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_988_, lean_object* v_depth_989_, lean_object* v_keys_990_, lean_object* v_vals_991_, lean_object* v_heq_992_, lean_object* v_i_993_, lean_object* v_entries_994_){
_start:
{
size_t v_depth_boxed_995_; lean_object* v_res_996_; 
v_depth_boxed_995_ = lean_unbox_usize(v_depth_989_);
lean_dec(v_depth_989_);
v_res_996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(v_00_u03b2_988_, v_depth_boxed_995_, v_keys_990_, v_vals_991_, v_heq_992_, v_i_993_, v_entries_994_);
lean_dec_ref(v_vals_991_);
lean_dec_ref(v_keys_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* v_mvarId_1003_, lean_object* v_args_1004_, uint8_t v_transparency_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1003_, v_args_1004_, v_transparency_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1011_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* v_as_1022_, size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_b_1025_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* v_as_1062_, lean_object* v_sz_1063_, lean_object* v_i_1064_, lean_object* v_b_1065_){
_start:
{
size_t v_sz_boxed_1066_; size_t v_i_boxed_1067_; lean_object* v_res_1068_; 
v_sz_boxed_1066_ = lean_unbox_usize(v_sz_1063_);
lean_dec(v_sz_1063_);
v_i_boxed_1067_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_as_1062_, v_sz_boxed_1066_, v_i_boxed_1067_, v_b_1065_);
lean_dec_ref(v_as_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_bs_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_bs_1071_);
return v___x_1075_;
}
else
{
lean_object* v_v_1076_; lean_object* v_expr_1077_; lean_object* v_xName_x3f_1078_; lean_object* v_hName_x3f_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1102_; 
v_v_1076_ = lean_array_uget(v_bs_1071_, v_i_1070_);
v_expr_1077_ = lean_ctor_get(v_v_1076_, 0);
v_xName_x3f_1078_ = lean_ctor_get(v_v_1076_, 1);
v_hName_x3f_1079_ = lean_ctor_get(v_v_1076_, 2);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_v_1076_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1081_ = v_v_1076_;
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_hName_x3f_1079_);
lean_inc(v_xName_x3f_1078_);
lean_inc(v_expr_1077_);
lean_dec(v_v_1076_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_expr_1077_, v___y_1072_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v_bs_x27_1086_; lean_object* v___x_1088_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v_bs_x27_1086_ = lean_array_uset(v_bs_1071_, v_i_1070_, v___x_1085_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_a_1084_);
v___x_1088_ = v___x_1081_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1084_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_xName_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_hName_x3f_1079_);
v___x_1088_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1070_, v___x_1089_);
v___x_1091_ = lean_array_uset(v_bs_x27_1086_, v_i_1070_, v___x_1088_);
v_i_1070_ = v___x_1090_;
v_bs_1071_ = v___x_1091_;
goto _start;
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1081_);
lean_dec(v_hName_x3f_1079_);
lean_dec(v_xName_x3f_1078_);
lean_dec_ref(v_bs_1071_);
v_a_1094_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1083_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1083_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* v_sz_1103_, lean_object* v_i_1104_, lean_object* v_bs_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1103_);
lean_dec(v_sz_1103_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1104_);
lean_dec(v_i_1104_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_boxed_1108_, v_i_boxed_1109_, v_bs_1105_, v___y_1106_);
lean_dec(v___y_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t v_transparency_1111_, lean_object* v_a_1112_, lean_object* v_as_1113_, size_t v_i_1114_, size_t v_stop_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_eq(v_i_1114_, v_stop_1115_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v_expr_1123_; lean_object* v___x_1124_; uint8_t v_foApprox_1125_; uint8_t v_ctxApprox_1126_; uint8_t v_quasiPatternApprox_1127_; uint8_t v_constApprox_1128_; uint8_t v_isDefEqStuckEx_1129_; uint8_t v_unificationHints_1130_; uint8_t v_proofIrrelevance_1131_; uint8_t v_assignSyntheticOpaque_1132_; uint8_t v_offsetCnstrs_1133_; uint8_t v_etaStruct_1134_; uint8_t v_univApprox_1135_; uint8_t v_iota_1136_; uint8_t v_beta_1137_; uint8_t v_proj_1138_; uint8_t v_zeta_1139_; uint8_t v_zetaDelta_1140_; uint8_t v_zetaUnused_1141_; uint8_t v_zetaHave_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1190_; 
v___x_1122_ = lean_array_uget_borrowed(v_as_1113_, v_i_1114_);
v_expr_1123_ = lean_ctor_get(v___x_1122_, 0);
v___x_1124_ = l_Lean_Meta_Context_config(v___y_1116_);
v_foApprox_1125_ = lean_ctor_get_uint8(v___x_1124_, 0);
v_ctxApprox_1126_ = lean_ctor_get_uint8(v___x_1124_, 1);
v_quasiPatternApprox_1127_ = lean_ctor_get_uint8(v___x_1124_, 2);
v_constApprox_1128_ = lean_ctor_get_uint8(v___x_1124_, 3);
v_isDefEqStuckEx_1129_ = lean_ctor_get_uint8(v___x_1124_, 4);
v_unificationHints_1130_ = lean_ctor_get_uint8(v___x_1124_, 5);
v_proofIrrelevance_1131_ = lean_ctor_get_uint8(v___x_1124_, 6);
v_assignSyntheticOpaque_1132_ = lean_ctor_get_uint8(v___x_1124_, 7);
v_offsetCnstrs_1133_ = lean_ctor_get_uint8(v___x_1124_, 8);
v_etaStruct_1134_ = lean_ctor_get_uint8(v___x_1124_, 10);
v_univApprox_1135_ = lean_ctor_get_uint8(v___x_1124_, 11);
v_iota_1136_ = lean_ctor_get_uint8(v___x_1124_, 12);
v_beta_1137_ = lean_ctor_get_uint8(v___x_1124_, 13);
v_proj_1138_ = lean_ctor_get_uint8(v___x_1124_, 14);
v_zeta_1139_ = lean_ctor_get_uint8(v___x_1124_, 15);
v_zetaDelta_1140_ = lean_ctor_get_uint8(v___x_1124_, 16);
v_zetaUnused_1141_ = lean_ctor_get_uint8(v___x_1124_, 17);
v_zetaHave_1142_ = lean_ctor_get_uint8(v___x_1124_, 18);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1144_ = v___x_1124_;
v_isShared_1145_ = v_isSharedCheck_1190_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v___x_1124_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1190_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
uint8_t v_trackZetaDelta_1146_; lean_object* v_zetaDeltaSet_1147_; lean_object* v_lctx_1148_; lean_object* v_localInstances_1149_; lean_object* v_defEqCtx_x3f_1150_; lean_object* v_synthPendingDepth_1151_; lean_object* v_canUnfold_x3f_1152_; uint8_t v_univApprox_1153_; uint8_t v_inTypeClassResolution_1154_; uint8_t v_cacheInferType_1155_; lean_object* v_config_1157_; 
v_trackZetaDelta_1146_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7);
v_zetaDeltaSet_1147_ = lean_ctor_get(v___y_1116_, 1);
v_lctx_1148_ = lean_ctor_get(v___y_1116_, 2);
v_localInstances_1149_ = lean_ctor_get(v___y_1116_, 3);
v_defEqCtx_x3f_1150_ = lean_ctor_get(v___y_1116_, 4);
v_synthPendingDepth_1151_ = lean_ctor_get(v___y_1116_, 5);
v_canUnfold_x3f_1152_ = lean_ctor_get(v___y_1116_, 6);
v_univApprox_1153_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1154_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 2);
v_cacheInferType_1155_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 3);
if (v_isShared_1145_ == 0)
{
v_config_1157_ = v___x_1144_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 0, v_foApprox_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 1, v_ctxApprox_1126_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 2, v_quasiPatternApprox_1127_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 3, v_constApprox_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 4, v_isDefEqStuckEx_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 5, v_unificationHints_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 6, v_proofIrrelevance_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 7, v_assignSyntheticOpaque_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 8, v_offsetCnstrs_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 10, v_etaStruct_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 11, v_univApprox_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 12, v_iota_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 13, v_beta_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 14, v_proj_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 15, v_zeta_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 16, v_zetaDelta_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 17, v_zetaUnused_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, 18, v_zetaHave_1142_);
v_config_1157_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; lean_object* v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v_key_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_ctor_set_uint8(v_config_1157_, 9, v_transparency_1111_);
v___x_1158_ = l_Lean_Meta_Context_configKey(v___y_1116_);
v___x_1159_ = 2ULL;
v___x_1160_ = lean_uint64_shift_right(v___x_1158_, v___x_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_uint64_shift_left(v___x_1160_, v___x_1159_);
v___x_1163_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_1111_);
v_key_1164_ = lean_uint64_lor(v___x_1162_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1165_, 0, v_config_1157_);
lean_ctor_set_uint64(v___x_1165_, sizeof(void*)*1, v_key_1164_);
lean_inc(v_canUnfold_x3f_1152_);
lean_inc(v_synthPendingDepth_1151_);
lean_inc(v_defEqCtx_x3f_1150_);
lean_inc_ref(v_localInstances_1149_);
lean_inc_ref(v_lctx_1148_);
lean_inc(v_zetaDeltaSet_1147_);
v___x_1166_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_zetaDeltaSet_1147_);
lean_ctor_set(v___x_1166_, 2, v_lctx_1148_);
lean_ctor_set(v___x_1166_, 3, v_localInstances_1149_);
lean_ctor_set(v___x_1166_, 4, v_defEqCtx_x3f_1150_);
lean_ctor_set(v___x_1166_, 5, v_synthPendingDepth_1151_);
lean_ctor_set(v___x_1166_, 6, v_canUnfold_x3f_1152_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7, v_trackZetaDelta_1146_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 1, v_univApprox_1153_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1154_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 3, v_cacheInferType_1155_);
lean_inc_ref(v_expr_1123_);
lean_inc_ref(v_a_1112_);
v___x_1167_ = l_Lean_Meta_kabstract(v_a_1112_, v_expr_1123_, v___x_1161_, v___x_1166_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1180_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___x_1172_; 
v___x_1172_ = l_Lean_Expr_hasLooseBVars(v_a_1168_);
lean_dec(v_a_1168_);
if (v___x_1172_ == 0)
{
size_t v___x_1173_; size_t v___x_1174_; 
lean_del_object(v___x_1170_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1114_, v___x_1173_);
v_i_1114_ = v___x_1174_;
goto _start;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec_ref(v_a_1112_);
v___x_1176_ = lean_box(v___x_1172_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1176_);
v___x_1178_ = v___x_1170_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_a_1112_);
v_a_1181_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1167_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1167_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
else
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_a_1112_);
v___x_1191_ = 0;
v___x_1192_ = lean_box(v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* v_transparency_1194_, lean_object* v_a_1195_, lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v_transparency_boxed_1204_; size_t v_i_boxed_1205_; size_t v_stop_boxed_1206_; lean_object* v_res_1207_; 
v_transparency_boxed_1204_ = lean_unbox(v_transparency_1194_);
v_i_boxed_1205_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1206_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_boxed_1204_, v_a_1195_, v_as_1196_, v_i_boxed_1205_, v_stop_boxed_1206_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v_as_1196_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* v_a_1208_, lean_object* v___x_1209_, uint8_t v_transparency_1210_, lean_object* v_as_1211_, size_t v_i_1212_, size_t v_stop_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_a_1221_; uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1212_, v_stop_1213_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; uint8_t v_a_1228_; lean_object* v___x_1230_; 
v___x_1226_ = lean_array_uget_borrowed(v_as_1211_, v_i_1212_);
lean_inc(v___x_1226_);
v___x_1230_ = l_Lean_FVarId_getType___redArg(v___x_1226_, v___y_1215_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1231_, v___y_1216_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_nat_dec_eq(v___x_1209_, v___x_1234_);
v___x_1236_ = lean_array_get_size(v_a_1208_);
v___x_1237_ = lean_nat_dec_lt(v___x_1234_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v_a_1233_);
v_a_1228_ = v___x_1235_;
goto v___jp_1227_;
}
else
{
if (v___x_1237_ == 0)
{
lean_dec(v_a_1233_);
v_a_1228_ = v___x_1235_;
goto v___jp_1227_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = ((size_t)0ULL);
v___x_1239_ = lean_usize_of_nat(v___x_1236_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1210_, v_a_1233_, v_a_1208_, v___x_1238_, v___x_1239_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; uint8_t v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_unbox(v_a_1241_);
lean_dec(v_a_1241_);
v_a_1228_ = v___x_1242_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_b_1214_);
v_a_1243_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1240_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1240_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_b_1214_);
v_a_1251_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1232_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1232_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_b_1214_);
v_a_1259_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1230_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1230_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
v___jp_1227_:
{
if (v_a_1228_ == 0)
{
v_a_1221_ = v_b_1214_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1229_; 
lean_inc(v___x_1226_);
v___x_1229_ = lean_array_push(v_b_1214_, v___x_1226_);
v_a_1221_ = v___x_1229_;
goto v___jp_1220_;
}
}
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1214_);
return v___x_1267_;
}
v___jp_1220_:
{
size_t v___x_1222_; size_t v___x_1223_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1212_, v___x_1222_);
v_i_1212_ = v___x_1223_;
v_b_1214_ = v_a_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* v_a_1268_, lean_object* v___x_1269_, lean_object* v_transparency_1270_, lean_object* v_as_1271_, lean_object* v_i_1272_, lean_object* v_stop_1273_, lean_object* v_b_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v_transparency_boxed_1280_; size_t v_i_boxed_1281_; size_t v_stop_boxed_1282_; lean_object* v_res_1283_; 
v_transparency_boxed_1280_ = lean_unbox(v_transparency_1270_);
v_i_boxed_1281_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_stop_boxed_1282_ = lean_unbox_usize(v_stop_1273_);
lean_dec(v_stop_1273_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1268_, v___x_1269_, v_transparency_boxed_1280_, v_as_1271_, v_i_boxed_1281_, v_stop_boxed_1282_, v_b_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_as_1271_);
lean_dec(v___x_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t v_transparency_1284_, lean_object* v_a_1285_, lean_object* v___x_1286_, lean_object* v_as_1287_, size_t v_i_1288_, size_t v_stop_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_a_1297_; uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_eq(v_i_1288_, v_stop_1289_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; uint8_t v_a_1304_; lean_object* v___x_1306_; 
v___x_1302_ = lean_array_uget_borrowed(v_as_1287_, v_i_1288_);
lean_inc(v___x_1302_);
v___x_1306_ = l_Lean_FVarId_getType___redArg(v___x_1302_, v___y_1291_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1306_);
v___x_1308_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(v_a_1307_, v___y_1292_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_nat_dec_eq(v___x_1286_, v___x_1310_);
v___x_1312_ = lean_array_get_size(v_a_1285_);
v___x_1313_ = lean_nat_dec_lt(v___x_1310_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec(v_a_1309_);
v_a_1304_ = v___x_1311_;
goto v___jp_1303_;
}
else
{
if (v___x_1313_ == 0)
{
lean_dec(v_a_1309_);
v_a_1304_ = v___x_1311_;
goto v___jp_1303_;
}
else
{
size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = lean_usize_of_nat(v___x_1312_);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(v_transparency_1284_, v_a_1309_, v_a_1285_, v___x_1314_, v___x_1315_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; uint8_t v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = lean_unbox(v_a_1317_);
lean_dec(v_a_1317_);
v_a_1304_ = v___x_1318_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_b_1290_);
v_a_1319_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1316_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_b_1290_);
v_a_1327_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1308_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1308_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_b_1290_);
v_a_1335_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1306_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1306_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
v___jp_1303_:
{
if (v_a_1304_ == 0)
{
v_a_1297_ = v_b_1290_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1305_; 
lean_inc(v___x_1302_);
v___x_1305_ = lean_array_push(v_b_1290_, v___x_1302_);
v_a_1297_ = v___x_1305_;
goto v___jp_1296_;
}
}
}
else
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_b_1290_);
return v___x_1343_;
}
v___jp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1288_, v___x_1298_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(v_a_1285_, v___x_1286_, v_transparency_1284_, v_as_1287_, v___x_1299_, v_stop_1289_, v_a_1297_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* v_transparency_1344_, lean_object* v_a_1345_, lean_object* v___x_1346_, lean_object* v_as_1347_, lean_object* v_i_1348_, lean_object* v_stop_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v_transparency_boxed_1356_; size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; lean_object* v_res_1359_; 
v_transparency_boxed_1356_ = lean_unbox(v_transparency_1344_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1348_);
lean_dec(v_i_1348_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1349_);
lean_dec(v_stop_1349_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_boxed_1356_, v_a_1345_, v___x_1346_, v_as_1347_, v_i_boxed_1357_, v_stop_boxed_1358_, v_b_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec_ref(v_as_1347_);
lean_dec(v___x_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* v_mvarId_1362_, lean_object* v_args_1363_, lean_object* v_hyps_1364_, lean_object* v_fvarSubst_1365_, uint8_t v_transparency_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_array_get_size(v_hyps_1364_);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_nat_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v_sz_1375_ = lean_array_size(v_args_1363_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1375_, v___x_1376_, v_args_1363_, v_a_1368_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; uint8_t v___x_1379_; lean_object* v_a_1381_; lean_object* v___y_1455_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = 1;
v___x_1465_ = ((lean_object*)(l_Lean_MVarId_generalizeHyp___closed__0));
v___x_1466_ = lean_nat_dec_lt(v___x_1373_, v___x_1372_);
if (v___x_1466_ == 0)
{
v_a_1381_ = v___x_1465_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_le(v___x_1372_, v___x_1372_);
if (v___x_1467_ == 0)
{
if (v___x_1466_ == 0)
{
v_a_1381_ = v___x_1465_;
goto v___jp_1380_;
}
else
{
size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_usize_of_nat(v___x_1372_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1366_, v_a_1378_, v___x_1372_, v_hyps_1364_, v___x_1376_, v___x_1468_, v___x_1465_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
v___y_1455_ = v___x_1469_;
goto v___jp_1454_;
}
}
else
{
size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_usize_of_nat(v___x_1372_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(v_transparency_1366_, v_a_1378_, v___x_1372_, v_hyps_1364_, v___x_1376_, v___x_1470_, v___x_1465_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
v___y_1455_ = v___x_1471_;
goto v___jp_1454_;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_MVarId_revert(v_mvarId_1362_, v_a_1381_, v___x_1379_, v___x_1374_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v_fst_1384_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v_a_1383_, 1);
lean_inc(v_snd_1385_);
lean_dec(v_a_1383_);
v___x_1386_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_snd_1385_, v_a_1378_, v_transparency_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_fst_1388_; lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1437_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref(v___x_1386_);
v_fst_1388_ = lean_ctor_get(v_a_1387_, 0);
v_snd_1389_ = lean_ctor_get(v_a_1387_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1387_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1391_ = v_a_1387_;
v_isShared_1392_ = v_isSharedCheck_1437_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_inc(v_fst_1388_);
lean_dec(v_a_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1437_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_array_get_size(v_fst_1384_);
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Lean_Meta_introNCore(v_snd_1389_, v___x_1393_, v___x_1394_, v___x_1374_, v___x_1379_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1428_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1428_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1427_; 
v_fst_1400_ = lean_ctor_get(v_a_1396_, 0);
v_snd_1401_ = lean_ctor_get(v_a_1396_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1403_ = v_a_1396_;
v_isShared_1404_ = v_isSharedCheck_1427_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1401_);
lean_inc(v_fst_1400_);
lean_dec(v_a_1396_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1427_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_array_get_size(v_fst_1400_);
v___x_1406_ = l_Array_toSubarray___redArg(v_fst_1400_, v___x_1373_, v___x_1405_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1406_);
lean_ctor_set(v___x_1403_, 0, v_fvarSubst_1365_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_fvarSubst_1365_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
size_t v_sz_1409_; lean_object* v___x_1410_; lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1424_; 
v_sz_1409_ = lean_array_size(v_fst_1384_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(v_fst_1384_, v_sz_1409_, v___x_1376_, v___x_1408_);
lean_dec(v_fst_1384_);
v_fst_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v___x_1410_, 1);
lean_dec(v_unused_1425_);
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_snd_1401_);
lean_ctor_set(v___x_1413_, 0, v_fst_1388_);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1388_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1401_);
v___x_1416_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v___x_1416_);
lean_ctor_set(v___x_1391_, 0, v_fst_1411_);
v___x_1418_ = v___x_1391_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1418_);
v___x_1420_ = v___x_1398_;
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
}
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_del_object(v___x_1391_);
lean_dec(v_fst_1388_);
lean_dec(v_fst_1384_);
lean_dec(v_fvarSubst_1365_);
v_a_1429_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1395_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1395_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_fst_1384_);
lean_dec(v_fvarSubst_1365_);
v_a_1438_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1386_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1386_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1378_);
lean_dec(v_fvarSubst_1365_);
v_a_1446_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1382_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1382_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
v___jp_1454_:
{
if (lean_obj_tag(v___y_1455_) == 0)
{
lean_object* v_a_1456_; 
v_a_1456_ = lean_ctor_get(v___y_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___y_1455_);
v_a_1381_ = v_a_1456_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_a_1378_);
lean_dec(v_fvarSubst_1365_);
lean_dec(v_mvarId_1362_);
v_a_1457_ = lean_ctor_get(v___y_1455_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___y_1455_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___y_1455_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___y_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_fvarSubst_1365_);
lean_dec(v_mvarId_1362_);
v_a_1472_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1377_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1377_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(v_mvarId_1362_, v_args_1363_, v_transparency_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1489_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_fvarSubst_1365_);
lean_ctor_set(v___x_1485_, 1, v_a_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_fvarSubst_1365_);
v_a_1490_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1480_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1480_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* v_mvarId_1498_, lean_object* v_args_1499_, lean_object* v_hyps_1500_, lean_object* v_fvarSubst_1501_, lean_object* v_transparency_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
uint8_t v_transparency_boxed_1508_; lean_object* v_res_1509_; 
v_transparency_boxed_1508_ = lean_unbox(v_transparency_1502_);
v_res_1509_ = l_Lean_MVarId_generalizeHyp(v_mvarId_1498_, v_args_1499_, v_hyps_1500_, v_fvarSubst_1501_, v_transparency_boxed_1508_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec_ref(v_hyps_1500_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t v_sz_1510_, size_t v_i_1511_, lean_object* v_bs_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(v_sz_1510_, v_i_1511_, v_bs_1512_, v___y_1514_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_bs_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(v_sz_boxed_1527_, v_i_boxed_1528_, v_bs_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1529_;
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
