// Lean compiler output
// Module: Lean.Meta.Match.CaseValues
// Imports: public import Lean.Meta.Basic public import Lean.Meta.Tactic.FVarSubst import Lean.Meta.Tactic.Subst
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro1__(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "caseValue"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 144, 12, 65, 131, 233, 76, 239)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4;
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal_default = (const lean_object*)&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal = (const lean_object*)&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "caseValues"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 31, 83, 94, 219, 75, 195, 44)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "list of values must not be empty"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5;
static const lean_string_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__6_value),LEAN_SCALAR_PTR_LITERAL(201, 154, 204, 143, 225, 235, 23, 70)}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_ks_55_; lean_object* v_vs_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_80_; 
v_ks_55_ = lean_ctor_get(v_x_51_, 0);
v_vs_56_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_80_ == 0)
{
v___x_58_ = v_x_51_;
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_vs_56_);
lean_inc(v_ks_55_);
lean_dec(v_x_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_ks_55_);
v___x_61_ = lean_nat_dec_lt(v_x_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_x_52_);
v___x_62_ = lean_array_push(v_ks_55_, v_x_53_);
v___x_63_ = lean_array_push(v_vs_56_, v_x_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_63_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_ks_55_, v_x_52_);
v___x_68_ = l_Lean_instBEqMVarId_beq(v_x_53_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_59_ == 0)
{
v___x_70_ = v___x_58_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_ks_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_vs_56_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_x_52_, v___x_71_);
lean_dec(v_x_52_);
v_x_51_ = v___x_70_;
v_x_52_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_array_fset(v_ks_55_, v_x_52_, v_x_53_);
v___x_76_ = lean_array_fset(v_vs_56_, v_x_52_, v_x_54_);
lean_dec(v_x_52_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_76_);
lean_ctor_set(v___x_58_, 0, v___x_75_);
v___x_78_ = v___x_58_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_81_, v___x_84_, v_k_82_, v_v_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(lean_object* v_x_87_, size_t v_x_88_, size_t v_x_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_es_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_es_92_ = lean_ctor_get(v_x_87_, 0);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_88_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_size(v_es_92_);
v___x_97_ = lean_nat_dec_lt(v_j_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_j_95_);
lean_dec(v_x_91_);
lean_dec(v_x_90_);
return v_x_87_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_es_92_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_x_87_, 0);
lean_dec(v_unused_137_);
v___x_99_ = v_x_87_;
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_v_101_; lean_object* v___x_102_; lean_object* v_xs_x27_103_; lean_object* v___y_105_; 
v_v_101_ = lean_array_fget(v_es_92_, v_j_95_);
v___x_102_ = lean_box(0);
v_xs_x27_103_ = lean_array_fset(v_es_92_, v_j_95_, v___x_102_);
switch(lean_obj_tag(v_v_101_))
{
case 0:
{
lean_object* v_key_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_121_; 
v_key_110_ = lean_ctor_get(v_v_101_, 0);
v_val_111_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_121_ == 0)
{
v___x_113_ = v_v_101_;
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_inc(v_key_110_);
lean_dec(v_v_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_instBEqMVarId_beq(v_x_90_, v_key_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_113_);
v___x_116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_110_, v_val_111_, v_x_90_, v_x_91_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_val_111_);
lean_dec(v_key_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_x_91_);
lean_ctor_set(v___x_113_, 0, v_x_90_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_91_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
}
}
}
case 1:
{
lean_object* v_node_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_134_; 
v_node_122_ = lean_ctor_get(v_v_101_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_134_ == 0)
{
v___x_124_ = v_v_101_;
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_node_122_);
lean_dec(v_v_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_usize_shift_right(v_x_88_, v___x_126_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_x_89_, v___x_128_);
v___x_130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_node_122_, v___x_127_, v___x_129_, v_x_90_, v_x_91_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v___y_105_ = v___x_132_;
goto v___jp_104_;
}
}
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_x_90_);
lean_ctor_set(v___x_135_, 1, v_x_91_);
v___y_105_ = v___x_135_;
goto v___jp_104_;
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_array_fset(v_xs_x27_103_, v_j_95_, v___y_105_);
lean_dec(v_j_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_159_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_159_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_159_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_158_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; uint8_t v___y_147_; size_t v___x_153_; uint8_t v___x_154_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_153_ = ((size_t)7ULL);
v___x_154_ = lean_usize_dec_le(v___x_153_, v_x_89_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
lean_object* v_ks_148_; lean_object* v_vs_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_ks_148_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_148_);
v_vs_149_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_149_);
lean_dec_ref(v_newNode_145_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_148_, v_vs_149_, v___x_150_, v___x_151_);
lean_dec_ref(v_vs_149_);
lean_dec_ref(v_ks_148_);
return v___x_152_;
}
else
{
return v_newNode_145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_160_, lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_entries_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_keys_161_);
v___x_166_ = lean_nat_dec_lt(v_i_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_163_);
return v_entries_164_;
}
else
{
lean_object* v_k_167_; lean_object* v_v_168_; uint64_t v___x_169_; size_t v_h_170_; size_t v___x_171_; lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v_h_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_k_167_ = lean_array_fget_borrowed(v_keys_161_, v_i_163_);
v_v_168_ = lean_array_fget_borrowed(v_vals_162_, v_i_163_);
v___x_169_ = l_Lean_instHashableMVarId_hash(v_k_167_);
v_h_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v_depth_160_, v___x_173_);
v___x_175_ = lean_usize_mul(v___x_171_, v___x_174_);
v_h_176_ = lean_usize_shift_right(v_h_170_, v___x_175_);
v___x_177_ = lean_nat_add(v_i_163_, v___x_172_);
lean_dec(v_i_163_);
lean_inc(v_v_168_);
lean_inc(v_k_167_);
v___x_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_entries_164_, v_h_176_, v_depth_160_, v_k_167_, v_v_168_);
v_i_163_ = v___x_177_;
v_entries_164_ = v___x_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_180_, lean_object* v_keys_181_, lean_object* v_vals_182_, lean_object* v_i_183_, lean_object* v_entries_184_){
_start:
{
size_t v_depth_boxed_185_; lean_object* v_res_186_; 
v_depth_boxed_185_ = lean_unbox_usize(v_depth_180_);
lean_dec(v_depth_180_);
v_res_186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_185_, v_keys_181_, v_vals_182_, v_i_183_, v_entries_184_);
lean_dec_ref(v_vals_182_);
lean_dec_ref(v_keys_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_2100__boxed_192_; size_t v_x_2101__boxed_193_; lean_object* v_res_194_; 
v_x_2100__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_x_2101__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_res_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_187_, v_x_2100__boxed_192_, v_x_2101__boxed_193_, v_x_190_, v_x_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_instHashableMVarId_hash(v_x_196_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_195_, v___x_199_, v___x_200_, v_x_196_, v_x_197_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(lean_object* v_mvarId_202_, lean_object* v_val_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_mctx_207_; lean_object* v_cache_208_; lean_object* v_zetaDeltaFVarIds_209_; lean_object* v_postponed_210_; lean_object* v_diag_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_240_; 
v___x_206_ = lean_st_ref_take(v___y_204_);
v_mctx_207_ = lean_ctor_get(v___x_206_, 0);
v_cache_208_ = lean_ctor_get(v___x_206_, 1);
v_zetaDeltaFVarIds_209_ = lean_ctor_get(v___x_206_, 2);
v_postponed_210_ = lean_ctor_get(v___x_206_, 3);
v_diag_211_ = lean_ctor_get(v___x_206_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_240_ == 0)
{
v___x_213_ = v___x_206_;
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_diag_211_);
lean_inc(v_postponed_210_);
lean_inc(v_zetaDeltaFVarIds_209_);
lean_inc(v_cache_208_);
lean_inc(v_mctx_207_);
lean_dec(v___x_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_240_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_depth_215_; lean_object* v_levelAssignDepth_216_; lean_object* v_lmvarCounter_217_; lean_object* v_mvarCounter_218_; lean_object* v_lDecls_219_; lean_object* v_decls_220_; lean_object* v_userNames_221_; lean_object* v_lAssignment_222_; lean_object* v_eAssignment_223_; lean_object* v_dAssignment_224_; lean_object* v_instanceTypedMVars_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_215_ = lean_ctor_get(v_mctx_207_, 0);
v_levelAssignDepth_216_ = lean_ctor_get(v_mctx_207_, 1);
v_lmvarCounter_217_ = lean_ctor_get(v_mctx_207_, 2);
v_mvarCounter_218_ = lean_ctor_get(v_mctx_207_, 3);
v_lDecls_219_ = lean_ctor_get(v_mctx_207_, 4);
v_decls_220_ = lean_ctor_get(v_mctx_207_, 5);
v_userNames_221_ = lean_ctor_get(v_mctx_207_, 6);
v_lAssignment_222_ = lean_ctor_get(v_mctx_207_, 7);
v_eAssignment_223_ = lean_ctor_get(v_mctx_207_, 8);
v_dAssignment_224_ = lean_ctor_get(v_mctx_207_, 9);
v_instanceTypedMVars_225_ = lean_ctor_get(v_mctx_207_, 10);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_207_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_207_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_instanceTypedMVars_225_);
lean_inc(v_dAssignment_224_);
lean_inc(v_eAssignment_223_);
lean_inc(v_lAssignment_222_);
lean_inc(v_userNames_221_);
lean_inc(v_decls_220_);
lean_inc(v_lDecls_219_);
lean_inc(v_mvarCounter_218_);
lean_inc(v_lmvarCounter_217_);
lean_inc(v_levelAssignDepth_216_);
lean_inc(v_depth_215_);
lean_dec(v_mctx_207_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_eAssignment_223_, v_mvarId_202_, v_val_203_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_instanceTypedMVars_225_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_231_);
v___x_233_ = v___x_213_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_210_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_211_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_204_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3));
v___x_254_ = l_Lean_mkConst(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_unsigned_to_nat(5u);
v___x_260_ = lean_mk_empty_array_with_capacity(v___x_259_);
v___x_261_ = lean_array_push(v___x_260_, v___x_258_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(lean_object* v_mvarId_262_, lean_object* v_value_263_, lean_object* v_fvarId_264_, lean_object* v_hName_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
lean_inc(v_mvarId_262_);
v___x_271_ = l_Lean_MVarId_getTag(v_mvarId_262_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1));
lean_inc(v_mvarId_262_);
v___x_274_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_262_, v___x_273_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; 
lean_dec_ref_known(v___x_274_, 1);
lean_inc(v_mvarId_262_);
v___x_275_ = l_Lean_MVarId_getType(v_mvarId_262_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = l_Lean_Meta_normLitValue(v_value_263_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
v___x_279_ = l_Lean_mkFVar(v_fvarId_264_);
v___x_280_ = l_Lean_Meta_mkEq(v___x_279_, v_a_278_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_n(v_a_281_, 3);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4);
v___x_283_ = l_Lean_Expr_app___override(v___x_282_, v_a_281_);
v___x_284_ = 0;
lean_inc(v_a_276_);
lean_inc(v_hName_265_);
v___x_285_ = l_Lean_mkForall(v_hName_265_, v___x_284_, v_a_281_, v_a_276_);
lean_inc(v_a_272_);
v___x_286_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_285_, v_a_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_mkForall(v_hName_265_, v___x_284_, v___x_283_, v_a_276_);
v___x_289_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_288_, v_a_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_n(v_a_290_, 2);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6));
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v_a_281_);
lean_inc(v_a_287_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_a_287_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_a_290_);
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7);
v___x_297_ = lean_array_push(v___x_296_, v___x_293_);
v___x_298_ = lean_array_push(v___x_297_, v___x_292_);
v___x_299_ = lean_array_push(v___x_298_, v___x_294_);
v___x_300_ = lean_array_push(v___x_299_, v___x_295_);
v___x_301_ = l_Lean_Meta_mkAppOptM(v___x_291_, v___x_300_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_262_, v_a_302_, v___y_267_);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_303_, 0);
lean_dec(v_unused_314_);
v___x_305_ = v___x_303_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_dec(v___x_303_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_307_ = l_Lean_Expr_mvarId_x21(v_a_287_);
lean_dec(v_a_287_);
v___x_308_ = l_Lean_Expr_mvarId_x21(v_a_290_);
lean_dec(v_a_290_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_311_ = v___x_305_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_a_290_);
lean_dec(v_a_287_);
lean_dec(v_mvarId_262_);
v_a_315_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_301_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_301_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_a_287_);
lean_dec(v_a_281_);
lean_dec(v_mvarId_262_);
v_a_323_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_289_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_289_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v___x_283_);
lean_dec(v_a_281_);
lean_dec(v_a_276_);
lean_dec(v_a_272_);
lean_dec(v_hName_265_);
lean_dec(v_mvarId_262_);
v_a_331_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_286_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_286_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_a_276_);
lean_dec(v_a_272_);
lean_dec(v_hName_265_);
lean_dec(v_mvarId_262_);
v_a_339_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_280_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_280_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_276_);
lean_dec(v_a_272_);
lean_dec(v_hName_265_);
lean_dec(v_fvarId_264_);
lean_dec(v_mvarId_262_);
v_a_347_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_277_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_277_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_a_272_);
lean_dec(v_hName_265_);
lean_dec(v_fvarId_264_);
lean_dec_ref(v_value_263_);
lean_dec(v_mvarId_262_);
v_a_355_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_275_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_275_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_a_272_);
lean_dec(v_hName_265_);
lean_dec(v_fvarId_264_);
lean_dec_ref(v_value_263_);
lean_dec(v_mvarId_262_);
v_a_363_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_274_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_274_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_hName_265_);
lean_dec(v_fvarId_264_);
lean_dec_ref(v_value_263_);
lean_dec(v_mvarId_262_);
v_a_371_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_271_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_271_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed(lean_object* v_mvarId_379_, lean_object* v_value_380_, lean_object* v_fvarId_381_, lean_object* v_hName_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(v_mvarId_379_, v_value_380_, v_fvarId_381_, v_hName_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(lean_object* v_mvarId_389_, lean_object* v_fvarId_390_, lean_object* v_value_391_, lean_object* v_hName_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; 
lean_inc(v_mvarId_389_);
v___f_398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed), 9, 4);
lean_closure_set(v___f_398_, 0, v_mvarId_389_);
lean_closure_set(v___f_398_, 1, v_value_391_);
lean_closure_set(v___f_398_, 2, v_fvarId_390_);
lean_closure_set(v___f_398_, 3, v_hName_392_);
v___x_399_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_389_, v___f_398_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___boxed(lean_object* v_mvarId_400_, lean_object* v_fvarId_401_, lean_object* v_value_402_, lean_object* v_hName_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(v_mvarId_400_, v_fvarId_401_, v_value_402_, v_hName_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(lean_object* v_mvarId_410_, lean_object* v_val_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_410_, v_val_411_, v___y_413_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___boxed(lean_object* v_mvarId_418_, lean_object* v_val_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(v_mvarId_418_, v_val_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_x_427_, v_x_428_, v_x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, size_t v_x_433_, size_t v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_432_, v_x_433_, v_x_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
size_t v_x_2628__boxed_444_; size_t v_x_2629__boxed_445_; lean_object* v_res_446_; 
v_x_2628__boxed_444_ = lean_unbox_usize(v_x_440_);
lean_dec(v_x_440_);
v_x_2629__boxed_445_ = lean_unbox_usize(v_x_441_);
lean_dec(v_x_441_);
v_res_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(v_00_u03b2_438_, v_x_439_, v_x_2628__boxed_444_, v_x_2629__boxed_445_, v_x_442_, v_x_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_447_, lean_object* v_n_448_, lean_object* v_k_449_, lean_object* v_v_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v_n_448_, v_k_449_, v_v_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_452_, size_t v_depth_453_, lean_object* v_keys_454_, lean_object* v_vals_455_, lean_object* v_heq_456_, lean_object* v_i_457_, lean_object* v_entries_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_453_, v_keys_454_, v_vals_455_, v_i_457_, v_entries_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_460_, lean_object* v_depth_461_, lean_object* v_keys_462_, lean_object* v_vals_463_, lean_object* v_heq_464_, lean_object* v_i_465_, lean_object* v_entries_466_){
_start:
{
size_t v_depth_boxed_467_; lean_object* v_res_468_; 
v_depth_boxed_467_ = lean_unbox_usize(v_depth_461_);
lean_dec(v_depth_461_);
v_res_468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_460_, v_depth_boxed_467_, v_keys_462_, v_vals_463_, v_heq_464_, v_i_465_, v_entries_466_);
lean_dec_ref(v_vals_463_);
lean_dec_ref(v_keys_462_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_470_, v_x_471_, v_x_472_, v_x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3));
v___x_490_ = l_Lean_MessageData_ofFormat(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(lean_object* v_fvarId_496_, lean_object* v_hNamePrefix_497_, uint8_t v_needHyps_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v___x_509_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1));
v___x_510_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5);
v___x_511_ = l_Lean_Meta_throwTacticEx___redArg(v___x_509_, v_a_500_, v___x_510_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_511_;
}
else
{
lean_object* v_head_512_; lean_object* v_tail_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_head_512_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_head_512_);
v_tail_513_ = lean_ctor_get(v_a_501_, 1);
lean_inc(v_tail_513_);
lean_dec_ref_known(v_a_501_, 2);
lean_inc(v_a_499_);
lean_inc(v_hNamePrefix_497_);
v___x_514_ = lean_name_append_index_after(v_hNamePrefix_497_, v_a_499_);
lean_inc(v_fvarId_496_);
v___x_515_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(v_a_500_, v_fvarId_496_, v_head_512_, v___x_514_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v_fst_517_ = lean_ctor_get(v_a_516_, 0);
lean_inc_n(v_fst_517_, 2);
v_snd_518_ = lean_ctor_get(v_a_516_, 1);
lean_inc(v_snd_518_);
lean_dec(v_a_516_);
v___x_519_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7));
lean_inc(v_a_499_);
v___x_520_ = lean_name_append_index_after(v___x_519_, v_a_499_);
v___x_521_ = l_Lean_Meta_appendTagSuffix(v_fst_517_, v___x_520_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v___x_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
lean_dec_ref_known(v___x_521_, 1);
v___x_522_ = l_Lean_MVarId_tryClearMany(v_fst_517_, v_a_502_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint8_t v___x_524_; lean_object* v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = 1;
v___x_525_ = l_Lean_Meta_introSubstEq(v_a_523_, v___x_524_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_fst_527_ = lean_ctor_get(v_a_526_, 0);
lean_inc(v_fst_527_);
v_snd_528_ = lean_ctor_get(v_a_526_, 1);
lean_inc(v_snd_528_);
lean_dec(v_a_526_);
v___x_529_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0));
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v_snd_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set(v___x_530_, 2, v_fst_527_);
v___x_531_ = lean_array_push(v_a_503_, v___x_530_);
if (v_needHyps_498_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_MVarId_intro1__(v_snd_518_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v_fst_533_ = v_a_502_;
v_snd_534_ = v_a_566_;
v___y_535_ = v_a_504_;
v___y_536_ = v_a_505_;
v___y_537_ = v_a_506_;
v___y_538_ = v_a_507_;
goto v___jp_532_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v___x_531_);
lean_dec(v_tail_513_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_567_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_intro1Core(v_snd_518_, v___x_524_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v_fst_577_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_snd_578_);
lean_dec(v_a_576_);
v___x_579_ = lean_array_push(v_a_502_, v_fst_577_);
v_fst_533_ = v___x_579_;
v_snd_534_ = v_snd_578_;
v___y_535_ = v_a_504_;
v___y_536_ = v_a_505_;
v___y_537_ = v_a_506_;
v___y_538_ = v_a_507_;
goto v___jp_532_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___x_531_);
lean_dec(v_tail_513_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_580_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_575_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_575_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
v___jp_532_:
{
if (lean_obj_tag(v_tail_513_) == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_a_499_, v___x_539_);
lean_dec(v_a_499_);
v___x_541_ = lean_name_append_index_after(v___x_519_, v___x_540_);
lean_inc(v_snd_534_);
v___x_542_ = l_Lean_Meta_appendTagSuffix(v_snd_534_, v___x_541_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_552_; 
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_553_);
v___x_544_ = v___x_542_;
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
else
{
lean_dec(v___x_542_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_546_ = lean_box(0);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v_snd_534_);
lean_ctor_set(v___x_547_, 1, v_fst_533_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = lean_array_push(v___x_531_, v___x_547_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_550_ = v___x_544_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_snd_534_);
lean_dec_ref(v_fst_533_);
lean_dec_ref(v___x_531_);
v_a_554_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_542_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_542_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_a_499_, v___x_562_);
lean_dec(v_a_499_);
v_a_499_ = v___x_563_;
v_a_500_ = v_snd_534_;
v_a_501_ = v_tail_513_;
v_a_502_ = v_fst_533_;
v_a_503_ = v___x_531_;
v_a_504_ = v___y_535_;
v_a_505_ = v___y_536_;
v_a_506_ = v___y_537_;
v_a_507_ = v___y_538_;
goto _start;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_snd_518_);
lean_dec(v_tail_513_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_588_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_525_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_525_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_snd_518_);
lean_dec(v_tail_513_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_596_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_522_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_522_);
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
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_snd_518_);
lean_dec(v_fst_517_);
lean_dec(v_tail_513_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_604_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_521_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_521_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
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
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_tail_513_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
lean_dec(v_hNamePrefix_497_);
lean_dec(v_fvarId_496_);
v_a_612_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_515_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_515_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___boxed(lean_object* v_fvarId_620_, lean_object* v_hNamePrefix_621_, lean_object* v_needHyps_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
uint8_t v_needHyps_boxed_633_; lean_object* v_res_634_; 
v_needHyps_boxed_633_ = lean_unbox(v_needHyps_622_);
v_res_634_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(v_fvarId_620_, v_hNamePrefix_621_, v_needHyps_boxed_633_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object* v_mvarId_635_, lean_object* v_fvarId_636_, lean_object* v_values_637_, lean_object* v_hNamePrefix_638_, uint8_t v_needHyps_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_array_to_list(v_values_637_);
v___x_647_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0));
v___x_648_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(v_fvarId_636_, v_hNamePrefix_638_, v_needHyps_639_, v___x_645_, v_mvarId_635_, v___x_646_, v___x_647_, v___x_647_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object* v_mvarId_649_, lean_object* v_fvarId_650_, lean_object* v_values_651_, lean_object* v_hNamePrefix_652_, lean_object* v_needHyps_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
uint8_t v_needHyps_boxed_659_; lean_object* v_res_660_; 
v_needHyps_boxed_659_ = lean_unbox(v_needHyps_653_);
v_res_660_ = l_Lean_Meta_caseValues(v_mvarId_649_, v_fvarId_650_, v_values_651_, v_hNamePrefix_652_, v_needHyps_boxed_659_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_660_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_CaseValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_CaseValues(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_CaseValues(builtin);
}
#ifdef __cplusplus
}
#endif
