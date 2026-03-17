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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro1__(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedFVarSubst_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedMVarId_default;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2;
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
static lean_once_cell_t l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal;
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
static const lean_array_object l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__8 = (const lean_object*)&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__8_value;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_86_ = ((size_t)5ULL);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_shift_left(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; 
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_91_ = lean_usize_sub(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(lean_object* v_x_93_, size_t v_x_94_, size_t v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v_j_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_es_98_ = lean_ctor_get(v_x_93_, 0);
v___x_99_ = ((size_t)5ULL);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_102_ = lean_usize_land(v_x_94_, v___x_101_);
v_j_103_ = lean_usize_to_nat(v___x_102_);
v___x_104_ = lean_array_get_size(v_es_98_);
v___x_105_ = lean_nat_dec_lt(v_j_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v_j_103_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_x_93_;
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_142_; 
lean_inc_ref(v_es_98_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_93_, 0);
lean_dec(v_unused_143_);
v___x_107_ = v_x_93_;
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_x_93_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_xs_x27_111_; lean_object* v___y_113_; 
v_v_109_ = lean_array_fget(v_es_98_, v_j_103_);
v___x_110_ = lean_box(0);
v_xs_x27_111_ = lean_array_fset(v_es_98_, v_j_103_, v___x_110_);
switch(lean_obj_tag(v_v_109_))
{
case 0:
{
lean_object* v_key_118_; lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v_key_118_ = lean_ctor_get(v_v_109_, 0);
v_val_119_ = lean_ctor_get(v_v_109_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_129_ == 0)
{
v___x_121_ = v_v_109_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_inc(v_key_118_);
lean_dec(v_v_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_instBEqMVarId_beq(v_x_96_, v_key_118_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_del_object(v___x_121_);
v___x_124_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_118_, v_val_119_, v_x_96_, v_x_97_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_val_119_);
lean_dec(v_key_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_x_97_);
lean_ctor_set(v___x_121_, 0, v_x_96_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_x_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_x_97_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_113_ = v___x_127_;
goto v___jp_112_;
}
}
}
}
case 1:
{
lean_object* v_node_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v_node_130_ = lean_ctor_get(v_v_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_132_ = v_v_109_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_node_130_);
lean_dec(v_v_109_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_134_ = lean_usize_shift_right(v_x_94_, v___x_99_);
v___x_135_ = lean_usize_add(v_x_95_, v___x_100_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_node_130_, v___x_134_, v___x_135_, v_x_96_, v_x_97_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_136_);
v___x_138_ = v___x_132_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v___y_113_ = v___x_138_;
goto v___jp_112_;
}
}
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_x_96_);
lean_ctor_set(v___x_141_, 1, v_x_97_);
v___y_113_ = v___x_141_;
goto v___jp_112_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_array_fset(v_xs_x27_111_, v_j_103_, v___y_113_);
lean_dec(v_j_103_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_114_);
v___x_116_ = v___x_107_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
else
{
lean_object* v_ks_144_; lean_object* v_vs_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_165_; 
v_ks_144_ = lean_ctor_get(v_x_93_, 0);
v_vs_145_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_165_ == 0)
{
v___x_147_ = v_x_93_;
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_vs_145_);
lean_inc(v_ks_144_);
lean_dec(v_x_93_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_ks_144_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_vs_145_);
v___x_150_ = v_reuseFailAlloc_164_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_newNode_151_; uint8_t v___y_153_; size_t v___x_159_; uint8_t v___x_160_; 
v_newNode_151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v___x_150_, v_x_96_, v_x_97_);
v___x_159_ = ((size_t)7ULL);
v___x_160_ = lean_usize_dec_le(v___x_159_, v_x_95_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_151_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___y_153_ = v___x_163_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_ks_154_ = lean_ctor_get(v_newNode_151_, 0);
lean_inc_ref(v_ks_154_);
v_vs_155_ = lean_ctor_get(v_newNode_151_, 1);
lean_inc_ref(v_vs_155_);
lean_dec_ref(v_newNode_151_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_x_95_, v_ks_154_, v_vs_155_, v___x_156_, v___x_157_);
lean_dec_ref(v_vs_155_);
lean_dec_ref(v_ks_154_);
return v___x_158_;
}
else
{
return v_newNode_151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_166_, lean_object* v_keys_167_, lean_object* v_vals_168_, lean_object* v_i_169_, lean_object* v_entries_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v_keys_167_);
v___x_172_ = lean_nat_dec_lt(v_i_169_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_i_169_);
return v_entries_170_;
}
else
{
lean_object* v_k_173_; lean_object* v_v_174_; uint64_t v___x_175_; size_t v_h_176_; size_t v___x_177_; lean_object* v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v_h_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_k_173_ = lean_array_fget_borrowed(v_keys_167_, v_i_169_);
v_v_174_ = lean_array_fget_borrowed(v_vals_168_, v_i_169_);
v___x_175_ = l_Lean_instHashableMVarId_hash(v_k_173_);
v_h_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_sub(v_depth_166_, v___x_179_);
v___x_181_ = lean_usize_mul(v___x_177_, v___x_180_);
v_h_182_ = lean_usize_shift_right(v_h_176_, v___x_181_);
v___x_183_ = lean_nat_add(v_i_169_, v___x_178_);
lean_dec(v_i_169_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v___x_184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_entries_170_, v_h_182_, v_depth_166_, v_k_173_, v_v_174_);
v_i_169_ = v___x_183_;
v_entries_170_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_186_, lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_entries_190_){
_start:
{
size_t v_depth_boxed_191_; lean_object* v_res_192_; 
v_depth_boxed_191_ = lean_unbox_usize(v_depth_186_);
lean_dec(v_depth_186_);
v_res_192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_191_, v_keys_187_, v_vals_188_, v_i_189_, v_entries_190_);
lean_dec_ref(v_vals_188_);
lean_dec_ref(v_keys_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_2172__boxed_198_; size_t v_x_2173__boxed_199_; lean_object* v_res_200_; 
v_x_2172__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_2173__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_193_, v_x_2172__boxed_198_, v_x_2173__boxed_199_, v_x_196_, v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_204_ = l_Lean_instHashableMVarId_hash(v_x_202_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_201_, v___x_205_, v___x_206_, v_x_202_, v_x_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(lean_object* v_mvarId_208_, lean_object* v_val_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_mctx_213_; lean_object* v_cache_214_; lean_object* v_zetaDeltaFVarIds_215_; lean_object* v_postponed_216_; lean_object* v_diag_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_244_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_mctx_213_ = lean_ctor_get(v___x_212_, 0);
v_cache_214_ = lean_ctor_get(v___x_212_, 1);
v_zetaDeltaFVarIds_215_ = lean_ctor_get(v___x_212_, 2);
v_postponed_216_ = lean_ctor_get(v___x_212_, 3);
v_diag_217_ = lean_ctor_get(v___x_212_, 4);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_244_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_244_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_diag_217_);
lean_inc(v_postponed_216_);
lean_inc(v_zetaDeltaFVarIds_215_);
lean_inc(v_cache_214_);
lean_inc(v_mctx_213_);
lean_dec(v___x_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_244_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_depth_221_; lean_object* v_levelAssignDepth_222_; lean_object* v_mvarCounter_223_; lean_object* v_lDepth_224_; lean_object* v_decls_225_; lean_object* v_userNames_226_; lean_object* v_lAssignment_227_; lean_object* v_eAssignment_228_; lean_object* v_dAssignment_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_depth_221_ = lean_ctor_get(v_mctx_213_, 0);
v_levelAssignDepth_222_ = lean_ctor_get(v_mctx_213_, 1);
v_mvarCounter_223_ = lean_ctor_get(v_mctx_213_, 2);
v_lDepth_224_ = lean_ctor_get(v_mctx_213_, 3);
v_decls_225_ = lean_ctor_get(v_mctx_213_, 4);
v_userNames_226_ = lean_ctor_get(v_mctx_213_, 5);
v_lAssignment_227_ = lean_ctor_get(v_mctx_213_, 6);
v_eAssignment_228_ = lean_ctor_get(v_mctx_213_, 7);
v_dAssignment_229_ = lean_ctor_get(v_mctx_213_, 8);
v_isSharedCheck_243_ = !lean_is_exclusive(v_mctx_213_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v_mctx_213_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_dAssignment_229_);
lean_inc(v_eAssignment_228_);
lean_inc(v_lAssignment_227_);
lean_inc(v_userNames_226_);
lean_inc(v_decls_225_);
lean_inc(v_lDepth_224_);
lean_inc(v_mvarCounter_223_);
lean_inc(v_levelAssignDepth_222_);
lean_inc(v_depth_221_);
lean_dec(v_mctx_213_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_eAssignment_228_, v_mvarId_208_, v_val_209_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 7, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_depth_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_levelAssignDepth_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_mvarCounter_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_lDepth_224_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_decls_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_userNames_226_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_lAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_dAssignment_229_);
v___x_235_ = v_reuseFailAlloc_242_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_235_);
v___x_237_ = v___x_219_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_zetaDeltaFVarIds_215_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_postponed_216_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_diag_217_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_set(v___y_210_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg___boxed(lean_object* v_mvarId_245_, lean_object* v_val_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_245_, v_val_246_, v___y_247_);
lean_dec(v___y_247_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__3));
v___x_258_ = l_Lean_mkConst(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_unsigned_to_nat(5u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_array_push(v___x_264_, v___x_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(lean_object* v_mvarId_266_, lean_object* v_value_267_, lean_object* v_fvarId_268_, lean_object* v_hName_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc(v_mvarId_266_);
v___x_275_ = l_Lean_MVarId_getTag(v_mvarId_266_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__1));
lean_inc(v_mvarId_266_);
v___x_278_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_266_, v___x_277_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v___x_278_);
lean_inc(v_mvarId_266_);
v___x_279_ = l_Lean_MVarId_getType(v_mvarId_266_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref(v___x_279_);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_281_ = l_Lean_Meta_normLitValue(v_value_267_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref(v___x_281_);
v___x_283_ = l_Lean_mkFVar(v_fvarId_268_);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_284_ = l_Lean_Meta_mkEq(v___x_283_, v_a_282_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__4);
lean_inc(v_a_285_);
v___x_287_ = l_Lean_Expr_app___override(v___x_286_, v_a_285_);
v___x_288_ = 0;
lean_inc(v_a_280_);
lean_inc(v_a_285_);
lean_inc(v_hName_269_);
v___x_289_ = l_Lean_mkForall(v_hName_269_, v___x_288_, v_a_285_, v_a_280_);
lean_inc_ref(v___y_270_);
lean_inc(v_a_276_);
v___x_290_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_289_, v_a_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref(v___x_290_);
v___x_292_ = l_Lean_mkForall(v_hName_269_, v___x_288_, v___x_287_, v_a_280_);
lean_inc_ref(v___y_270_);
v___x_293_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_292_, v_a_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v___x_293_);
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__6));
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_a_285_);
lean_inc(v_a_291_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_291_);
lean_inc(v_a_294_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_a_294_);
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___closed__7);
v___x_301_ = lean_array_push(v___x_300_, v___x_297_);
v___x_302_ = lean_array_push(v___x_301_, v___x_296_);
v___x_303_ = lean_array_push(v___x_302_, v___x_298_);
v___x_304_ = lean_array_push(v___x_303_, v___x_299_);
lean_inc(v___y_271_);
v___x_305_ = l_Lean_Meta_mkAppOptM(v___x_295_, v___x_304_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
v___x_307_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_266_, v_a_306_, v___y_271_);
lean_dec(v___y_271_);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_307_, 0);
lean_dec(v_unused_318_);
v___x_309_ = v___x_307_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_dec(v___x_307_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_311_ = l_Lean_Expr_mvarId_x21(v_a_291_);
lean_dec(v_a_291_);
v___x_312_ = l_Lean_Expr_mvarId_x21(v_a_294_);
lean_dec(v_a_294_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_313_);
v___x_315_ = v___x_309_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_a_294_);
lean_dec(v_a_291_);
lean_dec(v___y_271_);
lean_dec(v_mvarId_266_);
v_a_319_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_305_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_305_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_a_291_);
lean_dec(v_a_285_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_mvarId_266_);
v_a_327_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_293_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_293_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec_ref(v___x_287_);
lean_dec(v_a_285_);
lean_dec(v_a_280_);
lean_dec(v_a_276_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_mvarId_266_);
v_a_335_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_290_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_290_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_280_);
lean_dec(v_a_276_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_mvarId_266_);
v_a_343_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_284_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_284_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_a_280_);
lean_dec(v_a_276_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_fvarId_268_);
lean_dec(v_mvarId_266_);
v_a_351_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_281_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_281_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_276_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_fvarId_268_);
lean_dec_ref(v_value_267_);
lean_dec(v_mvarId_266_);
v_a_359_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_279_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_279_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_a_276_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_fvarId_268_);
lean_dec_ref(v_value_267_);
lean_dec(v_mvarId_266_);
v_a_367_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_278_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_278_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_hName_269_);
lean_dec(v_fvarId_268_);
lean_dec_ref(v_value_267_);
lean_dec(v_mvarId_266_);
v_a_375_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_275_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_275_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed(lean_object* v_mvarId_383_, lean_object* v_value_384_, lean_object* v_fvarId_385_, lean_object* v_hName_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0(v_mvarId_383_, v_value_384_, v_fvarId_385_, v_hName_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(lean_object* v_mvarId_393_, lean_object* v_fvarId_394_, lean_object* v_value_395_, lean_object* v_hName_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___f_402_; lean_object* v___x_403_; 
lean_inc(v_mvarId_393_);
v___f_402_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___lam__0___boxed), 9, 4);
lean_closure_set(v___f_402_, 0, v_mvarId_393_);
lean_closure_set(v___f_402_, 1, v_value_395_);
lean_closure_set(v___f_402_, 2, v_fvarId_394_);
lean_closure_set(v___f_402_, 3, v_hName_396_);
v___x_403_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__1___redArg(v_mvarId_393_, v___f_402_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue___boxed(lean_object* v_mvarId_404_, lean_object* v_fvarId_405_, lean_object* v_value_406_, lean_object* v_hName_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(v_mvarId_404_, v_fvarId_405_, v_value_406_, v_hName_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(lean_object* v_mvarId_414_, lean_object* v_val_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___redArg(v_mvarId_414_, v_val_415_, v___y_417_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0___boxed(lean_object* v_mvarId_422_, lean_object* v_val_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0(v_mvarId_422_, v_val_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0(lean_object* v_00_u03b2_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0___redArg(v_x_431_, v_x_432_, v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, size_t v_x_437_, size_t v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___redArg(v_x_436_, v_x_437_, v_x_438_, v_x_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_2718__boxed_448_; size_t v_x_2719__boxed_449_; lean_object* v_res_450_; 
v_x_2718__boxed_448_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_2719__boxed_449_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2(v_00_u03b2_442_, v_x_443_, v_x_2718__boxed_448_, v_x_2719__boxed_449_, v_x_446_, v_x_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_451_, lean_object* v_n_452_, lean_object* v_k_453_, lean_object* v_v_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3___redArg(v_n_452_, v_k_453_, v_v_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_456_, size_t v_depth_457_, lean_object* v_keys_458_, lean_object* v_vals_459_, lean_object* v_heq_460_, lean_object* v_i_461_, lean_object* v_entries_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_457_, v_keys_458_, v_vals_459_, v_i_461_, v_entries_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_464_, lean_object* v_depth_465_, lean_object* v_keys_466_, lean_object* v_vals_467_, lean_object* v_heq_468_, lean_object* v_i_469_, lean_object* v_entries_470_){
_start:
{
size_t v_depth_boxed_471_; lean_object* v_res_472_; 
v_depth_boxed_471_ = lean_unbox_usize(v_depth_465_);
lean_dec(v_depth_465_);
v_res_472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_464_, v_depth_boxed_471_, v_keys_466_, v_vals_467_, v_heq_468_, v_i_469_, v_entries_470_);
lean_dec_ref(v_vals_467_);
lean_dec_ref(v_keys_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_474_, v_x_475_, v_x_476_, v_x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = l_Lean_Meta_instInhabitedFVarSubst_default;
v___x_482_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__0));
v___x_483_ = l_Lean_instInhabitedMVarId_default;
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_481_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal_default(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1, &l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1_once, _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal_default___closed__1);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_instInhabitedCaseValuesSubgoal_default;
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__3));
v___x_494_ = l_Lean_MessageData_ofFormat(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__4);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(lean_object* v_fvarId_502_, lean_object* v_hNamePrefix_503_, uint8_t v_needHyps_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_a_507_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__1));
v___x_516_ = lean_obj_once(&l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5, &l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5_once, _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__5);
v___x_517_ = l_Lean_Meta_throwTacticEx___redArg(v___x_515_, v_a_506_, v___x_516_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v___x_517_;
}
else
{
lean_object* v_head_518_; lean_object* v_tail_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_head_518_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_head_518_);
v_tail_519_ = lean_ctor_get(v_a_507_, 1);
lean_inc(v_tail_519_);
lean_dec_ref(v_a_507_);
lean_inc(v_a_505_);
lean_inc(v_hNamePrefix_503_);
v___x_520_ = lean_name_append_index_after(v_hNamePrefix_503_, v_a_505_);
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc_ref(v_a_510_);
lean_inc(v_fvarId_502_);
v___x_521_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValue(v_a_506_, v_fvarId_502_, v_head_518_, v___x_520_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v_fst_523_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_fst_523_);
v_snd_524_ = lean_ctor_get(v_a_522_, 1);
lean_inc(v_snd_524_);
lean_dec(v_a_522_);
v___x_525_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__7));
lean_inc(v_a_505_);
v___x_526_ = lean_name_append_index_after(v___x_525_, v_a_505_);
lean_inc(v_fst_523_);
v___x_527_ = l_Lean_Meta_appendTagSuffix(v_fst_523_, v___x_526_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_527_);
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc_ref(v_a_510_);
v___x_528_ = l_Lean_MVarId_tryClearMany(v_fst_523_, v_a_508_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = 1;
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc_ref(v_a_510_);
v___x_531_ = l_Lean_Meta_introSubstEq(v_a_529_, v___x_530_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v_fst_533_ = lean_ctor_get(v_a_532_, 0);
lean_inc(v_fst_533_);
v_snd_534_ = lean_ctor_get(v_a_532_, 1);
lean_inc(v_snd_534_);
lean_dec(v_a_532_);
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__8));
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v_snd_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v_fst_533_);
v___x_537_ = lean_array_push(v_a_509_, v___x_536_);
if (v_needHyps_504_ == 0)
{
lean_object* v___x_571_; 
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc_ref(v_a_510_);
v___x_571_ = l_Lean_MVarId_intro1__(v_snd_524_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
v_fst_539_ = v_a_508_;
v_snd_540_ = v_a_572_;
v___y_541_ = v_a_510_;
v___y_542_ = v_a_511_;
v___y_543_ = v_a_512_;
v___y_544_ = v_a_513_;
goto v___jp_538_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v___x_537_);
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_573_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v___x_581_; 
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc_ref(v_a_510_);
v___x_581_ = l_Lean_Meta_intro1Core(v_snd_524_, v___x_530_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___x_585_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_581_);
v_fst_583_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_fst_583_);
v_snd_584_ = lean_ctor_get(v_a_582_, 1);
lean_inc(v_snd_584_);
lean_dec(v_a_582_);
v___x_585_ = lean_array_push(v_a_508_, v_fst_583_);
v_fst_539_ = v___x_585_;
v_snd_540_ = v_snd_584_;
v___y_541_ = v_a_510_;
v___y_542_ = v_a_511_;
v___y_543_ = v_a_512_;
v___y_544_ = v_a_513_;
goto v___jp_538_;
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v___x_537_);
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_586_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_581_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_581_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
v___jp_538_:
{
if (lean_obj_tag(v_tail_519_) == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_a_505_, v___x_545_);
lean_dec(v_a_505_);
v___x_547_ = lean_name_append_index_after(v___x_525_, v___x_546_);
lean_inc(v_snd_540_);
v___x_548_ = l_Lean_Meta_appendTagSuffix(v_snd_540_, v___x_547_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_548_, 0);
lean_dec(v_unused_559_);
v___x_550_ = v___x_548_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_dec(v___x_548_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v_snd_540_);
lean_ctor_set(v___x_553_, 1, v_fst_539_);
lean_ctor_set(v___x_553_, 2, v___x_552_);
v___x_554_ = lean_array_push(v___x_537_, v___x_553_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_snd_540_);
lean_dec_ref(v_fst_539_);
lean_dec_ref(v___x_537_);
v_a_560_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_548_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_548_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_a_505_, v___x_568_);
lean_dec(v_a_505_);
v_a_505_ = v___x_569_;
v_a_506_ = v_snd_540_;
v_a_507_ = v_tail_519_;
v_a_508_ = v_fst_539_;
v_a_509_ = v___x_537_;
v_a_510_ = v___y_541_;
v_a_511_ = v___y_542_;
v_a_512_ = v___y_543_;
v_a_513_ = v___y_544_;
goto _start;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_snd_524_);
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_594_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_531_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_531_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_snd_524_);
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_602_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_528_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_528_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_snd_524_);
lean_dec(v_fst_523_);
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_610_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_527_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_527_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_tail_519_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_505_);
lean_dec(v_hNamePrefix_503_);
lean_dec(v_fvarId_502_);
v_a_618_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_521_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_521_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
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
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___boxed(lean_object* v_fvarId_626_, lean_object* v_hNamePrefix_627_, lean_object* v_needHyps_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
uint8_t v_needHyps_boxed_639_; lean_object* v_res_640_; 
v_needHyps_boxed_639_ = lean_unbox(v_needHyps_628_);
v_res_640_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(v_fvarId_626_, v_hNamePrefix_627_, v_needHyps_boxed_639_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object* v_mvarId_641_, lean_object* v_fvarId_642_, lean_object* v_values_643_, lean_object* v_hNamePrefix_644_, uint8_t v_needHyps_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_array_to_list(v_values_643_);
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop___closed__8));
v___x_654_ = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValues_loop(v_fvarId_642_, v_hNamePrefix_644_, v_needHyps_645_, v___x_651_, v_mvarId_641_, v___x_652_, v___x_653_, v___x_653_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object* v_mvarId_655_, lean_object* v_fvarId_656_, lean_object* v_values_657_, lean_object* v_hNamePrefix_658_, lean_object* v_needHyps_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
uint8_t v_needHyps_boxed_665_; lean_object* v_res_666_; 
v_needHyps_boxed_665_ = lean_unbox(v_needHyps_659_);
v_res_666_ = l_Lean_Meta_caseValues(v_mvarId_655_, v_fvarId_656_, v_values_657_, v_hNamePrefix_658_, v_needHyps_boxed_665_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v_res_666_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_CaseValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCaseValuesSubgoal_default = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal_default);
l_Lean_Meta_instInhabitedCaseValuesSubgoal = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal);
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
