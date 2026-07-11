// Lean compiler output
// Module: Lean.Meta.Tactic.Acyclic
// Imports: public import Lean.Meta.MatchUtil import Lean.Meta.Tactic.Simp.Main
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "acyclic"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 161, 38, 50, 105, 233, 209, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "failed with\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SizeOf"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeOf"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 72, 249, 57, 72, 20, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17;
static const lean_array_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_lt_of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value),LEAN_SCALAR_PTR_LITERAL(126, 191, 12, 194, 254, 232, 98, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lt_irrefl"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value),LEAN_SCALAR_PTR_LITERAL(120, 15, 17, 57, 9, 165, 30, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "succeeded"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_acyclic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_acyclic___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_acyclic___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_acyclic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_acyclic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_acyclic___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_acyclic___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_acyclic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_MVarId_acyclic___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_acyclic___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_acyclic___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_acyclic___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Acyclic"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 198, 135, 160, 31, 129, 248, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(255, 124, 224, 32, 114, 109, 103, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 46, 145, 199, 158, 116, 85, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 217, 237, 84, 249, 145, 36, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(164, 214, 130, 148, 92, 170, 51, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 87, 195, 9, 213, 249, 145, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 6, 112, 5, 70, 180, 189, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 90, 52, 235, 115, 14, 126, 31)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 53, 120, 229, 81, 141, 250, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 22, 83, 181, 119, 214, 241, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1360063758) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(112, 64, 213, 79, 183, 160, 32, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 255, 153, 62, 130, 215, 224, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 67, 219, 225, 47, 48, 77, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(234, 161, 47, 157, 109, 32, 111, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object* v_lhs_1_, lean_object* v_rhs_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
uint8_t v___y_9_; uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = l_Lean_Expr_isFVar(v_lhs_1_);
v___x_15_ = lean_bool_not(v___x_14_);
if (v___x_15_ == 0)
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = l_Lean_Expr_occurs(v_lhs_1_, v_rhs_2_);
v___x_17_ = lean_bool_not(v___x_16_);
v___y_9_ = v___x_17_;
goto v___jp_8_;
}
else
{
lean_dec_ref(v_lhs_1_);
v___y_9_ = v___x_15_;
goto v___jp_8_;
}
v___jp_8_:
{
if (v___y_9_ == 0)
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Meta_isConstructorApp_x27(v_rhs_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_10_;
}
else
{
uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_rhs_2_);
v___x_11_ = 0;
v___x_12_ = lean_box(v___x_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(lean_object* v_lhs_18_, lean_object* v_rhs_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v_lhs_18_, v_rhs_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t v___y_26_, lean_object* v_____r_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(v___y_26_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object* v___y_36_, lean_object* v_____r_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___y_9176__boxed_43_; lean_object* v_res_44_; 
v___y_9176__boxed_43_ = lean_unbox(v___y_36_);
v_res_44_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_9176__boxed_43_, v_____r_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t v___x_45_, lean_object* v_____r_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(v___x_45_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object* v___x_55_, lean_object* v_____r_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
uint8_t v___x_9203__boxed_62_; lean_object* v_res_63_; 
v___x_9203__boxed_62_ = lean_unbox(v___x_55_);
v_res_63_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_9203__boxed_62_, v_____r_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(lean_object* v_msgData_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v_mctx_73_; lean_object* v_lctx_74_; lean_object* v_options_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = lean_st_ref_get(v___y_66_);
v_mctx_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_mctx_73_);
lean_dec(v___x_72_);
v_lctx_74_ = lean_ctor_get(v___y_65_, 2);
v_options_75_ = lean_ctor_get(v___y_67_, 2);
lean_inc_ref(v_options_75_);
lean_inc_ref(v_lctx_74_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_71_);
lean_ctor_set(v___x_76_, 1, v_mctx_73_);
lean_ctor_set(v___x_76_, 2, v_lctx_74_);
lean_ctor_set(v___x_76_, 3, v_options_75_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_64_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msgData_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_86_; double v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_float_of_nat(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object* v_cls_91_, lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_144_; 
v_ref_98_ = lean_ctor_get(v___y_95_, 5);
v___x_99_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_144_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_144_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_144_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v_traceState_105_; lean_object* v_env_106_; lean_object* v_nextMacroScope_107_; lean_object* v_ngen_108_; lean_object* v_auxDeclNGen_109_; lean_object* v_cache_110_; lean_object* v_messages_111_; lean_object* v_infoState_112_; lean_object* v_snapshotTasks_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_143_; 
v___x_104_ = lean_st_ref_take(v___y_96_);
v_traceState_105_ = lean_ctor_get(v___x_104_, 4);
v_env_106_ = lean_ctor_get(v___x_104_, 0);
v_nextMacroScope_107_ = lean_ctor_get(v___x_104_, 1);
v_ngen_108_ = lean_ctor_get(v___x_104_, 2);
v_auxDeclNGen_109_ = lean_ctor_get(v___x_104_, 3);
v_cache_110_ = lean_ctor_get(v___x_104_, 5);
v_messages_111_ = lean_ctor_get(v___x_104_, 6);
v_infoState_112_ = lean_ctor_get(v___x_104_, 7);
v_snapshotTasks_113_ = lean_ctor_get(v___x_104_, 8);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_143_ == 0)
{
v___x_115_ = v___x_104_;
v_isShared_116_ = v_isSharedCheck_143_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_snapshotTasks_113_);
lean_inc(v_infoState_112_);
lean_inc(v_messages_111_);
lean_inc(v_cache_110_);
lean_inc(v_traceState_105_);
lean_inc(v_auxDeclNGen_109_);
lean_inc(v_ngen_108_);
lean_inc(v_nextMacroScope_107_);
lean_inc(v_env_106_);
lean_dec(v___x_104_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_143_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint64_t v_tid_117_; lean_object* v_traces_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_142_; 
v_tid_117_ = lean_ctor_get_uint64(v_traceState_105_, sizeof(void*)*1);
v_traces_118_ = lean_ctor_get(v_traceState_105_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_traceState_105_);
if (v_isSharedCheck_142_ == 0)
{
v___x_120_ = v_traceState_105_;
v_isShared_121_ = v_isSharedCheck_142_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_traces_118_);
lean_dec(v_traceState_105_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_142_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; double v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_122_ = lean_box(0);
v___x_123_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0);
v___x_124_ = 0;
v___x_125_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1));
v___x_126_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_126_, 0, v_cls_91_);
lean_ctor_set(v___x_126_, 1, v___x_122_);
lean_ctor_set(v___x_126_, 2, v___x_125_);
lean_ctor_set_float(v___x_126_, sizeof(void*)*3, v___x_123_);
lean_ctor_set_float(v___x_126_, sizeof(void*)*3 + 8, v___x_123_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3 + 16, v___x_124_);
v___x_127_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2));
v___x_128_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v_a_100_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
lean_inc(v_ref_98_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ref_98_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_PersistentArray_push___redArg(v_traces_118_, v___x_129_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_130_);
v___x_132_ = v___x_120_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_130_);
lean_ctor_set_uint64(v_reuseFailAlloc_141_, sizeof(void*)*1, v_tid_117_);
v___x_132_ = v_reuseFailAlloc_141_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v___x_132_);
v___x_134_ = v___x_115_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_env_106_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_nextMacroScope_107_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_ngen_108_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_auxDeclNGen_109_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_140_, 5, v_cache_110_);
lean_ctor_set(v_reuseFailAlloc_140_, 6, v_messages_111_);
lean_ctor_set(v_reuseFailAlloc_140_, 7, v_infoState_112_);
lean_ctor_set(v_reuseFailAlloc_140_, 8, v_snapshotTasks_113_);
v___x_134_ = v_reuseFailAlloc_140_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = lean_st_ref_set(v___y_96_, v___x_134_);
v___x_136_ = lean_box(0);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_136_);
v___x_138_ = v___x_102_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object* v_cls_145_, lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_145_, v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_ks_157_; lean_object* v_vs_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_182_; 
v_ks_157_ = lean_ctor_get(v_x_153_, 0);
v_vs_158_ = lean_ctor_get(v_x_153_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_182_ == 0)
{
v___x_160_ = v_x_153_;
v_isShared_161_ = v_isSharedCheck_182_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_vs_158_);
lean_inc(v_ks_157_);
lean_dec(v_x_153_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_182_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_array_get_size(v_ks_157_);
v___x_163_ = lean_nat_dec_lt(v_x_154_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_x_154_);
v___x_164_ = lean_array_push(v_ks_157_, v_x_155_);
v___x_165_ = lean_array_push(v_vs_158_, v_x_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_165_);
lean_ctor_set(v___x_160_, 0, v___x_164_);
v___x_167_ = v___x_160_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v_k_x27_169_; uint8_t v___x_170_; 
v_k_x27_169_ = lean_array_fget_borrowed(v_ks_157_, v_x_154_);
v___x_170_ = l_Lean_instBEqMVarId_beq(v_x_155_, v_k_x27_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_172_; 
if (v_isShared_161_ == 0)
{
v___x_172_ = v___x_160_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_ks_157_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_vs_158_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_x_154_, v___x_173_);
lean_dec(v_x_154_);
v_x_153_ = v___x_172_;
v_x_154_ = v___x_174_;
goto _start;
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = lean_array_fset(v_ks_157_, v_x_154_, v_x_155_);
v___x_178_ = lean_array_fset(v_vs_158_, v_x_154_, v_x_156_);
lean_dec(v_x_154_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_178_);
lean_ctor_set(v___x_160_, 0, v___x_177_);
v___x_180_ = v___x_160_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_n_183_, lean_object* v_k_184_, lean_object* v_v_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_n_183_, v___x_186_, v_k_184_, v_v_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_189_, size_t v_x_190_, size_t v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v_es_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v_j_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_es_194_ = lean_ctor_get(v_x_189_, 0);
v___x_195_ = ((size_t)31ULL);
v___x_196_ = lean_usize_land(v_x_190_, v___x_195_);
v_j_197_ = lean_usize_to_nat(v___x_196_);
v___x_198_ = lean_array_get_size(v_es_194_);
v___x_199_ = lean_nat_dec_lt(v_j_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v_j_197_);
lean_dec(v_x_193_);
lean_dec(v_x_192_);
return v_x_189_;
}
else
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_238_; 
lean_inc_ref(v_es_194_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_x_189_, 0);
lean_dec(v_unused_239_);
v___x_201_ = v_x_189_;
v_isShared_202_ = v_isSharedCheck_238_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_x_189_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_238_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_v_203_; lean_object* v___x_204_; lean_object* v_xs_x27_205_; lean_object* v___y_207_; 
v_v_203_ = lean_array_fget(v_es_194_, v_j_197_);
v___x_204_ = lean_box(0);
v_xs_x27_205_ = lean_array_fset(v_es_194_, v_j_197_, v___x_204_);
switch(lean_obj_tag(v_v_203_))
{
case 0:
{
lean_object* v_key_212_; lean_object* v_val_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_223_; 
v_key_212_ = lean_ctor_get(v_v_203_, 0);
v_val_213_ = lean_ctor_get(v_v_203_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_v_203_);
if (v_isSharedCheck_223_ == 0)
{
v___x_215_ = v_v_203_;
v_isShared_216_ = v_isSharedCheck_223_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_val_213_);
lean_inc(v_key_212_);
lean_dec(v_v_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_223_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint8_t v___x_217_; 
v___x_217_ = l_Lean_instBEqMVarId_beq(v_x_192_, v_key_212_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_del_object(v___x_215_);
v___x_218_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_212_, v_val_213_, v_x_192_, v_x_193_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___y_207_ = v___x_219_;
goto v___jp_206_;
}
else
{
lean_object* v___x_221_; 
lean_dec(v_val_213_);
lean_dec(v_key_212_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v_x_193_);
lean_ctor_set(v___x_215_, 0, v_x_192_);
v___x_221_ = v___x_215_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_x_192_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_x_193_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
v___y_207_ = v___x_221_;
goto v___jp_206_;
}
}
}
}
case 1:
{
lean_object* v_node_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_236_; 
v_node_224_ = lean_ctor_get(v_v_203_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_v_203_);
if (v_isSharedCheck_236_ == 0)
{
v___x_226_ = v_v_203_;
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_node_224_);
lean_dec(v_v_203_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_236_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_usize_shift_right(v_x_190_, v___x_228_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_x_191_, v___x_230_);
v___x_232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_node_224_, v___x_229_, v___x_231_, v_x_192_, v_x_193_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_232_);
v___x_234_ = v___x_226_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
v___y_207_ = v___x_234_;
goto v___jp_206_;
}
}
}
default: 
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_x_192_);
lean_ctor_set(v___x_237_, 1, v_x_193_);
v___y_207_ = v___x_237_;
goto v___jp_206_;
}
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_array_fset(v_xs_x27_205_, v_j_197_, v___y_207_);
lean_dec(v_j_197_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
else
{
lean_object* v_ks_240_; lean_object* v_vs_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_261_; 
v_ks_240_ = lean_ctor_get(v_x_189_, 0);
v_vs_241_ = lean_ctor_get(v_x_189_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_261_ == 0)
{
v___x_243_ = v_x_189_;
v_isShared_244_ = v_isSharedCheck_261_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_vs_241_);
lean_inc(v_ks_240_);
lean_dec(v_x_189_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_261_;
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
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_ks_240_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_vs_241_);
v___x_246_ = v_reuseFailAlloc_260_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v_newNode_247_; uint8_t v___y_249_; size_t v___x_255_; uint8_t v___x_256_; 
v_newNode_247_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v___x_246_, v_x_192_, v_x_193_);
v___x_255_ = ((size_t)7ULL);
v___x_256_ = lean_usize_dec_le(v___x_255_, v_x_191_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_247_);
v___x_258_ = lean_unsigned_to_nat(4u);
v___x_259_ = lean_nat_dec_lt(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
v___y_249_ = v___x_259_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___x_256_;
goto v___jp_248_;
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v_ks_250_; lean_object* v_vs_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_ks_250_ = lean_ctor_get(v_newNode_247_, 0);
lean_inc_ref(v_ks_250_);
v_vs_251_ = lean_ctor_get(v_newNode_247_, 1);
lean_inc_ref(v_vs_251_);
lean_dec_ref(v_newNode_247_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_191_, v_ks_250_, v_vs_251_, v___x_252_, v___x_253_);
lean_dec_ref(v_vs_251_);
lean_dec_ref(v_ks_250_);
return v___x_254_;
}
else
{
return v_newNode_247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(size_t v_depth_262_, lean_object* v_keys_263_, lean_object* v_vals_264_, lean_object* v_i_265_, lean_object* v_entries_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_array_get_size(v_keys_263_);
v___x_268_ = lean_nat_dec_lt(v_i_265_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v_i_265_);
return v_entries_266_;
}
else
{
lean_object* v_k_269_; lean_object* v_v_270_; uint64_t v___x_271_; size_t v_h_272_; size_t v___x_273_; lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v_h_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_k_269_ = lean_array_fget_borrowed(v_keys_263_, v_i_265_);
v_v_270_ = lean_array_fget_borrowed(v_vals_264_, v_i_265_);
v___x_271_ = l_Lean_instHashableMVarId_hash(v_k_269_);
v_h_272_ = lean_uint64_to_usize(v___x_271_);
v___x_273_ = ((size_t)5ULL);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_sub(v_depth_262_, v___x_275_);
v___x_277_ = lean_usize_mul(v___x_273_, v___x_276_);
v_h_278_ = lean_usize_shift_right(v_h_272_, v___x_277_);
v___x_279_ = lean_nat_add(v_i_265_, v___x_274_);
lean_dec(v_i_265_);
lean_inc(v_v_270_);
lean_inc(v_k_269_);
v___x_280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_entries_266_, v_h_278_, v_depth_262_, v_k_269_, v_v_270_);
v_i_265_ = v___x_279_;
v_entries_266_ = v___x_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_depth_282_, lean_object* v_keys_283_, lean_object* v_vals_284_, lean_object* v_i_285_, lean_object* v_entries_286_){
_start:
{
size_t v_depth_boxed_287_; lean_object* v_res_288_; 
v_depth_boxed_287_ = lean_unbox_usize(v_depth_282_);
lean_dec(v_depth_282_);
v_res_288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_boxed_287_, v_keys_283_, v_vals_284_, v_i_285_, v_entries_286_);
lean_dec_ref(v_vals_284_);
lean_dec_ref(v_keys_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
size_t v_x_9433__boxed_294_; size_t v_x_9434__boxed_295_; lean_object* v_res_296_; 
v_x_9433__boxed_294_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_x_9434__boxed_295_ = lean_unbox_usize(v_x_291_);
lean_dec(v_x_291_);
v_res_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_289_, v_x_9433__boxed_294_, v_x_9434__boxed_295_, v_x_292_, v_x_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
uint64_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
v___x_300_ = l_Lean_instHashableMVarId_hash(v_x_298_);
v___x_301_ = lean_uint64_to_usize(v___x_300_);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_297_, v___x_301_, v___x_302_, v_x_298_, v_x_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(lean_object* v_mvarId_304_, lean_object* v_val_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v_mctx_309_; lean_object* v_cache_310_; lean_object* v_zetaDeltaFVarIds_311_; lean_object* v_postponed_312_; lean_object* v_diag_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_341_; 
v___x_308_ = lean_st_ref_take(v___y_306_);
v_mctx_309_ = lean_ctor_get(v___x_308_, 0);
v_cache_310_ = lean_ctor_get(v___x_308_, 1);
v_zetaDeltaFVarIds_311_ = lean_ctor_get(v___x_308_, 2);
v_postponed_312_ = lean_ctor_get(v___x_308_, 3);
v_diag_313_ = lean_ctor_get(v___x_308_, 4);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_341_ == 0)
{
v___x_315_ = v___x_308_;
v_isShared_316_ = v_isSharedCheck_341_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_diag_313_);
lean_inc(v_postponed_312_);
lean_inc(v_zetaDeltaFVarIds_311_);
lean_inc(v_cache_310_);
lean_inc(v_mctx_309_);
lean_dec(v___x_308_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_341_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_depth_317_; lean_object* v_levelAssignDepth_318_; lean_object* v_lmvarCounter_319_; lean_object* v_mvarCounter_320_; lean_object* v_lDecls_321_; lean_object* v_decls_322_; lean_object* v_userNames_323_; lean_object* v_lAssignment_324_; lean_object* v_eAssignment_325_; lean_object* v_dAssignment_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_340_; 
v_depth_317_ = lean_ctor_get(v_mctx_309_, 0);
v_levelAssignDepth_318_ = lean_ctor_get(v_mctx_309_, 1);
v_lmvarCounter_319_ = lean_ctor_get(v_mctx_309_, 2);
v_mvarCounter_320_ = lean_ctor_get(v_mctx_309_, 3);
v_lDecls_321_ = lean_ctor_get(v_mctx_309_, 4);
v_decls_322_ = lean_ctor_get(v_mctx_309_, 5);
v_userNames_323_ = lean_ctor_get(v_mctx_309_, 6);
v_lAssignment_324_ = lean_ctor_get(v_mctx_309_, 7);
v_eAssignment_325_ = lean_ctor_get(v_mctx_309_, 8);
v_dAssignment_326_ = lean_ctor_get(v_mctx_309_, 9);
v_isSharedCheck_340_ = !lean_is_exclusive(v_mctx_309_);
if (v_isSharedCheck_340_ == 0)
{
v___x_328_ = v_mctx_309_;
v_isShared_329_ = v_isSharedCheck_340_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_dAssignment_326_);
lean_inc(v_eAssignment_325_);
lean_inc(v_lAssignment_324_);
lean_inc(v_userNames_323_);
lean_inc(v_decls_322_);
lean_inc(v_lDecls_321_);
lean_inc(v_mvarCounter_320_);
lean_inc(v_lmvarCounter_319_);
lean_inc(v_levelAssignDepth_318_);
lean_inc(v_depth_317_);
lean_dec(v_mctx_309_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_340_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_eAssignment_325_, v_mvarId_304_, v_val_305_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 8, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_depth_317_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_levelAssignDepth_318_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_lmvarCounter_319_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_mvarCounter_320_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_lDecls_321_);
lean_ctor_set(v_reuseFailAlloc_339_, 5, v_decls_322_);
lean_ctor_set(v_reuseFailAlloc_339_, 6, v_userNames_323_);
lean_ctor_set(v_reuseFailAlloc_339_, 7, v_lAssignment_324_);
lean_ctor_set(v_reuseFailAlloc_339_, 8, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 9, v_dAssignment_326_);
v___x_332_ = v_reuseFailAlloc_339_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_332_);
v___x_334_ = v___x_315_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_cache_310_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_zetaDeltaFVarIds_311_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_postponed_312_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_diag_313_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_st_ref_set(v___y_306_, v___x_334_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(lean_object* v_mvarId_342_, lean_object* v_val_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_342_, v_val_343_, v___y_344_);
lean_dec(v___y_344_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5));
v___x_359_ = l_Lean_Name_append(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_box(0);
v___x_376_ = lean_unsigned_to_nat(16u);
v___x_377_ = lean_mk_array(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14);
v___x_386_ = 1;
v___x_387_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_384_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*2, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(32u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21(void){
_start:
{
size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_unsigned_to_nat(32u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20);
v___x_401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_397_);
lean_ctor_set(v___x_401_, 3, v___x_397_);
lean_ctor_set_usize(v___x_401_, 4, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21);
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
lean_ctor_set(v___x_404_, 3, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object* v_mvarId_420_, lean_object* v_h_421_, lean_object* v_lhs_422_, lean_object* v_rhs_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_a_430_; lean_object* v___y_448_; lean_object* v___y_459_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v_a_489_; lean_object* v___y_493_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11));
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
lean_inc_ref(v___x_497_);
v___x_498_ = lean_array_push(v___x_497_, v_lhs_422_);
v___x_499_ = l_Lean_Meta_mkAppM(v___x_495_, v___x_498_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
lean_inc_ref(v___x_497_);
v___x_501_ = lean_array_push(v___x_497_, v_rhs_423_);
v___x_502_ = l_Lean_Meta_mkAppM(v___x_495_, v___x_501_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
lean_inc(v_a_500_);
v___x_504_ = l_Lean_Meta_mkLT(v_a_500_, v_a_503_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_box(0);
v___x_507_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_505_, v___x_506_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_427_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; uint8_t v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = lean_unsigned_to_nat(2u);
v___x_512_ = 0;
v___x_513_ = 1;
v___x_514_ = lean_box(0);
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12));
lean_inc_ref(v___x_497_);
v___x_516_ = lean_array_push(v___x_497_, v_a_510_);
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
v___x_518_ = l_Lean_Options_empty;
v___x_519_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_515_, v___x_516_, v___x_517_, v___x_518_, v_a_424_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_Expr_mvarId_x21(v_a_508_);
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18));
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23);
v___x_524_ = l_Lean_Meta_simpTarget(v___x_521_, v_a_520_, v___x_522_, v___x_514_, v___x_513_, v___x_523_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_575_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_575_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_575_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_575_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_fst_529_; 
v_fst_529_ = lean_ctor_get(v_a_525_, 0);
lean_inc(v_fst_529_);
lean_dec(v_a_525_);
if (lean_obj_tag(v_fst_529_) == 0)
{
lean_object* v___x_530_; 
lean_del_object(v___x_527_);
v___x_530_ = l_Lean_Meta_mkEqSymm(v_h_421_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l_Lean_Expr_appFn_x21(v_a_500_);
v___x_533_ = l_Lean_Meta_mkCongrArg(v___x_532_, v_a_531_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26));
v___x_536_ = lean_mk_empty_array_with_capacity(v___x_511_);
v___x_537_ = lean_array_push(v___x_536_, v_a_508_);
v___x_538_ = lean_array_push(v___x_537_, v_a_534_);
v___x_539_ = l_Lean_Meta_mkAppM(v___x_535_, v___x_538_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28));
v___x_542_ = lean_array_push(v___x_497_, v_a_500_);
v___x_543_ = l_Lean_Meta_mkAppM(v___x_541_, v___x_542_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
lean_inc(v_mvarId_420_);
v___x_545_ = l_Lean_MVarId_getType(v_mvarId_420_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Expr_app___override(v_a_544_, v_a_540_);
v___x_548_ = l_Lean_Meta_mkFalseElim(v_a_546_, v___x_547_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v_options_551_; lean_object* v_inheritedTraceOptions_552_; uint8_t v_hasTrace_553_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_420_, v_a_549_, v_a_425_);
lean_dec_ref(v___x_550_);
v_options_551_ = lean_ctor_get(v_a_426_, 2);
v_inheritedTraceOptions_552_ = lean_ctor_get(v_a_426_, 13);
v_hasTrace_553_ = lean_ctor_get_uint8(v_options_551_, sizeof(void*)*1);
if (v_hasTrace_553_ == 0)
{
goto v___jp_554_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_552_, v_options_551_, v___x_558_);
if (v___x_559_ == 0)
{
goto v___jp_554_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30);
v___x_561_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_557_, v___x_560_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_513_, v_a_562_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
v___y_493_ = v___x_563_;
goto v___jp_492_;
}
else
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_561_, 1);
v_a_489_ = v_a_564_;
goto v___jp_488_;
}
}
}
v___jp_554_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_513_, v___x_555_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
v___y_493_ = v___x_556_;
goto v___jp_492_;
}
}
else
{
lean_object* v_a_565_; 
lean_dec(v_mvarId_420_);
v_a_565_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_548_, 1);
v_a_489_ = v_a_565_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_566_; 
lean_dec(v_a_544_);
lean_dec(v_a_540_);
lean_dec(v_mvarId_420_);
v_a_566_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_545_, 1);
v_a_489_ = v_a_566_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_567_; 
lean_dec(v_a_540_);
lean_dec(v_mvarId_420_);
v_a_567_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_543_, 1);
v_a_489_ = v_a_567_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_568_; 
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec(v_mvarId_420_);
v_a_568_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_539_, 1);
v_a_489_ = v_a_568_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_569_; 
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec(v_mvarId_420_);
v_a_569_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_533_, 1);
v_a_489_ = v_a_569_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_570_; 
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec(v_mvarId_420_);
v_a_570_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_530_, 1);
v_a_489_ = v_a_570_;
goto v___jp_488_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec_ref_known(v_fst_529_, 1);
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v___x_571_ = lean_box(v___x_512_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_571_);
v___x_573_ = v___x_527_;
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
else
{
lean_object* v_a_576_; 
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_576_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_524_, 1);
v_a_489_ = v_a_576_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_577_; 
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_577_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_519_, 1);
v_a_489_ = v_a_577_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_578_; 
lean_dec(v_a_508_);
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_578_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_509_, 1);
v_a_489_ = v_a_578_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_579_; 
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_579_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_507_, 1);
v_a_489_ = v_a_579_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_580_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_504_, 1);
v_a_489_ = v_a_580_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_581_; 
lean_dec(v_a_500_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_581_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_502_, 1);
v_a_489_ = v_a_581_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_582_; 
lean_dec_ref(v___x_497_);
lean_dec_ref(v_rhs_423_);
lean_dec_ref(v_h_421_);
lean_dec(v_mvarId_420_);
v_a_582_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_499_, 1);
v_a_489_ = v_a_582_;
goto v___jp_488_;
}
v___jp_429_:
{
if (lean_obj_tag(v_a_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v_a_430_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v_a_430_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v_a_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_439_ = lean_ctor_get(v_a_430_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_a_430_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v_a_430_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 0);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
v___jp_447_:
{
if (lean_obj_tag(v___y_448_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___y_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___y_448_, 1);
v_a_430_ = v_a_449_;
goto v___jp_429_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___y_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___y_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___y_448_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___y_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
v___jp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_box(0);
lean_inc(v_a_427_);
lean_inc_ref(v_a_426_);
lean_inc(v_a_425_);
lean_inc_ref(v_a_424_);
v___x_461_ = lean_apply_6(v___y_459_, v___x_460_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, lean_box(0));
v___y_448_ = v___x_461_;
goto v___jp_447_;
}
v___jp_462_:
{
if (v___y_464_ == 0)
{
lean_object* v_options_465_; lean_object* v_inheritedTraceOptions_466_; uint8_t v_hasTrace_467_; lean_object* v___x_468_; lean_object* v___f_469_; 
v_options_465_ = lean_ctor_get(v_a_426_, 2);
v_inheritedTraceOptions_466_ = lean_ctor_get(v_a_426_, 13);
v_hasTrace_467_ = lean_ctor_get_uint8(v_options_465_, sizeof(void*)*1);
v___x_468_ = lean_box(v___y_464_);
v___f_469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_469_, 0, v___x_468_);
if (v_hasTrace_467_ == 0)
{
lean_dec_ref(v___y_463_);
v___y_459_ = v___f_469_;
goto v___jp_458_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_466_, v_options_465_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec_ref(v___y_463_);
v___y_459_ = v___f_469_;
goto v___jp_458_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v___f_469_);
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8);
v___x_474_ = l_Lean_Exception_toMessageData(v___y_463_);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_470_, v___x_475_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_464_, v_a_477_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
v___y_448_ = v___x_478_;
goto v___jp_447_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_476_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_476_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
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
}
}
else
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___y_463_);
return v___x_487_;
}
}
v___jp_488_:
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Exception_isInterrupt(v_a_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
lean_inc_ref(v_a_489_);
v___x_491_ = l_Lean_Exception_isRuntime(v_a_489_);
v___y_463_ = v_a_489_;
v___y_464_ = v___x_491_;
goto v___jp_462_;
}
else
{
v___y_463_ = v_a_489_;
v___y_464_ = v___x_490_;
goto v___jp_462_;
}
}
v___jp_492_:
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___y_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___y_493_);
v_a_430_ = v_a_494_;
goto v___jp_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object* v_mvarId_583_, lean_object* v_h_584_, lean_object* v_lhs_585_, lean_object* v_rhs_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_583_, v_h_584_, v_lhs_585_, v_rhs_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object* v_mvarId_593_, lean_object* v_val_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_593_, v_val_594_, v___y_596_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object* v_mvarId_601_, lean_object* v_val_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_601_, v_val_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_x_610_, v_x_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, size_t v_x_616_, size_t v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_615_, v_x_616_, v_x_617_, v_x_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_10262__boxed_627_; size_t v_x_10263__boxed_628_; lean_object* v_res_629_; 
v_x_10262__boxed_627_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_x_10263__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(v_00_u03b2_621_, v_x_622_, v_x_10262__boxed_627_, v_x_10263__boxed_628_, v_x_625_, v_x_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_630_, lean_object* v_n_631_, lean_object* v_k_632_, lean_object* v_v_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v_n_631_, v_k_632_, v_v_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_635_, size_t v_depth_636_, lean_object* v_keys_637_, lean_object* v_vals_638_, lean_object* v_heq_639_, lean_object* v_i_640_, lean_object* v_entries_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_636_, v_keys_637_, v_vals_638_, v_i_640_, v_entries_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_643_, lean_object* v_depth_644_, lean_object* v_keys_645_, lean_object* v_vals_646_, lean_object* v_heq_647_, lean_object* v_i_648_, lean_object* v_entries_649_){
_start:
{
size_t v_depth_boxed_650_; lean_object* v_res_651_; 
v_depth_boxed_650_ = lean_unbox_usize(v_depth_644_);
lean_dec(v_depth_644_);
v_res_651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(v_00_u03b2_643_, v_depth_boxed_650_, v_keys_645_, v_vals_646_, v_heq_647_, v_i_648_, v_entries_649_);
lean_dec_ref(v_vals_646_);
lean_dec_ref(v_keys_645_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_x_653_, v_x_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object* v_mvarId_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_665_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_665_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object* v_mvarId_682_, lean_object* v_x_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_682_, v_x_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object* v_00_u03b1_690_, lean_object* v_mvarId_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object* v_00_u03b1_699_, lean_object* v_mvarId_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(v_00_u03b1_699_, v_mvarId_700_, v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__2));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* v_h_714_, lean_object* v_mvarId_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc_ref(v_h_714_);
v___x_721_ = lean_infer_type(v_h_714_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = l_Lean_Meta_whnfD(v_a_722_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_779_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_779_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v_options_761_; uint8_t v_hasTrace_762_; 
v_options_761_ = lean_ctor_get(v___y_718_, 2);
v_hasTrace_762_ = lean_ctor_get_uint8(v_options_761_, sizeof(void*)*1);
if (v_hasTrace_762_ == 0)
{
v___y_729_ = v___y_716_;
v___y_730_ = v___y_717_;
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
goto v___jp_728_;
}
else
{
lean_object* v_inheritedTraceOptions_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_inheritedTraceOptions_763_ = lean_ctor_get(v___y_718_, 13);
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_761_, v___x_765_);
if (v___x_766_ == 0)
{
v___y_729_ = v___y_716_;
v___y_730_ = v___y_717_;
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
goto v___jp_728_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_767_ = lean_obj_once(&l_Lean_MVarId_acyclic___lam__0___closed__3, &l_Lean_MVarId_acyclic___lam__0___closed__3_once, _init_l_Lean_MVarId_acyclic___lam__0___closed__3);
lean_inc(v_a_724_);
v___x_768_ = l_Lean_MessageData_ofExpr(v_a_724_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_764_, v___x_769_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_dec_ref_known(v___x_770_, 1);
v___y_729_ = v___y_716_;
v___y_730_ = v___y_717_;
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
goto v___jp_728_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_726_);
lean_dec(v_a_724_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
v___jp_728_:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__1));
v___x_734_ = lean_unsigned_to_nat(3u);
v___x_735_ = l_Lean_Expr_isAppOfArity(v_a_724_, v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_a_724_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
v___x_736_ = lean_box(v___x_735_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_736_);
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_del_object(v___x_726_);
v___x_740_ = l_Lean_Expr_appFn_x21(v_a_724_);
v___x_741_ = l_Lean_Expr_appArg_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_Expr_appArg_x21(v_a_724_);
lean_dec(v_a_724_);
lean_inc_ref(v___x_742_);
lean_inc_ref(v___x_741_);
v___x_743_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_741_, v___x_742_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; uint8_t v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = lean_unbox(v_a_744_);
lean_dec(v_a_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_inc_ref(v___x_741_);
lean_inc_ref(v___x_742_);
v___x_746_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_742_, v___x_741_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
v___x_748_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_741_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
return v___x_746_;
}
else
{
lean_object* v___x_749_; 
lean_dec_ref_known(v___x_746_, 1);
v___x_749_ = l_Lean_Meta_mkEqSymm(v_h_714_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_715_, v_a_750_, v___x_742_, v___x_741_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v___x_751_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_741_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_mvarId_715_);
v_a_752_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_749_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_749_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_741_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
return v___x_746_;
}
}
else
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_715_, v_h_714_, v___x_741_, v___x_742_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v___x_760_;
}
}
else
{
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_741_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
v_a_780_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_723_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_723_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_mvarId_715_);
lean_dec_ref(v_h_714_);
v_a_788_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_721_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_721_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object* v_h_796_, lean_object* v_mvarId_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_MVarId_acyclic___lam__0(v_h_796_, v_mvarId_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* v_mvarId_804_, lean_object* v_h_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
lean_inc(v_mvarId_804_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0___boxed), 7, 2);
lean_closure_set(v___f_811_, 0, v_h_805_);
lean_closure_set(v___f_811_, 1, v_mvarId_804_);
v___x_812_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_804_, v___f_811_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* v_mvarId_813_, lean_object* v_h_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_MVarId_acyclic(v_mvarId_813_, v_h_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_885_ = 0;
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_));
v___x_887_ = l_Lean_registerTraceClass(v___x_884_, v___x_885_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
return v_res_889_;
}
}
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Acyclic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Acyclic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Acyclic(builtin);
}
#ifdef __cplusplus
}
#endif
