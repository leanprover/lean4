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
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2;
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
uint8_t v___x_12_; 
v___x_12_ = l_Lean_Expr_isFVar(v_lhs_1_);
if (v___x_12_ == 0)
{
lean_dec_ref(v_rhs_2_);
lean_dec_ref(v_lhs_1_);
goto v___jp_8_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = l_Lean_Expr_occurs(v_lhs_1_, v_rhs_2_);
if (v___x_13_ == 0)
{
lean_dec_ref(v_rhs_2_);
goto v___jp_8_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_isConstructorApp_x27(v_rhs_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_14_;
}
}
v___jp_8_:
{
uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = 0;
v___x_10_ = lean_box(v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(lean_object* v_lhs_15_, lean_object* v_rhs_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v_lhs_15_, v_rhs_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t v___y_23_, lean_object* v_____r_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(v___y_23_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object* v___y_33_, lean_object* v_____r_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
uint8_t v___y_9155__boxed_40_; lean_object* v_res_41_; 
v___y_9155__boxed_40_ = lean_unbox(v___y_33_);
v_res_41_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_9155__boxed_40_, v_____r_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t v___x_42_, lean_object* v_____r_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_box(v___x_42_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object* v___x_52_, lean_object* v_____r_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v___x_9182__boxed_59_; lean_object* v_res_60_; 
v___x_9182__boxed_59_ = lean_unbox(v___x_52_);
v_res_60_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_9182__boxed_59_, v_____r_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_env_68_; lean_object* v___x_69_; lean_object* v_mctx_70_; lean_object* v_lctx_71_; lean_object* v_options_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = lean_st_ref_get(v___y_63_);
v_mctx_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_mctx_70_);
lean_dec(v___x_69_);
v_lctx_71_ = lean_ctor_get(v___y_62_, 2);
v_options_72_ = lean_ctor_get(v___y_64_, 2);
lean_inc_ref(v_options_72_);
lean_inc_ref(v_lctx_71_);
v___x_73_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_73_, 0, v_env_68_);
lean_ctor_set(v___x_73_, 1, v_mctx_70_);
lean_ctor_set(v___x_73_, 2, v_lctx_71_);
lean_ctor_set(v___x_73_, 3, v_options_72_);
v___x_74_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_msgData_61_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0___boxed(lean_object* v_msgData_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msgData_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_83_; double v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_float_of_nat(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object* v_cls_88_, lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_ref_95_; lean_object* v___x_96_; lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_141_; 
v_ref_95_ = lean_ctor_get(v___y_92_, 5);
v___x_96_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_141_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_141_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_141_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v_traceState_102_; lean_object* v_env_103_; lean_object* v_nextMacroScope_104_; lean_object* v_ngen_105_; lean_object* v_auxDeclNGen_106_; lean_object* v_cache_107_; lean_object* v_messages_108_; lean_object* v_infoState_109_; lean_object* v_snapshotTasks_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_140_; 
v___x_101_ = lean_st_ref_take(v___y_93_);
v_traceState_102_ = lean_ctor_get(v___x_101_, 4);
v_env_103_ = lean_ctor_get(v___x_101_, 0);
v_nextMacroScope_104_ = lean_ctor_get(v___x_101_, 1);
v_ngen_105_ = lean_ctor_get(v___x_101_, 2);
v_auxDeclNGen_106_ = lean_ctor_get(v___x_101_, 3);
v_cache_107_ = lean_ctor_get(v___x_101_, 5);
v_messages_108_ = lean_ctor_get(v___x_101_, 6);
v_infoState_109_ = lean_ctor_get(v___x_101_, 7);
v_snapshotTasks_110_ = lean_ctor_get(v___x_101_, 8);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_140_ == 0)
{
v___x_112_ = v___x_101_;
v_isShared_113_ = v_isSharedCheck_140_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_snapshotTasks_110_);
lean_inc(v_infoState_109_);
lean_inc(v_messages_108_);
lean_inc(v_cache_107_);
lean_inc(v_traceState_102_);
lean_inc(v_auxDeclNGen_106_);
lean_inc(v_ngen_105_);
lean_inc(v_nextMacroScope_104_);
lean_inc(v_env_103_);
lean_dec(v___x_101_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_140_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint64_t v_tid_114_; lean_object* v_traces_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_139_; 
v_tid_114_ = lean_ctor_get_uint64(v_traceState_102_, sizeof(void*)*1);
v_traces_115_ = lean_ctor_get(v_traceState_102_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v_traceState_102_);
if (v_isSharedCheck_139_ == 0)
{
v___x_117_ = v_traceState_102_;
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_traces_115_);
lean_dec(v_traceState_102_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; double v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_119_ = lean_box(0);
v___x_120_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0);
v___x_121_ = 0;
v___x_122_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1));
v___x_123_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_123_, 0, v_cls_88_);
lean_ctor_set(v___x_123_, 1, v___x_119_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_ctor_set_float(v___x_123_, sizeof(void*)*3, v___x_120_);
lean_ctor_set_float(v___x_123_, sizeof(void*)*3 + 8, v___x_120_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*3 + 16, v___x_121_);
v___x_124_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2));
v___x_125_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v_a_97_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
lean_inc(v_ref_95_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v_ref_95_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_PersistentArray_push___redArg(v_traces_115_, v___x_126_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_127_);
v___x_129_ = v___x_117_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_127_);
lean_ctor_set_uint64(v_reuseFailAlloc_138_, sizeof(void*)*1, v_tid_114_);
v___x_129_ = v_reuseFailAlloc_138_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_129_);
v___x_131_ = v___x_112_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_env_103_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_nextMacroScope_104_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_ngen_105_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v_auxDeclNGen_106_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_137_, 5, v_cache_107_);
lean_ctor_set(v_reuseFailAlloc_137_, 6, v_messages_108_);
lean_ctor_set(v_reuseFailAlloc_137_, 7, v_infoState_109_);
lean_ctor_set(v_reuseFailAlloc_137_, 8, v_snapshotTasks_110_);
v___x_131_ = v_reuseFailAlloc_137_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_st_ref_set(v___y_93_, v___x_131_);
v___x_133_ = lean_box(0);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_133_);
v___x_135_ = v___x_99_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object* v_cls_142_, lean_object* v_msg_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_142_, v_msg_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_179_; 
v_ks_154_ = lean_ctor_get(v_x_150_, 0);
v_vs_155_ = lean_ctor_get(v_x_150_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_179_ == 0)
{
v___x_157_ = v_x_150_;
v_isShared_158_ = v_isSharedCheck_179_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_vs_155_);
lean_inc(v_ks_154_);
lean_dec(v_x_150_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_179_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_ks_154_);
v___x_160_ = lean_nat_dec_lt(v_x_151_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec(v_x_151_);
v___x_161_ = lean_array_push(v_ks_154_, v_x_152_);
v___x_162_ = lean_array_push(v_vs_155_, v_x_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_162_);
lean_ctor_set(v___x_157_, 0, v___x_161_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v_k_x27_166_; uint8_t v___x_167_; 
v_k_x27_166_ = lean_array_fget_borrowed(v_ks_154_, v_x_151_);
v___x_167_ = l_Lean_instBEqMVarId_beq(v_x_152_, v_k_x27_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_169_; 
if (v_isShared_158_ == 0)
{
v___x_169_ = v___x_157_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_ks_154_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_vs_155_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_x_151_, v___x_170_);
lean_dec(v_x_151_);
v_x_150_ = v___x_169_;
v_x_151_ = v___x_171_;
goto _start;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_array_fset(v_ks_154_, v_x_151_, v_x_152_);
v___x_175_ = lean_array_fset(v_vs_155_, v_x_151_, v_x_153_);
lean_dec(v_x_151_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_175_);
lean_ctor_set(v___x_157_, 0, v___x_174_);
v___x_177_ = v___x_157_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_n_180_, lean_object* v_k_181_, lean_object* v_v_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_n_180_, v___x_183_, v_k_181_, v_v_182_);
return v___x_184_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; 
v___x_185_ = ((size_t)5ULL);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_shift_left(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_190_ = lean_usize_sub(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_192_, size_t v_x_193_, size_t v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_es_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v_j_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_es_197_ = lean_ctor_get(v_x_192_, 0);
v___x_198_ = ((size_t)5ULL);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_201_ = lean_usize_land(v_x_193_, v___x_200_);
v_j_202_ = lean_usize_to_nat(v___x_201_);
v___x_203_ = lean_array_get_size(v_es_197_);
v___x_204_ = lean_nat_dec_lt(v_j_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_j_202_);
lean_dec(v_x_196_);
lean_dec(v_x_195_);
return v_x_192_;
}
else
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_241_; 
lean_inc_ref(v_es_197_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_x_192_, 0);
lean_dec(v_unused_242_);
v___x_206_ = v_x_192_;
v_isShared_207_ = v_isSharedCheck_241_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_x_192_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_241_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_v_208_; lean_object* v___x_209_; lean_object* v_xs_x27_210_; lean_object* v___y_212_; 
v_v_208_ = lean_array_fget(v_es_197_, v_j_202_);
v___x_209_ = lean_box(0);
v_xs_x27_210_ = lean_array_fset(v_es_197_, v_j_202_, v___x_209_);
switch(lean_obj_tag(v_v_208_))
{
case 0:
{
lean_object* v_key_217_; lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
v_key_217_ = lean_ctor_get(v_v_208_, 0);
v_val_218_ = lean_ctor_get(v_v_208_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_v_208_);
if (v_isSharedCheck_228_ == 0)
{
v___x_220_ = v_v_208_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_inc(v_key_217_);
lean_dec(v_v_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; 
v___x_222_ = l_Lean_instBEqMVarId_beq(v_x_195_, v_key_217_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_del_object(v___x_220_);
v___x_223_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_217_, v_val_218_, v_x_195_, v_x_196_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___y_212_ = v___x_224_;
goto v___jp_211_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v_val_218_);
lean_dec(v_key_217_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_x_196_);
lean_ctor_set(v___x_220_, 0, v_x_195_);
v___x_226_ = v___x_220_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_x_195_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_x_196_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v___y_212_ = v___x_226_;
goto v___jp_211_;
}
}
}
}
case 1:
{
lean_object* v_node_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_239_; 
v_node_229_ = lean_ctor_get(v_v_208_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_v_208_);
if (v_isSharedCheck_239_ == 0)
{
v___x_231_ = v_v_208_;
v_isShared_232_ = v_isSharedCheck_239_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_node_229_);
lean_dec(v_v_208_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_239_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_233_ = lean_usize_shift_right(v_x_193_, v___x_198_);
v___x_234_ = lean_usize_add(v_x_194_, v___x_199_);
v___x_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_node_229_, v___x_233_, v___x_234_, v_x_195_, v_x_196_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_235_);
v___x_237_ = v___x_231_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
v___y_212_ = v___x_237_;
goto v___jp_211_;
}
}
}
default: 
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_x_195_);
lean_ctor_set(v___x_240_, 1, v_x_196_);
v___y_212_ = v___x_240_;
goto v___jp_211_;
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_array_fset(v_xs_x27_210_, v_j_202_, v___y_212_);
lean_dec(v_j_202_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_213_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
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
}
else
{
lean_object* v_ks_243_; lean_object* v_vs_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_264_; 
v_ks_243_ = lean_ctor_get(v_x_192_, 0);
v_vs_244_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_264_ == 0)
{
v___x_246_ = v_x_192_;
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_vs_244_);
lean_inc(v_ks_243_);
lean_dec(v_x_192_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_ks_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_vs_244_);
v___x_249_ = v_reuseFailAlloc_263_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v_newNode_250_; uint8_t v___y_252_; size_t v___x_258_; uint8_t v___x_259_; 
v_newNode_250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v___x_249_, v_x_195_, v_x_196_);
v___x_258_ = ((size_t)7ULL);
v___x_259_ = lean_usize_dec_le(v___x_258_, v_x_194_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_250_);
v___x_261_ = lean_unsigned_to_nat(4u);
v___x_262_ = lean_nat_dec_lt(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___y_252_ = v___x_262_;
goto v___jp_251_;
}
else
{
v___y_252_ = v___x_259_;
goto v___jp_251_;
}
v___jp_251_:
{
if (v___y_252_ == 0)
{
lean_object* v_ks_253_; lean_object* v_vs_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_ks_253_ = lean_ctor_get(v_newNode_250_, 0);
lean_inc_ref(v_ks_253_);
v_vs_254_ = lean_ctor_get(v_newNode_250_, 1);
lean_inc_ref(v_vs_254_);
lean_dec_ref(v_newNode_250_);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2);
v___x_257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_194_, v_ks_253_, v_vs_254_, v___x_255_, v___x_256_);
lean_dec_ref(v_vs_254_);
lean_dec_ref(v_ks_253_);
return v___x_257_;
}
else
{
return v_newNode_250_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(size_t v_depth_265_, lean_object* v_keys_266_, lean_object* v_vals_267_, lean_object* v_i_268_, lean_object* v_entries_269_){
_start:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_array_get_size(v_keys_266_);
v___x_271_ = lean_nat_dec_lt(v_i_268_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_i_268_);
return v_entries_269_;
}
else
{
lean_object* v_k_272_; lean_object* v_v_273_; uint64_t v___x_274_; size_t v_h_275_; size_t v___x_276_; lean_object* v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v_h_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_k_272_ = lean_array_fget_borrowed(v_keys_266_, v_i_268_);
v_v_273_ = lean_array_fget_borrowed(v_vals_267_, v_i_268_);
v___x_274_ = l_Lean_instHashableMVarId_hash(v_k_272_);
v_h_275_ = lean_uint64_to_usize(v___x_274_);
v___x_276_ = ((size_t)5ULL);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v_depth_265_, v___x_278_);
v___x_280_ = lean_usize_mul(v___x_276_, v___x_279_);
v_h_281_ = lean_usize_shift_right(v_h_275_, v___x_280_);
v___x_282_ = lean_nat_add(v_i_268_, v___x_277_);
lean_dec(v_i_268_);
lean_inc(v_v_273_);
lean_inc(v_k_272_);
v___x_283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_entries_269_, v_h_281_, v_depth_265_, v_k_272_, v_v_273_);
v_i_268_ = v___x_282_;
v_entries_269_ = v___x_283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_depth_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_entries_289_){
_start:
{
size_t v_depth_boxed_290_; lean_object* v_res_291_; 
v_depth_boxed_290_ = lean_unbox_usize(v_depth_285_);
lean_dec(v_depth_285_);
v_res_291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_boxed_290_, v_keys_286_, v_vals_287_, v_i_288_, v_entries_289_);
lean_dec_ref(v_vals_287_);
lean_dec_ref(v_keys_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
size_t v_x_9424__boxed_297_; size_t v_x_9425__boxed_298_; lean_object* v_res_299_; 
v_x_9424__boxed_297_ = lean_unbox_usize(v_x_293_);
lean_dec(v_x_293_);
v_x_9425__boxed_298_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_res_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_292_, v_x_9424__boxed_297_, v_x_9425__boxed_298_, v_x_295_, v_x_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_303_ = l_Lean_instHashableMVarId_hash(v_x_301_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_300_, v___x_304_, v___x_305_, v_x_301_, v_x_302_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(lean_object* v_mvarId_307_, lean_object* v_val_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_mctx_312_; lean_object* v_cache_313_; lean_object* v_zetaDeltaFVarIds_314_; lean_object* v_postponed_315_; lean_object* v_diag_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_344_; 
v___x_311_ = lean_st_ref_take(v___y_309_);
v_mctx_312_ = lean_ctor_get(v___x_311_, 0);
v_cache_313_ = lean_ctor_get(v___x_311_, 1);
v_zetaDeltaFVarIds_314_ = lean_ctor_get(v___x_311_, 2);
v_postponed_315_ = lean_ctor_get(v___x_311_, 3);
v_diag_316_ = lean_ctor_get(v___x_311_, 4);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_344_ == 0)
{
v___x_318_ = v___x_311_;
v_isShared_319_ = v_isSharedCheck_344_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_diag_316_);
lean_inc(v_postponed_315_);
lean_inc(v_zetaDeltaFVarIds_314_);
lean_inc(v_cache_313_);
lean_inc(v_mctx_312_);
lean_dec(v___x_311_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_344_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_depth_320_; lean_object* v_levelAssignDepth_321_; lean_object* v_lmvarCounter_322_; lean_object* v_mvarCounter_323_; lean_object* v_lDecls_324_; lean_object* v_decls_325_; lean_object* v_userNames_326_; lean_object* v_lAssignment_327_; lean_object* v_eAssignment_328_; lean_object* v_dAssignment_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_343_; 
v_depth_320_ = lean_ctor_get(v_mctx_312_, 0);
v_levelAssignDepth_321_ = lean_ctor_get(v_mctx_312_, 1);
v_lmvarCounter_322_ = lean_ctor_get(v_mctx_312_, 2);
v_mvarCounter_323_ = lean_ctor_get(v_mctx_312_, 3);
v_lDecls_324_ = lean_ctor_get(v_mctx_312_, 4);
v_decls_325_ = lean_ctor_get(v_mctx_312_, 5);
v_userNames_326_ = lean_ctor_get(v_mctx_312_, 6);
v_lAssignment_327_ = lean_ctor_get(v_mctx_312_, 7);
v_eAssignment_328_ = lean_ctor_get(v_mctx_312_, 8);
v_dAssignment_329_ = lean_ctor_get(v_mctx_312_, 9);
v_isSharedCheck_343_ = !lean_is_exclusive(v_mctx_312_);
if (v_isSharedCheck_343_ == 0)
{
v___x_331_ = v_mctx_312_;
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_dAssignment_329_);
lean_inc(v_eAssignment_328_);
lean_inc(v_lAssignment_327_);
lean_inc(v_userNames_326_);
lean_inc(v_decls_325_);
lean_inc(v_lDecls_324_);
lean_inc(v_mvarCounter_323_);
lean_inc(v_lmvarCounter_322_);
lean_inc(v_levelAssignDepth_321_);
lean_inc(v_depth_320_);
lean_dec(v_mctx_312_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_eAssignment_328_, v_mvarId_307_, v_val_308_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 8, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_depth_320_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_levelAssignDepth_321_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_lmvarCounter_322_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_mvarCounter_323_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_lDecls_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 5, v_decls_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 6, v_userNames_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 7, v_lAssignment_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 8, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_342_, 9, v_dAssignment_329_);
v___x_335_ = v_reuseFailAlloc_342_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_335_);
v___x_337_ = v___x_318_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_cache_313_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_zetaDeltaFVarIds_314_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_postponed_315_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_diag_316_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_st_ref_set(v___y_309_, v___x_337_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(lean_object* v_mvarId_345_, lean_object* v_val_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_345_, v_val_346_, v___y_347_);
lean_dec(v___y_347_);
return v_res_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5));
v___x_362_ = l_Lean_Name_append(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_unsigned_to_nat(16u);
v___x_380_ = lean_mk_array(v___x_379_, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14);
v___x_389_ = 1;
v___x_390_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*2, v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(32u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21(void){
_start:
{
size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = ((size_t)5ULL);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_unsigned_to_nat(32u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20);
v___x_404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_400_);
lean_ctor_set(v___x_404_, 3, v___x_400_);
lean_ctor_set_usize(v___x_404_, 4, v___x_399_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22);
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object* v_mvarId_423_, lean_object* v_h_424_, lean_object* v_lhs_425_, lean_object* v_rhs_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_a_433_; lean_object* v___y_451_; lean_object* v___y_462_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v_a_492_; lean_object* v___y_496_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11));
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
lean_inc_ref(v___x_500_);
v___x_501_ = lean_array_push(v___x_500_, v_lhs_425_);
v___x_502_ = l_Lean_Meta_mkAppM(v___x_498_, v___x_501_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
lean_inc_ref(v___x_500_);
v___x_504_ = lean_array_push(v___x_500_, v_rhs_426_);
v___x_505_ = l_Lean_Meta_mkAppM(v___x_498_, v___x_504_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
lean_inc(v_a_503_);
v___x_507_ = l_Lean_Meta_mkLT(v_a_503_, v_a_506_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = lean_box(0);
v___x_510_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_508_, v___x_509_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_430_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; uint8_t v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = 0;
v___x_516_ = 1;
v___x_517_ = lean_box(0);
v___x_518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12));
lean_inc_ref(v___x_500_);
v___x_519_ = lean_array_push(v___x_500_, v_a_513_);
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
v___x_521_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_518_, v___x_519_, v___x_520_, v_a_427_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = l_Lean_Expr_mvarId_x21(v_a_511_);
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18));
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23);
v___x_526_ = l_Lean_Meta_simpTarget(v___x_523_, v_a_522_, v___x_524_, v___x_517_, v___x_516_, v___x_525_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_577_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_577_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_577_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_577_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; 
v_fst_531_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_fst_531_);
lean_dec(v_a_527_);
if (lean_obj_tag(v_fst_531_) == 0)
{
lean_object* v___x_532_; 
lean_del_object(v___x_529_);
v___x_532_ = l_Lean_Meta_mkEqSymm(v_h_424_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_Expr_appFn_x21(v_a_503_);
v___x_535_ = l_Lean_Meta_mkCongrArg(v___x_534_, v_a_533_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26));
v___x_538_ = lean_mk_empty_array_with_capacity(v___x_514_);
v___x_539_ = lean_array_push(v___x_538_, v_a_511_);
v___x_540_ = lean_array_push(v___x_539_, v_a_536_);
v___x_541_ = l_Lean_Meta_mkAppM(v___x_537_, v___x_540_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28));
v___x_544_ = lean_array_push(v___x_500_, v_a_503_);
v___x_545_ = l_Lean_Meta_mkAppM(v___x_543_, v___x_544_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
lean_inc(v_mvarId_423_);
v___x_547_ = l_Lean_MVarId_getType(v_mvarId_423_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = l_Lean_Expr_app___override(v_a_546_, v_a_542_);
v___x_550_ = l_Lean_Meta_mkFalseElim(v_a_548_, v___x_549_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v_options_553_; lean_object* v_inheritedTraceOptions_554_; uint8_t v_hasTrace_555_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_423_, v_a_551_, v_a_428_);
lean_dec_ref(v___x_552_);
v_options_553_ = lean_ctor_get(v_a_429_, 2);
v_inheritedTraceOptions_554_ = lean_ctor_get(v_a_429_, 13);
v_hasTrace_555_ = lean_ctor_get_uint8(v_options_553_, sizeof(void*)*1);
if (v_hasTrace_555_ == 0)
{
goto v___jp_556_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_554_, v_options_553_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_556_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30);
v___x_563_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_559_, v___x_562_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_516_, v_a_564_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v___y_496_ = v___x_565_;
goto v___jp_495_;
}
else
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___x_563_);
v_a_492_ = v_a_566_;
goto v___jp_491_;
}
}
}
v___jp_556_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_516_, v___x_557_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v___y_496_ = v___x_558_;
goto v___jp_495_;
}
}
else
{
lean_object* v_a_567_; 
lean_dec(v_mvarId_423_);
v_a_567_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_567_);
lean_dec_ref(v___x_550_);
v_a_492_ = v_a_567_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_568_; 
lean_dec(v_a_546_);
lean_dec(v_a_542_);
lean_dec(v_mvarId_423_);
v_a_568_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_547_);
v_a_492_ = v_a_568_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_569_; 
lean_dec(v_a_542_);
lean_dec(v_mvarId_423_);
v_a_569_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_545_);
v_a_492_ = v_a_569_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_570_; 
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec(v_mvarId_423_);
v_a_570_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_541_);
v_a_492_ = v_a_570_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_571_; 
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec(v_mvarId_423_);
v_a_571_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_535_);
v_a_492_ = v_a_571_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_572_; 
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec(v_mvarId_423_);
v_a_572_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_532_);
v_a_492_ = v_a_572_;
goto v___jp_491_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec_ref(v_fst_531_);
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v___x_573_ = lean_box(v___x_515_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_573_);
v___x_575_ = v___x_529_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; 
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_578_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_526_);
v_a_492_ = v_a_578_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_579_; 
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_579_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_521_);
v_a_492_ = v_a_579_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v_a_511_);
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_580_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_512_);
v_a_492_ = v_a_580_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_581_; 
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_581_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_510_);
v_a_492_ = v_a_581_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_582_; 
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_582_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_507_);
v_a_492_ = v_a_582_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_583_; 
lean_dec(v_a_503_);
lean_dec_ref(v___x_500_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_583_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_583_);
lean_dec_ref(v___x_505_);
v_a_492_ = v_a_583_;
goto v___jp_491_;
}
}
else
{
lean_object* v_a_584_; 
lean_dec_ref(v___x_500_);
lean_dec_ref(v_rhs_426_);
lean_dec_ref(v_h_424_);
lean_dec(v_mvarId_423_);
v_a_584_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_502_);
v_a_492_ = v_a_584_;
goto v___jp_491_;
}
v___jp_432_:
{
if (lean_obj_tag(v_a_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v_a_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v_a_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v_a_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v_a_433_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_a_433_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v_a_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 0);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
v___jp_450_:
{
if (lean_obj_tag(v___y_451_) == 0)
{
lean_object* v_a_452_; 
v_a_452_ = lean_ctor_get(v___y_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___y_451_);
v_a_433_ = v_a_452_;
goto v___jp_432_;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_a_453_ = lean_ctor_get(v___y_451_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___y_451_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___y_451_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___y_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_box(0);
lean_inc(v_a_430_);
lean_inc_ref(v_a_429_);
lean_inc(v_a_428_);
lean_inc_ref(v_a_427_);
v___x_464_ = lean_apply_6(v___y_462_, v___x_463_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, lean_box(0));
v___y_451_ = v___x_464_;
goto v___jp_450_;
}
v___jp_465_:
{
if (v___y_467_ == 0)
{
lean_object* v_options_468_; lean_object* v_inheritedTraceOptions_469_; uint8_t v_hasTrace_470_; lean_object* v___x_471_; lean_object* v___f_472_; 
v_options_468_ = lean_ctor_get(v_a_429_, 2);
v_inheritedTraceOptions_469_ = lean_ctor_get(v_a_429_, 13);
v_hasTrace_470_ = lean_ctor_get_uint8(v_options_468_, sizeof(void*)*1);
v___x_471_ = lean_box(v___y_467_);
v___f_472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_472_, 0, v___x_471_);
if (v_hasTrace_470_ == 0)
{
lean_dec_ref(v___y_466_);
v___y_462_ = v___f_472_;
goto v___jp_461_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_469_, v_options_468_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec_ref(v___y_466_);
v___y_462_ = v___f_472_;
goto v___jp_461_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___f_472_);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8);
v___x_477_ = l_Lean_Exception_toMessageData(v___y_466_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_473_, v___x_478_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___x_481_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_467_, v_a_480_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
v___y_451_ = v___x_481_;
goto v___jp_450_;
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_479_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___y_466_);
return v___x_490_;
}
}
v___jp_491_:
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Exception_isInterrupt(v_a_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
lean_inc_ref(v_a_492_);
v___x_494_ = l_Lean_Exception_isRuntime(v_a_492_);
v___y_466_ = v_a_492_;
v___y_467_ = v___x_494_;
goto v___jp_465_;
}
else
{
v___y_466_ = v_a_492_;
v___y_467_ = v___x_493_;
goto v___jp_465_;
}
}
v___jp_495_:
{
lean_object* v_a_497_; 
v_a_497_ = lean_ctor_get(v___y_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___y_496_);
v_a_433_ = v_a_497_;
goto v___jp_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object* v_mvarId_585_, lean_object* v_h_586_, lean_object* v_lhs_587_, lean_object* v_rhs_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_585_, v_h_586_, v_lhs_587_, v_rhs_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object* v_mvarId_595_, lean_object* v_val_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_595_, v_val_596_, v___y_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object* v_mvarId_603_, lean_object* v_val_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_603_, v_val_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_x_612_, v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, size_t v_x_618_, size_t v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_617_, v_x_618_, v_x_619_, v_x_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
size_t v_x_10257__boxed_629_; size_t v_x_10258__boxed_630_; lean_object* v_res_631_; 
v_x_10257__boxed_629_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_x_10258__boxed_630_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_res_631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(v_00_u03b2_623_, v_x_624_, v_x_10257__boxed_629_, v_x_10258__boxed_630_, v_x_627_, v_x_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_632_, lean_object* v_n_633_, lean_object* v_k_634_, lean_object* v_v_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v_n_633_, v_k_634_, v_v_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_637_, size_t v_depth_638_, lean_object* v_keys_639_, lean_object* v_vals_640_, lean_object* v_heq_641_, lean_object* v_i_642_, lean_object* v_entries_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_638_, v_keys_639_, v_vals_640_, v_i_642_, v_entries_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_645_, lean_object* v_depth_646_, lean_object* v_keys_647_, lean_object* v_vals_648_, lean_object* v_heq_649_, lean_object* v_i_650_, lean_object* v_entries_651_){
_start:
{
size_t v_depth_boxed_652_; lean_object* v_res_653_; 
v_depth_boxed_652_ = lean_unbox_usize(v_depth_646_);
lean_dec(v_depth_646_);
v_res_653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(v_00_u03b2_645_, v_depth_boxed_652_, v_keys_647_, v_vals_648_, v_heq_649_, v_i_650_, v_entries_651_);
lean_dec_ref(v_vals_648_);
lean_dec_ref(v_keys_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_x_655_, v_x_656_, v_x_657_, v_x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object* v_mvarId_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_667_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_667_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object* v_mvarId_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_684_, v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object* v_00_u03b1_692_, lean_object* v_mvarId_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_693_, v_x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object* v_00_u03b1_701_, lean_object* v_mvarId_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(v_00_u03b1_701_, v_mvarId_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__2));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* v_h_716_, lean_object* v_mvarId_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc_ref(v_h_716_);
v___x_723_ = lean_infer_type(v_h_716_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l_Lean_Meta_whnfD(v_a_724_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_781_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_781_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_781_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_781_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_options_763_; uint8_t v_hasTrace_764_; 
v_options_763_ = lean_ctor_get(v___y_720_, 2);
v_hasTrace_764_ = lean_ctor_get_uint8(v_options_763_, sizeof(void*)*1);
if (v_hasTrace_764_ == 0)
{
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
goto v___jp_730_;
}
else
{
lean_object* v_inheritedTraceOptions_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_inheritedTraceOptions_765_ = lean_ctor_get(v___y_720_, 13);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_765_, v_options_763_, v___x_767_);
if (v___x_768_ == 0)
{
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
goto v___jp_730_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_769_ = lean_obj_once(&l_Lean_MVarId_acyclic___lam__0___closed__3, &l_Lean_MVarId_acyclic___lam__0___closed__3_once, _init_l_Lean_MVarId_acyclic___lam__0___closed__3);
lean_inc(v_a_726_);
v___x_770_ = l_Lean_MessageData_ofExpr(v_a_726_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_766_, v___x_771_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_dec_ref(v___x_772_);
v___y_731_ = v___y_718_;
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
goto v___jp_730_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
v___jp_730_:
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__1));
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = l_Lean_Expr_isAppOfArity(v_a_726_, v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_a_726_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
v___x_738_ = lean_box(v___x_737_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_738_);
v___x_740_ = v___x_728_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_del_object(v___x_728_);
v___x_742_ = l_Lean_Expr_appFn_x21(v_a_726_);
v___x_743_ = l_Lean_Expr_appArg_x21(v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = l_Lean_Expr_appArg_x21(v_a_726_);
lean_dec(v_a_726_);
lean_inc_ref(v___x_744_);
lean_inc_ref(v___x_743_);
v___x_745_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_743_, v___x_744_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; uint8_t v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_745_);
v___x_747_ = lean_unbox(v_a_746_);
lean_dec(v_a_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_inc_ref(v___x_743_);
lean_inc_ref(v___x_744_);
v___x_748_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_744_, v___x_743_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; uint8_t v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
v___x_750_ = lean_unbox(v_a_749_);
lean_dec(v_a_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_743_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
return v___x_748_;
}
else
{
lean_object* v___x_751_; 
lean_dec_ref(v___x_748_);
v___x_751_ = l_Lean_Meta_mkEqSymm(v_h_716_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_717_, v_a_752_, v___x_744_, v___x_743_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_743_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_mvarId_717_);
v_a_754_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_751_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_751_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_743_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
return v___x_748_;
}
}
else
{
lean_object* v___x_762_; 
v___x_762_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_717_, v_h_716_, v___x_743_, v___x_744_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v___x_762_;
}
}
else
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_743_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
v_a_782_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_725_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_725_);
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
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v_mvarId_717_);
lean_dec_ref(v_h_716_);
v_a_790_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_723_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_723_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object* v_h_798_, lean_object* v_mvarId_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_MVarId_acyclic___lam__0(v_h_798_, v_mvarId_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* v_mvarId_806_, lean_object* v_h_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___f_813_; lean_object* v___x_814_; 
lean_inc(v_mvarId_806_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0___boxed), 7, 2);
lean_closure_set(v___f_813_, 0, v_h_807_);
lean_closure_set(v___f_813_, 1, v_mvarId_806_);
v___x_814_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_806_, v___f_813_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* v_mvarId_815_, lean_object* v_h_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_MVarId_acyclic(v_mvarId_815_, v_h_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_887_ = 0;
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_));
v___x_889_ = l_Lean_registerTraceClass(v___x_886_, v___x_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
return v_res_891_;
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
