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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
uint8_t v___y_8957__boxed_40_; lean_object* v_res_41_; 
v___y_8957__boxed_40_ = lean_unbox(v___y_33_);
v_res_41_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_8957__boxed_40_, v_____r_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
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
uint8_t v___x_8984__boxed_59_; lean_object* v_res_60_; 
v___x_8984__boxed_59_ = lean_unbox(v___x_52_);
v_res_60_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_8984__boxed_59_, v_____r_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
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
lean_object* v___x_67_; lean_object* v_env_68_; uint8_t v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v_toCold_72_; lean_object* v_mctx_73_; lean_object* v_lctx_74_; lean_object* v_options_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = 0;
v_env_70_ = l_Lean_Environment_setRecordingDeps(v_env_68_, v___x_69_);
v___x_71_ = lean_st_ref_get(v___y_63_);
v_toCold_72_ = lean_ctor_get(v___y_64_, 0);
v_mctx_73_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_mctx_73_);
lean_dec(v___x_71_);
v_lctx_74_ = lean_ctor_get(v___y_62_, 2);
v_options_75_ = lean_ctor_get(v_toCold_72_, 2);
lean_inc_ref(v_options_75_);
lean_inc_ref(v_lctx_74_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_70_);
lean_ctor_set(v___x_76_, 1, v_mctx_73_);
lean_ctor_set(v___x_76_, 2, v_lctx_74_);
lean_ctor_set(v___x_76_, 3, v_options_75_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_61_);
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
lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_145_; 
v_ref_98_ = lean_ctor_get(v___y_95_, 2);
v___x_99_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_145_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_145_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_145_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v_traceState_105_; lean_object* v_env_106_; lean_object* v_nextMacroScope_107_; lean_object* v_ngen_108_; lean_object* v_auxDeclNGen_109_; lean_object* v_cache_110_; lean_object* v_recordedDeps_111_; lean_object* v_messages_112_; lean_object* v_infoState_113_; lean_object* v_snapshotTasks_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_144_; 
v___x_104_ = lean_st_ref_take(v___y_96_);
v_traceState_105_ = lean_ctor_get(v___x_104_, 4);
v_env_106_ = lean_ctor_get(v___x_104_, 0);
v_nextMacroScope_107_ = lean_ctor_get(v___x_104_, 1);
v_ngen_108_ = lean_ctor_get(v___x_104_, 2);
v_auxDeclNGen_109_ = lean_ctor_get(v___x_104_, 3);
v_cache_110_ = lean_ctor_get(v___x_104_, 5);
v_recordedDeps_111_ = lean_ctor_get(v___x_104_, 6);
v_messages_112_ = lean_ctor_get(v___x_104_, 7);
v_infoState_113_ = lean_ctor_get(v___x_104_, 8);
v_snapshotTasks_114_ = lean_ctor_get(v___x_104_, 9);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_144_ == 0)
{
v___x_116_ = v___x_104_;
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_snapshotTasks_114_);
lean_inc(v_infoState_113_);
lean_inc(v_messages_112_);
lean_inc(v_recordedDeps_111_);
lean_inc(v_cache_110_);
lean_inc(v_traceState_105_);
lean_inc(v_auxDeclNGen_109_);
lean_inc(v_ngen_108_);
lean_inc(v_nextMacroScope_107_);
lean_inc(v_env_106_);
lean_dec(v___x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint64_t v_tid_118_; lean_object* v_traces_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_tid_118_ = lean_ctor_get_uint64(v_traceState_105_, sizeof(void*)*1);
v_traces_119_ = lean_ctor_get(v_traceState_105_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_traceState_105_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v_traceState_105_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_traces_119_);
lean_dec(v_traceState_105_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; double v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_box(0);
v___x_125_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0);
v___x_126_ = 0;
v___x_127_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1));
v___x_128_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_128_, 0, v_cls_91_);
lean_ctor_set(v___x_128_, 1, v___x_124_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
lean_ctor_set_float(v___x_128_, sizeof(void*)*3, v___x_125_);
lean_ctor_set_float(v___x_128_, sizeof(void*)*3 + 8, v___x_125_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 16, v___x_126_);
v___x_129_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2));
v___x_130_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v_a_100_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
lean_inc(v_ref_98_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_ref_98_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = l_Lean_PersistentArray_push___redArg(v_traces_119_, v___x_131_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_132_);
v___x_134_ = v___x_121_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_132_);
lean_ctor_set_uint64(v_reuseFailAlloc_142_, sizeof(void*)*1, v_tid_118_);
v___x_134_ = v_reuseFailAlloc_142_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v___x_134_);
v___x_136_ = v___x_116_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_env_106_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_nextMacroScope_107_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_ngen_108_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_auxDeclNGen_109_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_cache_110_);
lean_ctor_set(v_reuseFailAlloc_141_, 6, v_recordedDeps_111_);
lean_ctor_set(v_reuseFailAlloc_141_, 7, v_messages_112_);
lean_ctor_set(v_reuseFailAlloc_141_, 8, v_infoState_113_);
lean_ctor_set(v_reuseFailAlloc_141_, 9, v_snapshotTasks_114_);
v___x_136_ = v_reuseFailAlloc_141_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_st_ref_put(v___y_96_, v___x_136_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_123_);
v___x_139_ = v___x_102_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_123_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object* v_cls_146_, lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_146_, v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_ks_158_; lean_object* v_vs_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_183_; 
v_ks_158_ = lean_ctor_get(v_x_154_, 0);
v_vs_159_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_183_ == 0)
{
v___x_161_ = v_x_154_;
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_vs_159_);
lean_inc(v_ks_158_);
lean_dec(v_x_154_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_ks_158_);
v___x_164_ = lean_nat_dec_lt(v_x_155_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_x_155_);
v___x_165_ = lean_array_push(v_ks_158_, v_x_156_);
v___x_166_ = lean_array_push(v_vs_159_, v_x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_166_);
lean_ctor_set(v___x_161_, 0, v___x_165_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
lean_object* v_k_x27_170_; uint8_t v___x_171_; 
v_k_x27_170_ = lean_array_fget_borrowed(v_ks_158_, v_x_155_);
v___x_171_ = l_Lean_instBEqMVarId_beq(v_x_156_, v_k_x27_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_173_; 
if (v_isShared_162_ == 0)
{
v___x_173_ = v___x_161_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_ks_158_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_vs_159_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_x_155_, v___x_174_);
lean_dec(v_x_155_);
v_x_154_ = v___x_173_;
v_x_155_ = v___x_175_;
goto _start;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_array_fset(v_ks_158_, v_x_155_, v_x_156_);
v___x_179_ = lean_array_fset(v_vs_159_, v_x_155_, v_x_157_);
lean_dec(v_x_155_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_179_);
lean_ctor_set(v___x_161_, 0, v___x_178_);
v___x_181_ = v___x_161_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_179_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_n_184_, lean_object* v_k_185_, lean_object* v_v_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_n_184_, v___x_187_, v_k_185_, v_v_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_190_, size_t v_x_191_, size_t v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v_es_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v_j_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_es_195_ = lean_ctor_get(v_x_190_, 0);
v___x_196_ = ((size_t)31ULL);
v___x_197_ = lean_usize_land(v_x_191_, v___x_196_);
v_j_198_ = lean_usize_to_nat(v___x_197_);
v___x_199_ = lean_array_get_size(v_es_195_);
v___x_200_ = lean_nat_dec_lt(v_j_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v_j_198_);
lean_dec(v_x_194_);
lean_dec(v_x_193_);
return v_x_190_;
}
else
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_239_; 
lean_inc_ref(v_es_195_);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_x_190_, 0);
lean_dec(v_unused_240_);
v___x_202_ = v_x_190_;
v_isShared_203_ = v_isSharedCheck_239_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_x_190_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_239_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_v_204_; lean_object* v___x_205_; lean_object* v_xs_x27_206_; lean_object* v___y_208_; 
v_v_204_ = lean_array_fget(v_es_195_, v_j_198_);
v___x_205_ = lean_box(0);
v_xs_x27_206_ = lean_array_fset(v_es_195_, v_j_198_, v___x_205_);
switch(lean_obj_tag(v_v_204_))
{
case 0:
{
lean_object* v_key_213_; lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_224_; 
v_key_213_ = lean_ctor_get(v_v_204_, 0);
v_val_214_ = lean_ctor_get(v_v_204_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_v_204_);
if (v_isSharedCheck_224_ == 0)
{
v___x_216_ = v_v_204_;
v_isShared_217_ = v_isSharedCheck_224_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_inc(v_key_213_);
lean_dec(v_v_204_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_224_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_instBEqMVarId_beq(v_x_193_, v_key_213_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_del_object(v___x_216_);
v___x_219_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_213_, v_val_214_, v_x_193_, v_x_194_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
v___y_208_ = v___x_220_;
goto v___jp_207_;
}
else
{
lean_object* v___x_222_; 
lean_dec(v_val_214_);
lean_dec(v_key_213_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v_x_194_);
lean_ctor_set(v___x_216_, 0, v_x_193_);
v___x_222_ = v___x_216_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_x_193_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_x_194_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v___y_208_ = v___x_222_;
goto v___jp_207_;
}
}
}
}
case 1:
{
lean_object* v_node_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_237_; 
v_node_225_ = lean_ctor_get(v_v_204_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_v_204_);
if (v_isSharedCheck_237_ == 0)
{
v___x_227_ = v_v_204_;
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_node_225_);
lean_dec(v_v_204_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_usize_shift_right(v_x_191_, v___x_229_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_x_192_, v___x_231_);
v___x_233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_node_225_, v___x_230_, v___x_232_, v_x_193_, v_x_194_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_233_);
v___x_235_ = v___x_227_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v___y_208_ = v___x_235_;
goto v___jp_207_;
}
}
}
default: 
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_x_193_);
lean_ctor_set(v___x_238_, 1, v_x_194_);
v___y_208_ = v___x_238_;
goto v___jp_207_;
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_array_fset(v_xs_x27_206_, v_j_198_, v___y_208_);
lean_dec(v_j_198_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_209_);
v___x_211_ = v___x_202_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v_ks_241_; lean_object* v_vs_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_260_; 
v_ks_241_ = lean_ctor_get(v_x_190_, 0);
v_vs_242_ = lean_ctor_get(v_x_190_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_260_ == 0)
{
v___x_244_ = v_x_190_;
v_isShared_245_ = v_isSharedCheck_260_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_vs_242_);
lean_inc(v_ks_241_);
lean_dec(v_x_190_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_260_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_ks_241_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_vs_242_);
v___x_247_ = v_reuseFailAlloc_259_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v_newNode_248_; size_t v___x_249_; uint8_t v___x_250_; 
v_newNode_248_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v___x_247_, v_x_193_, v_x_194_);
v___x_249_ = ((size_t)7ULL);
v___x_250_ = lean_usize_dec_le(v___x_249_, v_x_192_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_248_);
v___x_252_ = lean_unsigned_to_nat(4u);
v___x_253_ = lean_nat_dec_lt(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
if (v___x_253_ == 0)
{
lean_object* v_ks_254_; lean_object* v_vs_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_ks_254_ = lean_ctor_get(v_newNode_248_, 0);
lean_inc_ref(v_ks_254_);
v_vs_255_ = lean_ctor_get(v_newNode_248_, 1);
lean_inc_ref(v_vs_255_);
lean_dec_ref(v_newNode_248_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_192_, v_ks_254_, v_vs_255_, v___x_256_, v___x_257_);
lean_dec_ref(v_vs_255_);
lean_dec_ref(v_ks_254_);
return v___x_258_;
}
else
{
return v_newNode_248_;
}
}
else
{
return v_newNode_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(size_t v_depth_261_, lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_entries_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_keys_262_);
v___x_267_ = lean_nat_dec_lt(v_i_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_i_264_);
return v_entries_265_;
}
else
{
lean_object* v_k_268_; lean_object* v_v_269_; uint64_t v___x_270_; size_t v_h_271_; size_t v___x_272_; lean_object* v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v_h_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_k_268_ = lean_array_fget_borrowed(v_keys_262_, v_i_264_);
v_v_269_ = lean_array_fget_borrowed(v_vals_263_, v_i_264_);
v___x_270_ = l_Lean_instHashableMVarId_hash(v_k_268_);
v_h_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = ((size_t)5ULL);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_sub(v_depth_261_, v___x_274_);
v___x_276_ = lean_usize_mul(v___x_272_, v___x_275_);
v_h_277_ = lean_usize_shift_right(v_h_271_, v___x_276_);
v___x_278_ = lean_nat_add(v_i_264_, v___x_273_);
lean_dec(v_i_264_);
lean_inc(v_v_269_);
lean_inc(v_k_268_);
v___x_279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_entries_265_, v_h_277_, v_depth_261_, v_k_268_, v_v_269_);
v_i_264_ = v___x_278_;
v_entries_265_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
size_t v_depth_boxed_286_; lean_object* v_res_287_; 
v_depth_boxed_286_ = lean_unbox_usize(v_depth_281_);
lean_dec(v_depth_281_);
v_res_287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_boxed_286_, v_keys_282_, v_vals_283_, v_i_284_, v_entries_285_);
lean_dec_ref(v_vals_283_);
lean_dec_ref(v_keys_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
size_t v_x_9216__boxed_293_; size_t v_x_9217__boxed_294_; lean_object* v_res_295_; 
v_x_9216__boxed_293_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_x_9217__boxed_294_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_res_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_288_, v_x_9216__boxed_293_, v_x_9217__boxed_294_, v_x_291_, v_x_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint64_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_299_ = l_Lean_instHashableMVarId_hash(v_x_297_);
v___x_300_ = lean_uint64_to_usize(v___x_299_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_296_, v___x_300_, v___x_301_, v_x_297_, v_x_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(lean_object* v_mvarId_303_, lean_object* v_val_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_mctx_308_; lean_object* v_cache_309_; lean_object* v_zetaDeltaFVarIds_310_; lean_object* v_postponed_311_; lean_object* v_diag_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_342_; 
v___x_307_ = lean_st_ref_take(v___y_305_);
v_mctx_308_ = lean_ctor_get(v___x_307_, 0);
v_cache_309_ = lean_ctor_get(v___x_307_, 1);
v_zetaDeltaFVarIds_310_ = lean_ctor_get(v___x_307_, 2);
v_postponed_311_ = lean_ctor_get(v___x_307_, 3);
v_diag_312_ = lean_ctor_get(v___x_307_, 4);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_342_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_342_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_diag_312_);
lean_inc(v_postponed_311_);
lean_inc(v_zetaDeltaFVarIds_310_);
lean_inc(v_cache_309_);
lean_inc(v_mctx_308_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_342_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_depth_316_; lean_object* v_levelAssignDepth_317_; lean_object* v_lmvarCounter_318_; lean_object* v_mvarCounter_319_; lean_object* v_lDecls_320_; lean_object* v_decls_321_; lean_object* v_userNames_322_; lean_object* v_lAssignment_323_; lean_object* v_eAssignment_324_; lean_object* v_dAssignment_325_; lean_object* v_instanceTypedMVars_326_; lean_object* v_synthNormMemo_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_341_; 
v_depth_316_ = lean_ctor_get(v_mctx_308_, 0);
v_levelAssignDepth_317_ = lean_ctor_get(v_mctx_308_, 1);
v_lmvarCounter_318_ = lean_ctor_get(v_mctx_308_, 2);
v_mvarCounter_319_ = lean_ctor_get(v_mctx_308_, 3);
v_lDecls_320_ = lean_ctor_get(v_mctx_308_, 4);
v_decls_321_ = lean_ctor_get(v_mctx_308_, 5);
v_userNames_322_ = lean_ctor_get(v_mctx_308_, 6);
v_lAssignment_323_ = lean_ctor_get(v_mctx_308_, 7);
v_eAssignment_324_ = lean_ctor_get(v_mctx_308_, 8);
v_dAssignment_325_ = lean_ctor_get(v_mctx_308_, 9);
v_instanceTypedMVars_326_ = lean_ctor_get(v_mctx_308_, 10);
v_synthNormMemo_327_ = lean_ctor_get(v_mctx_308_, 11);
v_isSharedCheck_341_ = !lean_is_exclusive(v_mctx_308_);
if (v_isSharedCheck_341_ == 0)
{
v___x_329_ = v_mctx_308_;
v_isShared_330_ = v_isSharedCheck_341_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_synthNormMemo_327_);
lean_inc(v_instanceTypedMVars_326_);
lean_inc(v_dAssignment_325_);
lean_inc(v_eAssignment_324_);
lean_inc(v_lAssignment_323_);
lean_inc(v_userNames_322_);
lean_inc(v_decls_321_);
lean_inc(v_lDecls_320_);
lean_inc(v_mvarCounter_319_);
lean_inc(v_lmvarCounter_318_);
lean_inc(v_levelAssignDepth_317_);
lean_inc(v_depth_316_);
lean_dec(v_mctx_308_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_341_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_box(0);
v___x_332_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_eAssignment_324_, v_mvarId_303_, v_val_304_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 8, v___x_332_);
v___x_334_ = v___x_329_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_depth_316_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_levelAssignDepth_317_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_lmvarCounter_318_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_mvarCounter_319_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_lDecls_320_);
lean_ctor_set(v_reuseFailAlloc_340_, 5, v_decls_321_);
lean_ctor_set(v_reuseFailAlloc_340_, 6, v_userNames_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 7, v_lAssignment_323_);
lean_ctor_set(v_reuseFailAlloc_340_, 8, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 9, v_dAssignment_325_);
lean_ctor_set(v_reuseFailAlloc_340_, 10, v_instanceTypedMVars_326_);
lean_ctor_set(v_reuseFailAlloc_340_, 11, v_synthNormMemo_327_);
v___x_334_ = v_reuseFailAlloc_340_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_334_);
v___x_336_ = v___x_314_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_zetaDeltaFVarIds_310_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_postponed_311_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_diag_312_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_st_ref_put(v___y_305_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_331_);
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(lean_object* v_mvarId_343_, lean_object* v_val_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_343_, v_val_344_, v___y_345_);
lean_dec(v___y_345_);
return v_res_347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5));
v___x_360_ = l_Lean_Name_append(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_unsigned_to_nat(16u);
v___x_378_ = lean_mk_array(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14);
v___x_387_ = 1;
v___x_388_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_385_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*2, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(32u);
v___x_395_ = lean_mk_empty_array_with_capacity(v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21(void){
_start:
{
size_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_397_ = ((size_t)5ULL);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_unsigned_to_nat(32u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20);
v___x_402_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_398_);
lean_ctor_set(v___x_402_, 3, v___x_398_);
lean_ctor_set_usize(v___x_402_, 4, v___x_397_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21);
v___x_404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v___x_404_);
lean_ctor_set(v___x_405_, 3, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22);
v___x_407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object* v_mvarId_421_, lean_object* v_h_422_, lean_object* v_lhs_423_, lean_object* v_rhs_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_a_431_; lean_object* v___y_449_; lean_object* v___y_460_; lean_object* v___y_464_; uint8_t v___y_465_; lean_object* v_a_491_; lean_object* v___y_495_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11));
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_mk_empty_array_with_capacity(v___x_498_);
lean_inc_ref(v___x_499_);
v___x_500_ = lean_array_push(v___x_499_, v_lhs_423_);
v___x_501_ = l_Lean_Meta_mkAppM(v___x_497_, v___x_500_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
lean_inc_ref(v___x_499_);
v___x_503_ = lean_array_push(v___x_499_, v_rhs_424_);
v___x_504_ = l_Lean_Meta_mkAppM(v___x_497_, v___x_503_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
lean_inc(v_a_502_);
v___x_506_ = l_Lean_Meta_mkLT(v_a_502_, v_a_505_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_box(0);
v___x_509_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_507_, v___x_508_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_428_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_unsigned_to_nat(2u);
v___x_514_ = 0;
v___x_515_ = 1;
v___x_519_ = lean_box(0);
v___x_520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12));
lean_inc_ref(v___x_499_);
v___x_521_ = lean_array_push(v___x_499_, v_a_512_);
v___x_522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
v___x_523_ = l_Lean_Options_empty;
v___x_524_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_520_, v___x_521_, v___x_522_, v___x_523_, v_a_425_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Expr_mvarId_x21(v_a_510_);
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18));
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23);
v___x_529_ = l_Lean_Meta_simpTarget(v___x_526_, v_a_525_, v___x_527_, v___x_519_, v___x_515_, v___x_528_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_578_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_578_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_578_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_578_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; 
v_fst_534_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_fst_534_);
lean_dec(v_a_530_);
if (lean_obj_tag(v_fst_534_) == 0)
{
lean_object* v___x_535_; 
lean_del_object(v___x_532_);
v___x_535_ = l_Lean_Meta_mkEqSymm(v_h_422_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v___x_537_ = l_Lean_Expr_appFn_x21(v_a_502_);
v___x_538_ = l_Lean_Meta_mkCongrArg(v___x_537_, v_a_536_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26));
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_513_);
v___x_542_ = lean_array_push(v___x_541_, v_a_510_);
v___x_543_ = lean_array_push(v___x_542_, v_a_539_);
v___x_544_ = l_Lean_Meta_mkAppM(v___x_540_, v___x_543_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28));
v___x_547_ = lean_array_push(v___x_499_, v_a_502_);
v___x_548_ = l_Lean_Meta_mkAppM(v___x_546_, v___x_547_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
lean_inc(v_mvarId_421_);
v___x_550_ = l_Lean_MVarId_getType(v_mvarId_421_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = l_Lean_Expr_app___override(v_a_549_, v_a_545_);
v___x_553_ = l_Lean_Meta_mkFalseElim(v_a_551_, v___x_552_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v_toCold_556_; lean_object* v_options_557_; uint8_t v_hasTrace_558_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_421_, v_a_554_, v_a_426_);
lean_dec_ref(v___x_555_);
v_toCold_556_ = lean_ctor_get(v_a_427_, 0);
v_options_557_ = lean_ctor_get(v_toCold_556_, 2);
v_hasTrace_558_ = lean_ctor_get_uint8(v_options_557_, sizeof(void*)*1);
if (v_hasTrace_558_ == 0)
{
goto v___jp_516_;
}
else
{
lean_object* v_inheritedTraceOptions_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_inheritedTraceOptions_559_ = lean_ctor_get(v_toCold_556_, 11);
v___x_560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_559_, v_options_557_, v___x_561_);
if (v___x_562_ == 0)
{
goto v___jp_516_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30);
v___x_564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_560_, v___x_563_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_515_, v_a_565_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
v___y_495_ = v___x_566_;
goto v___jp_494_;
}
else
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_564_, 1);
v_a_491_ = v_a_567_;
goto v___jp_490_;
}
}
}
}
else
{
lean_object* v_a_568_; 
lean_dec(v_mvarId_421_);
v_a_568_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_553_, 1);
v_a_491_ = v_a_568_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_569_; 
lean_dec(v_a_549_);
lean_dec(v_a_545_);
lean_dec(v_mvarId_421_);
v_a_569_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_550_, 1);
v_a_491_ = v_a_569_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_570_; 
lean_dec(v_a_545_);
lean_dec(v_mvarId_421_);
v_a_570_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_548_, 1);
v_a_491_ = v_a_570_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_571_; 
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec(v_mvarId_421_);
v_a_571_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_544_, 1);
v_a_491_ = v_a_571_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_572_; 
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec(v_mvarId_421_);
v_a_572_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_538_, 1);
v_a_491_ = v_a_572_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_573_; 
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec(v_mvarId_421_);
v_a_573_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_535_, 1);
v_a_491_ = v_a_573_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec_ref_known(v_fst_534_, 1);
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v___x_574_ = lean_box(v___x_514_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_574_);
v___x_576_ = v___x_532_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_a_579_; 
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_579_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_529_, 1);
v_a_491_ = v_a_579_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_580_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_524_, 1);
v_a_491_ = v_a_580_;
goto v___jp_490_;
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_515_, v___x_517_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
v___y_495_ = v___x_518_;
goto v___jp_494_;
}
}
else
{
lean_object* v_a_581_; 
lean_dec(v_a_510_);
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_581_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_511_, 1);
v_a_491_ = v_a_581_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_582_; 
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_582_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_509_, 1);
v_a_491_ = v_a_582_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_583_; 
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_583_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_506_, 1);
v_a_491_ = v_a_583_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_584_; 
lean_dec(v_a_502_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_584_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_504_, 1);
v_a_491_ = v_a_584_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_585_; 
lean_dec_ref(v___x_499_);
lean_dec_ref(v_rhs_424_);
lean_dec_ref(v_h_422_);
lean_dec(v_mvarId_421_);
v_a_585_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_501_, 1);
v_a_491_ = v_a_585_;
goto v___jp_490_;
}
v___jp_430_:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v_a_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_a_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v_a_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v_a_431_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v_a_431_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v_a_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 0);
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
v___jp_448_:
{
if (lean_obj_tag(v___y_449_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___y_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___y_449_, 1);
v_a_431_ = v_a_450_;
goto v___jp_430_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___y_449_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___y_449_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___y_449_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___y_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(0);
lean_inc(v_a_428_);
lean_inc_ref(v_a_427_);
lean_inc(v_a_426_);
lean_inc_ref(v_a_425_);
v___x_462_ = lean_apply_6(v___y_460_, v___x_461_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, lean_box(0));
v___y_449_ = v___x_462_;
goto v___jp_448_;
}
v___jp_463_:
{
if (v___y_465_ == 0)
{
lean_object* v_toCold_466_; lean_object* v_options_467_; lean_object* v_inheritedTraceOptions_468_; uint8_t v_hasTrace_469_; lean_object* v___x_470_; lean_object* v___f_471_; 
v_toCold_466_ = lean_ctor_get(v_a_427_, 0);
v_options_467_ = lean_ctor_get(v_toCold_466_, 2);
v_inheritedTraceOptions_468_ = lean_ctor_get(v_toCold_466_, 11);
v_hasTrace_469_ = lean_ctor_get_uint8(v_options_467_, sizeof(void*)*1);
v___x_470_ = lean_box(v___y_465_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_471_, 0, v___x_470_);
if (v_hasTrace_469_ == 0)
{
lean_dec_ref(v___y_464_);
v___y_460_ = v___f_471_;
goto v___jp_459_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_474_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_468_, v_options_467_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec_ref(v___y_464_);
v___y_460_ = v___f_471_;
goto v___jp_459_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v___f_471_);
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8);
v___x_476_ = l_Lean_Exception_toMessageData(v___y_464_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_472_, v___x_477_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_465_, v_a_479_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
v___y_449_ = v___x_480_;
goto v___jp_448_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_a_481_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_478_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_478_);
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
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___y_464_);
return v___x_489_;
}
}
v___jp_490_:
{
uint8_t v___x_492_; 
v___x_492_ = l_Lean_Exception_isInterrupt(v_a_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
lean_inc_ref(v_a_491_);
v___x_493_ = l_Lean_Exception_isRuntime(v_a_491_);
v___y_464_ = v_a_491_;
v___y_465_ = v___x_493_;
goto v___jp_463_;
}
else
{
v___y_464_ = v_a_491_;
v___y_465_ = v___x_492_;
goto v___jp_463_;
}
}
v___jp_494_:
{
lean_object* v_a_496_; 
v_a_496_ = lean_ctor_get(v___y_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___y_495_);
v_a_431_ = v_a_496_;
goto v___jp_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object* v_mvarId_586_, lean_object* v_h_587_, lean_object* v_lhs_588_, lean_object* v_rhs_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_586_, v_h_587_, v_lhs_588_, v_rhs_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object* v_mvarId_596_, lean_object* v_val_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_596_, v_val_597_, v___y_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object* v_mvarId_604_, lean_object* v_val_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_604_, v_val_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_x_613_, v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, size_t v_x_619_, size_t v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_618_, v_x_619_, v_x_620_, v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_10041__boxed_630_; size_t v_x_10042__boxed_631_; lean_object* v_res_632_; 
v_x_10041__boxed_630_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_x_10042__boxed_631_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_res_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(v_00_u03b2_624_, v_x_625_, v_x_10041__boxed_630_, v_x_10042__boxed_631_, v_x_628_, v_x_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_633_, lean_object* v_n_634_, lean_object* v_k_635_, lean_object* v_v_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v_n_634_, v_k_635_, v_v_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_638_, size_t v_depth_639_, lean_object* v_keys_640_, lean_object* v_vals_641_, lean_object* v_heq_642_, lean_object* v_i_643_, lean_object* v_entries_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_639_, v_keys_640_, v_vals_641_, v_i_643_, v_entries_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_646_, lean_object* v_depth_647_, lean_object* v_keys_648_, lean_object* v_vals_649_, lean_object* v_heq_650_, lean_object* v_i_651_, lean_object* v_entries_652_){
_start:
{
size_t v_depth_boxed_653_; lean_object* v_res_654_; 
v_depth_boxed_653_ = lean_unbox_usize(v_depth_647_);
lean_dec(v_depth_647_);
v_res_654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(v_00_u03b2_646_, v_depth_boxed_653_, v_keys_648_, v_vals_649_, v_heq_650_, v_i_651_, v_entries_652_);
lean_dec_ref(v_vals_649_);
lean_dec_ref(v_keys_648_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_x_656_, v_x_657_, v_x_658_, v_x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object* v_mvarId_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_a_677_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object* v_mvarId_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_685_, v_x_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object* v_00_u03b1_693_, lean_object* v_mvarId_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object* v_00_u03b1_702_, lean_object* v_mvarId_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(v_00_u03b1_702_, v_mvarId_703_, v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_710_;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__2));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* v_h_717_, lean_object* v_mvarId_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc_ref(v_h_717_);
v___x_724_ = lean_infer_type(v_h_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = l_Lean_Meta_whnfD(v_a_725_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_783_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_783_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_783_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_783_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v_toCold_764_; lean_object* v_options_765_; uint8_t v_hasTrace_766_; 
v_toCold_764_ = lean_ctor_get(v___y_721_, 0);
v_options_765_ = lean_ctor_get(v_toCold_764_, 2);
v_hasTrace_766_ = lean_ctor_get_uint8(v_options_765_, sizeof(void*)*1);
if (v_hasTrace_766_ == 0)
{
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
v___y_735_ = v___y_722_;
goto v___jp_731_;
}
else
{
lean_object* v_inheritedTraceOptions_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_inheritedTraceOptions_767_ = lean_ctor_get(v_toCold_764_, 11);
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_767_, v_options_765_, v___x_769_);
if (v___x_770_ == 0)
{
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
v___y_735_ = v___y_722_;
goto v___jp_731_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_771_ = lean_obj_once(&l_Lean_MVarId_acyclic___lam__0___closed__3, &l_Lean_MVarId_acyclic___lam__0___closed__3_once, _init_l_Lean_MVarId_acyclic___lam__0___closed__3);
lean_inc(v_a_727_);
v___x_772_ = l_Lean_MessageData_ofExpr(v_a_727_);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_768_, v___x_773_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec_ref_known(v___x_774_, 1);
v___y_732_ = v___y_719_;
v___y_733_ = v___y_720_;
v___y_734_ = v___y_721_;
v___y_735_ = v___y_722_;
goto v___jp_731_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_del_object(v___x_729_);
lean_dec(v_a_727_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
v___jp_731_:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__1));
v___x_737_ = lean_unsigned_to_nat(3u);
v___x_738_ = l_Lean_Expr_isAppOfArity(v_a_727_, v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_a_727_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
v___x_739_ = lean_box(v___x_738_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_739_);
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_del_object(v___x_729_);
v___x_743_ = l_Lean_Expr_appFn_x21(v_a_727_);
v___x_744_ = l_Lean_Expr_appArg_x21(v___x_743_);
lean_dec_ref(v___x_743_);
v___x_745_ = l_Lean_Expr_appArg_x21(v_a_727_);
lean_dec(v_a_727_);
lean_inc_ref(v___x_745_);
lean_inc_ref(v___x_744_);
v___x_746_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_744_, v___x_745_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_inc_ref(v___x_744_);
lean_inc_ref(v___x_745_);
v___x_749_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_745_, v___x_744_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; uint8_t v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v___x_751_ = lean_unbox(v_a_750_);
if (v___x_751_ == 0)
{
lean_dec_ref(v___x_745_);
lean_dec_ref(v___x_744_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
return v___x_749_;
}
else
{
lean_object* v___x_752_; 
lean_dec_ref_known(v___x_749_, 1);
v___x_752_ = l_Lean_Meta_mkEqSymm(v_h_717_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_718_, v_a_753_, v___x_745_, v___x_744_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v___x_744_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_mvarId_718_);
v_a_755_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_752_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_752_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_745_);
lean_dec_ref(v___x_744_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
return v___x_749_;
}
}
else
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_718_, v_h_717_, v___x_744_, v___x_745_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v___x_763_;
}
}
else
{
lean_dec_ref(v___x_745_);
lean_dec_ref(v___x_744_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
v_a_784_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_726_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_726_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_h_717_);
v_a_792_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_724_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_724_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object* v_h_800_, lean_object* v_mvarId_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_MVarId_acyclic___lam__0(v_h_800_, v_mvarId_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* v_mvarId_808_, lean_object* v_h_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___f_815_; lean_object* v___x_816_; 
lean_inc(v_mvarId_808_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0___boxed), 7, 2);
lean_closure_set(v___f_815_, 0, v_h_809_);
lean_closure_set(v___f_815_, 1, v_mvarId_808_);
v___x_816_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_808_, v___f_815_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* v_mvarId_817_, lean_object* v_h_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_MVarId_acyclic(v_mvarId_817_, v_h_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_889_ = 0;
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_));
v___x_891_ = l_Lean_registerTraceClass(v___x_888_, v___x_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
return v_res_893_;
}
}
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
