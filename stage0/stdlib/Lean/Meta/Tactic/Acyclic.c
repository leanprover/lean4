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
lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object* v_lhs_1_, lean_object* v_rhs_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1_ = stack[0].m_obj;
lean_object* v_rhs_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_15_;
v_res_15_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v_lhs_1_, v_rhs_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(lean_object* v_lhs_16_, lean_object* v_rhs_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v_lhs_16_, v_rhs_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
return v_res_23_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t v___y_24_, lean_object* v_____r_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(v___y_24_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_24_ = stack[0].m_num;
lean_object* v_____r_25_ = stack[1].m_obj;
lean_object* v___y_26_ = stack[2].m_obj;
lean_object* v___y_27_ = stack[3].m_obj;
lean_object* v___y_28_ = stack[4].m_obj;
lean_object* v___y_29_ = stack[5].m_obj;
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_24_, v_____r_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object* v___y_35_, lean_object* v_____r_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
uint8_t v___y_8957__boxed_42_; lean_object* v_res_43_; 
v___y_8957__boxed_42_ = lean_unbox(v___y_35_);
v_res_43_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_8957__boxed_42_, v_____r_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_43_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t v___x_44_, lean_object* v_____r_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(v___x_44_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_44_ = stack[0].m_num;
lean_object* v_____r_45_ = stack[1].m_obj;
lean_object* v___y_46_ = stack[2].m_obj;
lean_object* v___y_47_ = stack[3].m_obj;
lean_object* v___y_48_ = stack[4].m_obj;
lean_object* v___y_49_ = stack[5].m_obj;
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_44_, v_____r_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object* v___x_55_, lean_object* v_____r_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
uint8_t v___x_9001__boxed_62_; lean_object* v_res_63_; 
v___x_9001__boxed_62_ = lean_unbox(v___x_55_);
v_res_63_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_9001__boxed_62_, v_____r_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_63_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(lean_object* v_msgData_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; uint8_t v___x_72_; lean_object* v_env_73_; lean_object* v___x_74_; lean_object* v_toCold_75_; lean_object* v_mctx_76_; lean_object* v_lctx_77_; lean_object* v_options_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = 0;
v_env_73_ = l_Lean_Environment_setRecordingDeps(v_env_71_, v___x_72_);
v___x_74_ = lean_st_ref_get(v___y_66_);
v_toCold_75_ = lean_ctor_get(v___y_67_, 0);
v_mctx_76_ = lean_ctor_get(v___x_74_, 0);
lean_inc_ref(v_mctx_76_);
lean_dec(v___x_74_);
v_lctx_77_ = lean_ctor_get(v___y_65_, 2);
v_options_78_ = lean_ctor_get(v_toCold_75_, 2);
lean_inc_ref(v_options_78_);
lean_inc_ref(v_lctx_77_);
v___x_79_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_79_, 0, v_env_73_);
lean_ctor_set(v___x_79_, 1, v_mctx_76_);
lean_ctor_set(v___x_79_, 2, v_lctx_77_);
lean_ctor_set(v___x_79_, 3, v_options_78_);
v___x_80_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_msgData_64_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_64_ = stack[0].m_obj;
lean_object* v___y_65_ = stack[1].m_obj;
lean_object* v___y_66_ = stack[2].m_obj;
lean_object* v___y_67_ = stack[3].m_obj;
lean_object* v___y_68_ = stack[4].m_obj;
lean_object* v_res_82_;
v_res_82_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msgData_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0___boxed(lean_object* v_msgData_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msgData_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_90_; double v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_float_of_nat(v___x_90_);
return v___x_91_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object* v_cls_95_, lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_ref_102_; lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_149_; 
v_ref_102_ = lean_ctor_get(v___y_99_, 2);
v___x_103_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msg_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_149_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_149_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_149_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v_traceState_109_; lean_object* v_env_110_; lean_object* v_nextMacroScope_111_; lean_object* v_ngen_112_; lean_object* v_auxDeclNGen_113_; lean_object* v_cache_114_; lean_object* v_recordedDeps_115_; lean_object* v_messages_116_; lean_object* v_infoState_117_; lean_object* v_snapshotTasks_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_148_; 
v___x_108_ = lean_st_ref_take(v___y_100_);
v_traceState_109_ = lean_ctor_get(v___x_108_, 4);
v_env_110_ = lean_ctor_get(v___x_108_, 0);
v_nextMacroScope_111_ = lean_ctor_get(v___x_108_, 1);
v_ngen_112_ = lean_ctor_get(v___x_108_, 2);
v_auxDeclNGen_113_ = lean_ctor_get(v___x_108_, 3);
v_cache_114_ = lean_ctor_get(v___x_108_, 5);
v_recordedDeps_115_ = lean_ctor_get(v___x_108_, 6);
v_messages_116_ = lean_ctor_get(v___x_108_, 7);
v_infoState_117_ = lean_ctor_get(v___x_108_, 8);
v_snapshotTasks_118_ = lean_ctor_get(v___x_108_, 9);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_148_ == 0)
{
v___x_120_ = v___x_108_;
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snapshotTasks_118_);
lean_inc(v_infoState_117_);
lean_inc(v_messages_116_);
lean_inc(v_recordedDeps_115_);
lean_inc(v_cache_114_);
lean_inc(v_traceState_109_);
lean_inc(v_auxDeclNGen_113_);
lean_inc(v_ngen_112_);
lean_inc(v_nextMacroScope_111_);
lean_inc(v_env_110_);
lean_dec(v___x_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint64_t v_tid_122_; lean_object* v_traces_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_147_; 
v_tid_122_ = lean_ctor_get_uint64(v_traceState_109_, sizeof(void*)*1);
v_traces_123_ = lean_ctor_get(v_traceState_109_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_traceState_109_);
if (v_isSharedCheck_147_ == 0)
{
v___x_125_ = v_traceState_109_;
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_traces_123_);
lean_dec(v_traceState_109_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; double v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_box(0);
v___x_129_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0);
v___x_130_ = 0;
v___x_131_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1));
v___x_132_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_132_, 0, v_cls_95_);
lean_ctor_set(v___x_132_, 1, v___x_128_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
lean_ctor_set_float(v___x_132_, sizeof(void*)*3, v___x_129_);
lean_ctor_set_float(v___x_132_, sizeof(void*)*3 + 8, v___x_129_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 16, v___x_130_);
v___x_133_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2));
v___x_134_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v_a_104_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_inc(v_ref_102_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_ref_102_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_Lean_PersistentArray_push___redArg(v_traces_123_, v___x_135_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_136_);
v___x_138_ = v___x_125_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_136_);
lean_ctor_set_uint64(v_reuseFailAlloc_146_, sizeof(void*)*1, v_tid_122_);
v___x_138_ = v_reuseFailAlloc_146_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v___x_138_);
v___x_140_ = v___x_120_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_env_110_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_nextMacroScope_111_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_ngen_112_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_auxDeclNGen_113_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_cache_114_);
lean_ctor_set(v_reuseFailAlloc_145_, 6, v_recordedDeps_115_);
lean_ctor_set(v_reuseFailAlloc_145_, 7, v_messages_116_);
lean_ctor_set(v_reuseFailAlloc_145_, 8, v_infoState_117_);
lean_ctor_set(v_reuseFailAlloc_145_, 9, v_snapshotTasks_118_);
v___x_140_ = v_reuseFailAlloc_145_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_st_ref_put(v___y_100_, v___x_140_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_127_);
v___x_143_ = v___x_106_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_127_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_95_ = stack[0].m_obj;
lean_object* v_msg_96_ = stack[1].m_obj;
lean_object* v___y_97_ = stack[2].m_obj;
lean_object* v___y_98_ = stack[3].m_obj;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v___y_100_ = stack[5].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_95_, v_msg_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object* v_cls_151_, lean_object* v_msg_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_151_, v_msg_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_ks_163_; lean_object* v_vs_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_188_; 
v_ks_163_ = lean_ctor_get(v_x_159_, 0);
v_vs_164_ = lean_ctor_get(v_x_159_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_188_ == 0)
{
v___x_166_ = v_x_159_;
v_isShared_167_ = v_isSharedCheck_188_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_vs_164_);
lean_inc(v_ks_163_);
lean_dec(v_x_159_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_188_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_array_get_size(v_ks_163_);
v___x_169_ = lean_nat_dec_lt(v_x_160_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
lean_dec(v_x_160_);
v___x_170_ = lean_array_push(v_ks_163_, v_x_161_);
v___x_171_ = lean_array_push(v_vs_164_, v_x_162_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_171_);
lean_ctor_set(v___x_166_, 0, v___x_170_);
v___x_173_ = v___x_166_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
else
{
lean_object* v_k_x27_175_; uint8_t v___x_176_; 
v_k_x27_175_ = lean_array_fget_borrowed(v_ks_163_, v_x_160_);
v___x_176_ = l_Lean_instBEqMVarId_beq(v_x_161_, v_k_x27_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_178_; 
if (v_isShared_167_ == 0)
{
v___x_178_ = v___x_166_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_ks_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_vs_164_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_x_160_, v___x_179_);
lean_dec(v_x_160_);
v_x_159_ = v___x_178_;
v_x_160_ = v___x_180_;
goto _start;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = lean_array_fset(v_ks_163_, v_x_160_, v_x_161_);
v___x_184_ = lean_array_fset(v_vs_164_, v_x_160_, v_x_162_);
lean_dec(v_x_160_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_184_);
lean_ctor_set(v___x_166_, 0, v___x_183_);
v___x_186_ = v___x_166_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_n_189_, lean_object* v_k_190_, lean_object* v_v_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_n_189_, v___x_192_, v_k_190_, v_v_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_194_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_195_, size_t v_x_196_, size_t v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v_es_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v_j_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_es_200_ = lean_ctor_get(v_x_195_, 0);
v___x_201_ = ((size_t)31ULL);
v___x_202_ = lean_usize_land(v_x_196_, v___x_201_);
v_j_203_ = lean_usize_to_nat(v___x_202_);
v___x_204_ = lean_array_get_size(v_es_200_);
v___x_205_ = lean_nat_dec_lt(v_j_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_j_203_);
lean_dec(v_x_199_);
lean_dec(v_x_198_);
return v_x_195_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_244_; 
lean_inc_ref(v_es_200_);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_x_195_, 0);
lean_dec(v_unused_245_);
v___x_207_ = v_x_195_;
v_isShared_208_ = v_isSharedCheck_244_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_x_195_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_244_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_v_209_; lean_object* v___x_210_; lean_object* v_xs_x27_211_; lean_object* v___y_213_; 
v_v_209_ = lean_array_fget(v_es_200_, v_j_203_);
v___x_210_ = lean_box(0);
v_xs_x27_211_ = lean_array_fset(v_es_200_, v_j_203_, v___x_210_);
switch(lean_obj_tag(v_v_209_))
{
case 0:
{
lean_object* v_key_218_; lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_key_218_ = lean_ctor_get(v_v_209_, 0);
v_val_219_ = lean_ctor_get(v_v_209_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_v_209_);
if (v_isSharedCheck_229_ == 0)
{
v___x_221_ = v_v_209_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_inc(v_key_218_);
lean_dec(v_v_209_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_instBEqMVarId_beq(v_x_198_, v_key_218_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_221_);
v___x_224_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_218_, v_val_219_, v_x_198_, v_x_199_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___y_213_ = v___x_225_;
goto v___jp_212_;
}
else
{
lean_object* v___x_227_; 
lean_dec(v_val_219_);
lean_dec(v_key_218_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v_x_199_);
lean_ctor_set(v___x_221_, 0, v_x_198_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_x_198_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_x_199_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
v___y_213_ = v___x_227_;
goto v___jp_212_;
}
}
}
}
case 1:
{
lean_object* v_node_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_242_; 
v_node_230_ = lean_ctor_get(v_v_209_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_v_209_);
if (v_isSharedCheck_242_ == 0)
{
v___x_232_ = v_v_209_;
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_node_230_);
lean_dec(v_v_209_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_234_ = ((size_t)5ULL);
v___x_235_ = lean_usize_shift_right(v_x_196_, v___x_234_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_x_197_, v___x_236_);
v___x_238_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_node_230_, v___x_235_, v___x_237_, v_x_198_, v_x_199_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_238_);
v___x_240_ = v___x_232_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v___y_213_ = v___x_240_;
goto v___jp_212_;
}
}
}
default: 
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_x_198_);
lean_ctor_set(v___x_243_, 1, v_x_199_);
v___y_213_ = v___x_243_;
goto v___jp_212_;
}
}
v___jp_212_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_array_fset(v_xs_x27_211_, v_j_203_, v___y_213_);
lean_dec(v_j_203_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_216_ = v___x_207_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
else
{
lean_object* v_ks_246_; lean_object* v_vs_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_265_; 
v_ks_246_ = lean_ctor_get(v_x_195_, 0);
v_vs_247_ = lean_ctor_get(v_x_195_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_265_ == 0)
{
v___x_249_ = v_x_195_;
v_isShared_250_ = v_isSharedCheck_265_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_vs_247_);
lean_inc(v_ks_246_);
lean_dec(v_x_195_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_265_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_ks_246_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_vs_247_);
v___x_252_ = v_reuseFailAlloc_264_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v_newNode_253_; size_t v___x_254_; uint8_t v___x_255_; 
v_newNode_253_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v___x_252_, v_x_198_, v_x_199_);
v___x_254_ = ((size_t)7ULL);
v___x_255_ = lean_usize_dec_le(v___x_254_, v_x_197_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_253_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
if (v___x_258_ == 0)
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_ks_259_ = lean_ctor_get(v_newNode_253_, 0);
lean_inc_ref(v_ks_259_);
v_vs_260_ = lean_ctor_get(v_newNode_253_, 1);
lean_inc_ref(v_vs_260_);
lean_dec_ref(v_newNode_253_);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_197_, v_ks_259_, v_vs_260_, v___x_261_, v___x_262_);
lean_dec_ref(v_vs_260_);
lean_dec_ref(v_ks_259_);
return v___x_263_;
}
else
{
return v_newNode_253_;
}
}
else
{
return v_newNode_253_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_195_ = stack[0].m_obj;
size_t v_x_196_ = stack[1].m_num;
size_t v_x_197_ = stack[2].m_num;
lean_object* v_x_198_ = stack[3].m_obj;
lean_object* v_x_199_ = stack[4].m_obj;
lean_object* v_res_266_;
v_res_266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_195_, v_x_196_, v_x_197_, v_x_198_, v_x_199_);
stack->m_obj
 = v_res_266_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(size_t v_depth_267_, lean_object* v_keys_268_, lean_object* v_vals_269_, lean_object* v_i_270_, lean_object* v_entries_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_array_get_size(v_keys_268_);
v___x_273_ = lean_nat_dec_lt(v_i_270_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_i_270_);
return v_entries_271_;
}
else
{
lean_object* v_k_274_; lean_object* v_v_275_; uint64_t v___x_276_; size_t v_h_277_; size_t v___x_278_; lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v_h_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_k_274_ = lean_array_fget_borrowed(v_keys_268_, v_i_270_);
v_v_275_ = lean_array_fget_borrowed(v_vals_269_, v_i_270_);
v___x_276_ = l_Lean_instHashableMVarId_hash(v_k_274_);
v_h_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = ((size_t)5ULL);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_sub(v_depth_267_, v___x_280_);
v___x_282_ = lean_usize_mul(v___x_278_, v___x_281_);
v_h_283_ = lean_usize_shift_right(v_h_277_, v___x_282_);
v___x_284_ = lean_nat_add(v_i_270_, v___x_279_);
lean_dec(v_i_270_);
lean_inc(v_v_275_);
lean_inc(v_k_274_);
v___x_285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_entries_271_, v_h_283_, v_depth_267_, v_k_274_, v_v_275_);
v_i_270_ = v___x_284_;
v_entries_271_ = v___x_285_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_267_ = stack[0].m_num;
lean_object* v_keys_268_ = stack[1].m_obj;
lean_object* v_vals_269_ = stack[2].m_obj;
lean_object* v_i_270_ = stack[3].m_obj;
lean_object* v_entries_271_ = stack[4].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_267_, v_keys_268_, v_vals_269_, v_i_270_, v_entries_271_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_depth_288_, lean_object* v_keys_289_, lean_object* v_vals_290_, lean_object* v_i_291_, lean_object* v_entries_292_){
_start:
{
size_t v_depth_boxed_293_; lean_object* v_res_294_; 
v_depth_boxed_293_ = lean_unbox_usize(v_depth_288_);
lean_dec(v_depth_288_);
v_res_294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_boxed_293_, v_keys_289_, v_vals_290_, v_i_291_, v_entries_292_);
lean_dec_ref(v_vals_290_);
lean_dec_ref(v_keys_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
size_t v_x_9347__boxed_300_; size_t v_x_9348__boxed_301_; lean_object* v_res_302_; 
v_x_9347__boxed_300_ = lean_unbox_usize(v_x_296_);
lean_dec(v_x_296_);
v_x_9348__boxed_301_ = lean_unbox_usize(v_x_297_);
lean_dec(v_x_297_);
v_res_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_295_, v_x_9347__boxed_300_, v_x_9348__boxed_301_, v_x_298_, v_x_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
uint64_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_306_ = l_Lean_instHashableMVarId_hash(v_x_304_);
v___x_307_ = lean_uint64_to_usize(v___x_306_);
v___x_308_ = ((size_t)1ULL);
v___x_309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_303_, v___x_307_, v___x_308_, v_x_304_, v_x_305_);
return v___x_309_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(lean_object* v_mvarId_310_, lean_object* v_val_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_cache_316_; lean_object* v_zetaDeltaFVarIds_317_; lean_object* v_postponed_318_; lean_object* v_diag_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_349_; 
v___x_314_ = lean_st_ref_take(v___y_312_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
v_cache_316_ = lean_ctor_get(v___x_314_, 1);
v_zetaDeltaFVarIds_317_ = lean_ctor_get(v___x_314_, 2);
v_postponed_318_ = lean_ctor_get(v___x_314_, 3);
v_diag_319_ = lean_ctor_get(v___x_314_, 4);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_349_ == 0)
{
v___x_321_ = v___x_314_;
v_isShared_322_ = v_isSharedCheck_349_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_diag_319_);
lean_inc(v_postponed_318_);
lean_inc(v_zetaDeltaFVarIds_317_);
lean_inc(v_cache_316_);
lean_inc(v_mctx_315_);
lean_dec(v___x_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_349_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_depth_323_; lean_object* v_levelAssignDepth_324_; lean_object* v_lmvarCounter_325_; lean_object* v_mvarCounter_326_; lean_object* v_lDecls_327_; lean_object* v_decls_328_; lean_object* v_userNames_329_; lean_object* v_lAssignment_330_; lean_object* v_eAssignment_331_; lean_object* v_dAssignment_332_; lean_object* v_instanceTypedMVars_333_; lean_object* v_synthNormMemo_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_348_; 
v_depth_323_ = lean_ctor_get(v_mctx_315_, 0);
v_levelAssignDepth_324_ = lean_ctor_get(v_mctx_315_, 1);
v_lmvarCounter_325_ = lean_ctor_get(v_mctx_315_, 2);
v_mvarCounter_326_ = lean_ctor_get(v_mctx_315_, 3);
v_lDecls_327_ = lean_ctor_get(v_mctx_315_, 4);
v_decls_328_ = lean_ctor_get(v_mctx_315_, 5);
v_userNames_329_ = lean_ctor_get(v_mctx_315_, 6);
v_lAssignment_330_ = lean_ctor_get(v_mctx_315_, 7);
v_eAssignment_331_ = lean_ctor_get(v_mctx_315_, 8);
v_dAssignment_332_ = lean_ctor_get(v_mctx_315_, 9);
v_instanceTypedMVars_333_ = lean_ctor_get(v_mctx_315_, 10);
v_synthNormMemo_334_ = lean_ctor_get(v_mctx_315_, 11);
v_isSharedCheck_348_ = !lean_is_exclusive(v_mctx_315_);
if (v_isSharedCheck_348_ == 0)
{
v___x_336_ = v_mctx_315_;
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_synthNormMemo_334_);
lean_inc(v_instanceTypedMVars_333_);
lean_inc(v_dAssignment_332_);
lean_inc(v_eAssignment_331_);
lean_inc(v_lAssignment_330_);
lean_inc(v_userNames_329_);
lean_inc(v_decls_328_);
lean_inc(v_lDecls_327_);
lean_inc(v_mvarCounter_326_);
lean_inc(v_lmvarCounter_325_);
lean_inc(v_levelAssignDepth_324_);
lean_inc(v_depth_323_);
lean_dec(v_mctx_315_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = lean_box(0);
v___x_339_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_eAssignment_331_, v_mvarId_310_, v_val_311_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 8, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_depth_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_levelAssignDepth_324_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_lmvarCounter_325_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_mvarCounter_326_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_lDecls_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 5, v_decls_328_);
lean_ctor_set(v_reuseFailAlloc_347_, 6, v_userNames_329_);
lean_ctor_set(v_reuseFailAlloc_347_, 7, v_lAssignment_330_);
lean_ctor_set(v_reuseFailAlloc_347_, 8, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 9, v_dAssignment_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 10, v_instanceTypedMVars_333_);
lean_ctor_set(v_reuseFailAlloc_347_, 11, v_synthNormMemo_334_);
v___x_341_ = v_reuseFailAlloc_347_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_341_);
v___x_343_ = v___x_321_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_cache_316_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_zetaDeltaFVarIds_317_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_postponed_318_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_diag_319_);
v___x_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_st_ref_put(v___y_312_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_338_);
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_310_ = stack[0].m_obj;
lean_object* v_val_311_ = stack[1].m_obj;
lean_object* v___y_312_ = stack[2].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_310_, v_val_311_, v___y_312_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(lean_object* v_mvarId_351_, lean_object* v_val_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_351_, v_val_352_, v___y_353_);
lean_dec(v___y_353_);
return v_res_355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5));
v___x_368_ = l_Lean_Name_append(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_unsigned_to_nat(16u);
v___x_386_ = lean_mk_array(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14);
v___x_395_ = 1;
v___x_396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_393_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*2, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(32u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21(void){
_start:
{
size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((size_t)5ULL);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_unsigned_to_nat(32u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20);
v___x_410_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_406_);
lean_ctor_set(v___x_410_, 3, v___x_406_);
lean_ctor_set_usize(v___x_410_, 4, v___x_405_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21);
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set(v___x_413_, 2, v___x_412_);
lean_ctor_set(v___x_413_, 3, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22);
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object* v_mvarId_429_, lean_object* v_h_430_, lean_object* v_lhs_431_, lean_object* v_rhs_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_a_439_; lean_object* v___y_457_; lean_object* v___y_468_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v_a_499_; lean_object* v___y_503_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11));
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
lean_inc_ref(v___x_507_);
v___x_508_ = lean_array_push(v___x_507_, v_lhs_431_);
v___x_509_ = l_Lean_Meta_mkAppM(v___x_505_, v___x_508_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
lean_inc_ref(v___x_507_);
v___x_511_ = lean_array_push(v___x_507_, v_rhs_432_);
v___x_512_ = l_Lean_Meta_mkAppM(v___x_505_, v___x_511_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
lean_inc(v_a_510_);
v___x_514_ = l_Lean_Meta_mkLT(v_a_510_, v_a_513_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_515_, v___x_516_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_436_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = 0;
v___x_523_ = 1;
v___x_527_ = lean_box(0);
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12));
lean_inc_ref(v___x_507_);
v___x_529_ = lean_array_push(v___x_507_, v_a_520_);
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
v___x_531_ = l_Lean_Options_empty;
v___x_532_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_528_, v___x_529_, v___x_530_, v___x_531_, v_a_433_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l_Lean_Expr_mvarId_x21(v_a_518_);
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18));
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23);
v___x_537_ = l_Lean_Meta_simpTarget(v___x_534_, v_a_533_, v___x_535_, v___x_527_, v___x_523_, v___x_536_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_586_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_586_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_586_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_586_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_fst_542_; 
v_fst_542_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_fst_542_);
lean_dec(v_a_538_);
if (lean_obj_tag(v_fst_542_) == 0)
{
lean_object* v___x_543_; 
lean_del_object(v___x_540_);
v___x_543_ = l_Lean_Meta_mkEqSymm(v_h_430_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = l_Lean_Expr_appFn_x21(v_a_510_);
v___x_546_ = l_Lean_Meta_mkCongrArg(v___x_545_, v_a_544_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26));
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_521_);
v___x_550_ = lean_array_push(v___x_549_, v_a_518_);
v___x_551_ = lean_array_push(v___x_550_, v_a_547_);
v___x_552_ = l_Lean_Meta_mkAppM(v___x_548_, v___x_551_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28));
v___x_555_ = lean_array_push(v___x_507_, v_a_510_);
v___x_556_ = l_Lean_Meta_mkAppM(v___x_554_, v___x_555_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
lean_inc(v_mvarId_429_);
v___x_558_ = l_Lean_MVarId_getType(v_mvarId_429_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = l_Lean_Expr_app___override(v_a_557_, v_a_553_);
v___x_561_ = l_Lean_Meta_mkFalseElim(v_a_559_, v___x_560_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v_toCold_564_; lean_object* v_options_565_; uint8_t v_hasTrace_566_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_429_, v_a_562_, v_a_434_);
lean_dec_ref(v___x_563_);
v_toCold_564_ = lean_ctor_get(v_a_435_, 0);
v_options_565_ = lean_ctor_get(v_toCold_564_, 2);
v_hasTrace_566_ = lean_ctor_get_uint8(v_options_565_, sizeof(void*)*1);
if (v_hasTrace_566_ == 0)
{
goto v___jp_524_;
}
else
{
lean_object* v_inheritedTraceOptions_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_inheritedTraceOptions_567_ = lean_ctor_get(v_toCold_564_, 11);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_567_, v_options_565_, v___x_569_);
if (v___x_570_ == 0)
{
goto v___jp_524_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30);
v___x_572_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_568_, v___x_571_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_523_, v_a_573_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
v___y_503_ = v___x_574_;
goto v___jp_502_;
}
else
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_572_, 1);
v_a_499_ = v_a_575_;
goto v___jp_498_;
}
}
}
}
else
{
lean_object* v_a_576_; 
lean_dec(v_mvarId_429_);
v_a_576_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_561_, 1);
v_a_499_ = v_a_576_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_577_; 
lean_dec(v_a_557_);
lean_dec(v_a_553_);
lean_dec(v_mvarId_429_);
v_a_577_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_558_, 1);
v_a_499_ = v_a_577_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_578_; 
lean_dec(v_a_553_);
lean_dec(v_mvarId_429_);
v_a_578_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_556_, 1);
v_a_499_ = v_a_578_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_579_; 
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec(v_mvarId_429_);
v_a_579_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_552_, 1);
v_a_499_ = v_a_579_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec(v_mvarId_429_);
v_a_580_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_546_, 1);
v_a_499_ = v_a_580_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_581_; 
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec(v_mvarId_429_);
v_a_581_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_543_, 1);
v_a_499_ = v_a_581_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_584_; 
lean_dec_ref_known(v_fst_542_, 1);
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v___x_582_ = lean_box(v___x_522_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_582_);
v___x_584_ = v___x_540_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_a_587_; 
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_587_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_537_, 1);
v_a_499_ = v_a_587_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_588_; 
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_588_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_532_, 1);
v_a_499_ = v_a_588_;
goto v___jp_498_;
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_box(0);
v___x_526_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_523_, v___x_525_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
v___y_503_ = v___x_526_;
goto v___jp_502_;
}
}
else
{
lean_object* v_a_589_; 
lean_dec(v_a_518_);
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_589_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_519_, 1);
v_a_499_ = v_a_589_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_590_; 
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_590_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_517_, 1);
v_a_499_ = v_a_590_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_591_; 
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_591_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_514_, 1);
v_a_499_ = v_a_591_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_592_; 
lean_dec(v_a_510_);
lean_dec_ref(v___x_507_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_592_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_512_, 1);
v_a_499_ = v_a_592_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_593_; 
lean_dec_ref(v___x_507_);
lean_dec_ref(v_rhs_432_);
lean_dec_ref(v_h_430_);
lean_dec(v_mvarId_429_);
v_a_593_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_509_, 1);
v_a_499_ = v_a_593_;
goto v___jp_498_;
}
v___jp_438_:
{
if (lean_obj_tag(v_a_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v_a_439_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v_a_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
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
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_a_439_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v_a_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
v___jp_456_:
{
if (lean_obj_tag(v___y_457_) == 0)
{
lean_object* v_a_458_; 
v_a_458_ = lean_ctor_get(v___y_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___y_457_, 1);
v_a_439_ = v_a_458_;
goto v___jp_438_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___y_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___y_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___y_457_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___y_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_box(0);
lean_inc(v_a_436_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc_ref(v_a_433_);
v___x_470_ = lean_apply_6(v___y_468_, v___x_469_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, lean_box(0));
v___y_457_ = v___x_470_;
goto v___jp_456_;
}
v___jp_471_:
{
if (v___y_473_ == 0)
{
lean_object* v_toCold_474_; lean_object* v_options_475_; lean_object* v_inheritedTraceOptions_476_; uint8_t v_hasTrace_477_; lean_object* v___x_478_; lean_object* v___f_479_; 
v_toCold_474_ = lean_ctor_get(v_a_435_, 0);
v_options_475_ = lean_ctor_get(v_toCold_474_, 2);
v_inheritedTraceOptions_476_ = lean_ctor_get(v_toCold_474_, 11);
v_hasTrace_477_ = lean_ctor_get_uint8(v_options_475_, sizeof(void*)*1);
v___x_478_ = lean_box(v___y_473_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_479_, 0, v___x_478_);
if (v_hasTrace_477_ == 0)
{
lean_dec_ref(v___y_472_);
v___y_468_ = v___f_479_;
goto v___jp_467_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_476_, v_options_475_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec_ref(v___y_472_);
v___y_468_ = v___f_479_;
goto v___jp_467_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref(v___f_479_);
v___x_483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8);
v___x_484_ = l_Lean_Exception_toMessageData(v___y_472_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_480_, v___x_485_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_473_, v_a_487_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
v___y_457_ = v___x_488_;
goto v___jp_456_;
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_486_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_486_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___y_472_);
return v___x_497_;
}
}
v___jp_498_:
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_Exception_isInterrupt(v_a_499_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
lean_inc_ref(v_a_499_);
v___x_501_ = l_Lean_Exception_isRuntime(v_a_499_);
v___y_472_ = v_a_499_;
v___y_473_ = v___x_501_;
goto v___jp_471_;
}
else
{
v___y_472_ = v_a_499_;
v___y_473_ = v___x_500_;
goto v___jp_471_;
}
}
v___jp_502_:
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v___y_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___y_503_);
v_a_439_ = v_a_504_;
goto v___jp_438_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_429_ = stack[0].m_obj;
lean_object* v_h_430_ = stack[1].m_obj;
lean_object* v_lhs_431_ = stack[2].m_obj;
lean_object* v_rhs_432_ = stack[3].m_obj;
lean_object* v_a_433_ = stack[4].m_obj;
lean_object* v_a_434_ = stack[5].m_obj;
lean_object* v_a_435_ = stack[6].m_obj;
lean_object* v_a_436_ = stack[7].m_obj;
lean_object* v_res_594_;
v_res_594_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_429_, v_h_430_, v_lhs_431_, v_rhs_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object* v_mvarId_595_, lean_object* v_h_596_, lean_object* v_lhs_597_, lean_object* v_rhs_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_595_, v_h_596_, v_lhs_597_, v_rhs_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_604_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object* v_mvarId_605_, lean_object* v_val_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_605_, v_val_606_, v___y_608_);
return v___x_612_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_605_ = stack[0].m_obj;
lean_object* v_val_606_ = stack[1].m_obj;
lean_object* v___y_607_ = stack[2].m_obj;
lean_object* v___y_608_ = stack[3].m_obj;
lean_object* v___y_609_ = stack[4].m_obj;
lean_object* v___y_610_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_605_, v_val_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object* v_mvarId_614_, lean_object* v_val_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_614_, v_val_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_x_623_, v_x_624_, v_x_625_);
return v___x_626_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, size_t v_x_629_, size_t v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_628_, v_x_629_, v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_628_ = stack[1].m_obj;
size_t v_x_629_ = stack[2].m_num;
size_t v_x_630_ = stack[3].m_num;
lean_object* v_x_631_ = stack[4].m_obj;
lean_object* v_x_632_ = stack[5].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(lean_box(0), v_x_628_, v_x_629_, v_x_630_, v_x_631_, v_x_632_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_10523__boxed_641_; size_t v_x_10524__boxed_642_; lean_object* v_res_643_; 
v_x_10523__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_x_10524__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(v_00_u03b2_635_, v_x_636_, v_x_10523__boxed_641_, v_x_10524__boxed_642_, v_x_639_, v_x_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_644_, lean_object* v_n_645_, lean_object* v_k_646_, lean_object* v_v_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v_n_645_, v_k_646_, v_v_647_);
return v___x_648_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_649_, size_t v_depth_650_, lean_object* v_keys_651_, lean_object* v_vals_652_, lean_object* v_heq_653_, lean_object* v_i_654_, lean_object* v_entries_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_650_, v_keys_651_, v_vals_652_, v_i_654_, v_entries_655_);
return v___x_656_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_650_ = stack[1].m_num;
lean_object* v_keys_651_ = stack[2].m_obj;
lean_object* v_vals_652_ = stack[3].m_obj;
lean_object* v_i_654_ = stack[5].m_obj;
lean_object* v_entries_655_ = stack[6].m_obj;
lean_object* v_res_657_;
v_res_657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(lean_box(0), v_depth_650_, v_keys_651_, v_vals_652_, lean_box(0), v_i_654_, v_entries_655_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_658_, lean_object* v_depth_659_, lean_object* v_keys_660_, lean_object* v_vals_661_, lean_object* v_heq_662_, lean_object* v_i_663_, lean_object* v_entries_664_){
_start:
{
size_t v_depth_boxed_665_; lean_object* v_res_666_; 
v_depth_boxed_665_ = lean_unbox_usize(v_depth_659_);
lean_dec(v_depth_659_);
v_res_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(v_00_u03b2_658_, v_depth_boxed_665_, v_keys_660_, v_vals_661_, v_heq_662_, v_i_663_, v_entries_664_);
lean_dec_ref(v_vals_661_);
lean_dec_ref(v_keys_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_x_668_, v_x_669_, v_x_670_, v_x_671_);
return v___x_672_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object* v_mvarId_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_673_ = stack[0].m_obj;
lean_object* v_x_674_ = stack[1].m_obj;
lean_object* v___y_675_ = stack[2].m_obj;
lean_object* v___y_676_ = stack[3].m_obj;
lean_object* v___y_677_ = stack[4].m_obj;
lean_object* v___y_678_ = stack[5].m_obj;
lean_object* v_res_697_;
v_res_697_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object* v_mvarId_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_698_, v_x_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_705_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object* v_00_u03b1_706_, lean_object* v_mvarId_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_707_, v_x_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_707_ = stack[1].m_obj;
lean_object* v_x_708_ = stack[2].m_obj;
lean_object* v___y_709_ = stack[3].m_obj;
lean_object* v___y_710_ = stack[4].m_obj;
lean_object* v___y_711_ = stack[5].m_obj;
lean_object* v___y_712_ = stack[6].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_box(0), v_mvarId_707_, v_x_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object* v_00_u03b1_716_, lean_object* v_mvarId_717_, lean_object* v_x_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(v_00_u03b1_716_, v_mvarId_717_, v_x_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__2));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* v_h_731_, lean_object* v_mvarId_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc_ref(v_h_731_);
v___x_738_ = lean_infer_type(v_h_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Meta_whnfD(v_a_739_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_797_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_797_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_797_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_797_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v_toCold_778_; lean_object* v_options_779_; uint8_t v_hasTrace_780_; 
v_toCold_778_ = lean_ctor_get(v___y_735_, 0);
v_options_779_ = lean_ctor_get(v_toCold_778_, 2);
v_hasTrace_780_ = lean_ctor_get_uint8(v_options_779_, sizeof(void*)*1);
if (v_hasTrace_780_ == 0)
{
v___y_746_ = v___y_733_;
v___y_747_ = v___y_734_;
v___y_748_ = v___y_735_;
v___y_749_ = v___y_736_;
goto v___jp_745_;
}
else
{
lean_object* v_inheritedTraceOptions_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_inheritedTraceOptions_781_ = lean_ctor_get(v_toCold_778_, 11);
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
v___x_784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_781_, v_options_779_, v___x_783_);
if (v___x_784_ == 0)
{
v___y_746_ = v___y_733_;
v___y_747_ = v___y_734_;
v___y_748_ = v___y_735_;
v___y_749_ = v___y_736_;
goto v___jp_745_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_obj_once(&l_Lean_MVarId_acyclic___lam__0___closed__3, &l_Lean_MVarId_acyclic___lam__0___closed__3_once, _init_l_Lean_MVarId_acyclic___lam__0___closed__3);
lean_inc(v_a_741_);
v___x_786_ = l_Lean_MessageData_ofExpr(v_a_741_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_782_, v___x_787_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_dec_ref_known(v___x_788_, 1);
v___y_746_ = v___y_733_;
v___y_747_ = v___y_734_;
v___y_748_ = v___y_735_;
v___y_749_ = v___y_736_;
goto v___jp_745_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_del_object(v___x_743_);
lean_dec(v_a_741_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
v___jp_745_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__1));
v___x_751_ = lean_unsigned_to_nat(3u);
v___x_752_ = l_Lean_Expr_isAppOfArity(v_a_741_, v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_a_741_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
v___x_753_ = lean_box(v___x_752_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_753_);
v___x_755_ = v___x_743_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_del_object(v___x_743_);
v___x_757_ = l_Lean_Expr_appFn_x21(v_a_741_);
v___x_758_ = l_Lean_Expr_appArg_x21(v___x_757_);
lean_dec_ref(v___x_757_);
v___x_759_ = l_Lean_Expr_appArg_x21(v_a_741_);
lean_dec(v_a_741_);
lean_inc_ref(v___x_759_);
lean_inc_ref(v___x_758_);
v___x_760_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_758_, v___x_759_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; uint8_t v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc_ref(v___x_758_);
lean_inc_ref(v___x_759_);
v___x_763_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_759_, v___x_758_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v___x_765_ = lean_unbox(v_a_764_);
if (v___x_765_ == 0)
{
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
return v___x_763_;
}
else
{
lean_object* v___x_766_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_766_ = l_Lean_Meta_mkEqSymm(v_h_731_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_732_, v_a_767_, v___x_759_, v___x_758_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v___x_768_;
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_mvarId_732_);
v_a_769_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_766_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
return v___x_763_;
}
}
else
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_732_, v_h_731_, v___x_758_, v___x_759_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v___x_777_;
}
}
else
{
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
v_a_798_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_740_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_740_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v_mvarId_732_);
lean_dec_ref(v_h_731_);
v_a_806_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_738_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_738_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_acyclic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_731_ = stack[0].m_obj;
lean_object* v_mvarId_732_ = stack[1].m_obj;
lean_object* v___y_733_ = stack[2].m_obj;
lean_object* v___y_734_ = stack[3].m_obj;
lean_object* v___y_735_ = stack[4].m_obj;
lean_object* v___y_736_ = stack[5].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Lean_MVarId_acyclic___lam__0(v_h_731_, v_mvarId_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object* v_h_815_, lean_object* v_mvarId_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_MVarId_acyclic___lam__0(v_h_815_, v_mvarId_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v_res_822_;
}
}
lean_object* l_Lean_MVarId_acyclic(lean_object* v_mvarId_823_, lean_object* v_h_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; 
lean_inc(v_mvarId_823_);
v___f_830_ = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0___boxed), 7, 2);
lean_closure_set(v___f_830_, 0, v_h_824_);
lean_closure_set(v___f_830_, 1, v_mvarId_823_);
v___x_831_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_823_, v___f_830_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_831_;
}
}
LEAN_EXPORT void l_Lean_MVarId_acyclic_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_823_ = stack[0].m_obj;
lean_object* v_h_824_ = stack[1].m_obj;
lean_object* v_a_825_ = stack[2].m_obj;
lean_object* v_a_826_ = stack[3].m_obj;
lean_object* v_a_827_ = stack[4].m_obj;
lean_object* v_a_828_ = stack[5].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_MVarId_acyclic(v_mvarId_823_, v_h_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* v_mvarId_833_, lean_object* v_h_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_MVarId_acyclic(v_mvarId_833_, v_h_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_905_ = 0;
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_));
v___x_907_ = l_Lean_registerTraceClass(v___x_904_, v___x_905_, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_908_;
v_res_908_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
return v_res_910_;
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
